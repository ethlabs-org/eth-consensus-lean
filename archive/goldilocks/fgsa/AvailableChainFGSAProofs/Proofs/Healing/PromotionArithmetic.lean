module
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW -- shake: keep (carrier time API)
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (healing lane strict-read supplier)
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.Channels
public import AvailableChainFGSARun.Proofs.Interface

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private def p0d3_arith_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d3_arith_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (p0d3_arith_timing p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

private def p0d3_arith_core (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }
private def p0d3_arith_safety (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGSafetyReads (fgsa p c) p.n (RowWire p.n) where
  proposalErase := safetyProposalErase p
  proposalRows := safetyProposalRows p
  encode := ofRow p
  decode := RowWire.toRow?
  decodeObject := decodeRowObject p
  fgLabel := .base .fg
  fgSeats := Equiv.refl _
  record := Node.record
  inputs := fun nd => fgInputs p nd.st
  enabled := fun t => decide (p.actionTime ((p.slotOf t - 1) / p.R) = t)
  finalizedOut := finalizedOut

omit [Fintype V] in
private theorem p0d3_arith_keep (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (i j : Nat) (x : V) (a : RowWire p.n)
    (hi : i ≤ j)
    (ha : FGCompose.rowHeld (p0d3_arith_core p c) (fun nd => FGSA.blockWireRows nd.st)
      (V2.D.Run.stateBefore E rho i x) a) :
    FGCompose.rowHeld (p0d3_arith_core p c) (fun nd => FGSA.blockWireRows nd.st)
      (V2.D.Run.stateBefore E rho j x) a := by
  obtain ⟨_, _, hprops, hpool⟩ := fgsa_store_durable p c E rho hi x
  change a ∈ (storeAt p c E rho (i) x).rowPool ∨
    a ∈ FGSA.blockWireRows (storeAt p c E rho (i) x) at ha
  change a ∈ (storeAt p c E rho (j) x).rowPool ∨
    a ∈ FGSA.blockWireRows (storeAt p c E rho (j) x)
  rcases ha with hp | hb
  · exact Or.inl (hpool.subset hp)
  · right
    change a ∈ FGSA.allBlockRows _ at hb ⊢
    unfold FGSA.allBlockRows at hb ⊢
    obtain ⟨rows, hr, ha⟩ := List.mem_flatten.mp hb
    obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp hr
    exact List.mem_flatten.mpr ⟨rows, List.mem_filterMap.mpr ⟨o, hprops.subset ho, he⟩, ha⟩

private theorem promotion_period_pos (p : Params) : 0 < P p := by
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  change 0 < 4 * (p.R : Time) * p.Δ
  have := p.deltaPos
  nlinarith

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: INTENTIONAL GUP r2 rounds the gap up by less than one proposal-grid interval. -/
theorem healing_promotion_gap_remainder (p : Params) (G : Time) :
    G ≤ Γ p G ∧ Γ p G < G + 4 * p.Δ := by
  exact FGCompose.healing_promotion_gap_remainder
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p) G

private theorem promotion_grid_upper (p : Params) (G z : Time) (s : Slot)
    (hs : SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + G) :
    SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + Γ p G := by
  linarith [(fgsa_gamma_bounds p G).1]

/-- A row held before one deadline remains held before each later deadline. -/
theorem healing_promotion_held_mono (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {d d' : Time} (hdd : d ≤ d') {x : V} {a : RowWire p.n}
    (ha : HeldBefore p c E rho x a d) : HeldBefore p c E rho x a d' := by
  exact FGCompose.healing_promotion_held_mono (p0d3_arith_core p c) E rho
    (fun nd => FGSA.blockWireRows nd.st) hrec.base.valid.toScheduleWellFormed
    (p0d3_arith_keep E rho) hdd ha

/-- Blueprint 21:1356–1370; plan §3.2 step 2.
DC: INTENTIONAL the full G window fits inside the supplied gate horizon.
The result retains the honest slot; it does not assert proposal emission. -/
theorem healing_promotion_gap (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon ∧
    ∃ s, (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.gateTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ := by
  apply FGCompose.healing_promotion_gap
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p) (fgsaInterface p c) E rho
    (r := r) (hgst := hgst) (hhor := hhor)
  intro t ht hh
  obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
  rw [proposalTime_fgsa] at hlo hhi
  exact ⟨s, hlo, hhi, hs⟩

/-- Blueprint 21:1371–1384; plan §3.2 step 3.
DC: SAME the earlier row's deadline is bounded without a later row selection. -/
theorem healing_promotion_row_deadline (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    {r rSent : Nat} (hr : rSent ≤ r) (hgst : E.t_GST ≤ p.actionTime r)
    {s : Slot} (hs : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s) :
    max (p.actionTime rSent) E.t_GST + ΔF ≤ p.actionTime r + ΔF ∧
    p.actionTime r + ΔF ≤ carrierTimeW p ΔF r ∧
    carrierTimeW p ΔF r ≤ ((r : Time) + 1) * P p ∧
    max (p.actionTime rSent) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    r * p.R + 2 ≤ s := by
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  exact FGCompose.healing_promotion_row_deadline
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p) E hF
    ⟨hbound.kappa_le_R⟩ hr hgst hs

/-- The H.9(b) trigger keeps the earlier strict deadline chain. -/
theorem healing_promotion_row_deadline_strict (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    {r rSent : Nat} (hr : rSent ≤ r) (hgst : E.t_GST ≤ p.actionTime r)
    {s : Slot} (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s) :
    max (p.actionTime rSent) E.t_GST + ΔF ≤ p.actionTime r + ΔF ∧
    p.actionTime r + ΔF ≤ carrierTimeW p ΔF r ∧
    carrierTimeW p ΔF r ≤ ((r : Time) + 1) * P p ∧
    ((r : Time) + 1) * P p < SA.proposalTime p.toParams s := by
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  exact FGCompose.healing_promotion_row_deadline_strict
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p) E hF
    ⟨hbound.kappa_le_R⟩ hr hgst hs

/-- Blueprint 21:1371–1384; plan §3.2 step 3.
DC: SAME strict receipt at max(send,GST)+ΔF, for the original signed row.
Assembly supplies rowsReceipt with RowService.fgsa_tRowsReceipt. -/
theorem healing_promotion_row_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n),
      HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest,
        HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    {r j rSent : Nat} {y : V} {a : RowWire p.n}
    (hr : rSent ≤ r) (ha : HonestRowAt p c E rho j y rSent a)
    (hgst : E.t_GST ≤ p.actionTime r) {s : Slot}
    (hs : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon) :
    max (p.actionTime rSent) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    max (p.actionTime r) E.t_GST + ΔF ≤ SA.proposalTime p.toParams s ∧
    r * p.R + 2 ≤ s ∧
    ∀ x ∈ rho.honest,
      HeldBefore p c E rho x a (max (p.actionTime rSent) E.t_GST + ΔF) ∧
      HeldBefore p c E rho x a (p.actionTime r + ΔF) := by
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  exact FGCompose.healing_promotion_row_receipt
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p)
    (p0d3_arith_core p c) (p0d3_arith_safety p c) E rho
    (fun nd => FGSA.blockWireRows nd.st) hrec.base.valid.toScheduleWellFormed
    (p0d3_arith_keep E rho) hF ⟨hbound.kappa_le_R⟩ rowsReceipt hr ha hgst hs hhor

/-- The H.9(b) trigger keeps the strict deadline and the original signed row. -/
theorem healing_promotion_row_receipt_strict (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n),
      HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest,
        HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    {r j rSent : Nat} {y : V} {a : RowWire p.n}
    (hr : rSent ≤ r) (ha : HonestRowAt p c E rho j y rSent a)
    (hgst : E.t_GST ≤ p.actionTime r) {s : Slot}
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon) :
    max (p.actionTime rSent) E.t_GST + ΔF < SA.proposalTime p.toParams s ∧
    ∀ x ∈ rho.honest,
      HeldBefore p c E rho x a (max (p.actionTime rSent) E.t_GST + ΔF) ∧
      HeldBefore p c E rho x a (p.actionTime r + ΔF) := by
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  exact FGCompose.healing_promotion_row_receipt_strict
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p)
    (p0d3_arith_core p c) (p0d3_arith_safety p c) E rho
    (fun nd => FGSA.blockWireRows nd.st) hrec.base.valid.toScheduleWellFormed
    (p0d3_arith_keep E rho) hF ⟨hbound.kappa_le_R⟩ rowsReceipt hr ha hgst hs hhor

/-- Blueprint 21:1385–1410; plan §3.2 steps 4–5.
DC: SAME two full periods give the maturity required by K-HEIGHT. -/
theorem healing_promotion_maturity (p : Params) (hδ : p.δt = 2 * p.R)
    {s : Nat} {U : FGBlock (Fin p.n)}
    (hs : SA.proposalTime p.toParams U.slot + 2 * P p ≤ SA.proposalTime p.toParams s) :
    U.slot + p.δt ≤ s := by
  exact FGCompose.healing_promotion_maturity
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p) hδ hs

/-- The entry-slot bound supplies the old action-based maturity case. -/
theorem healing_promotion_maturity_of_action (p : Params) (hδ : p.δt = 2 * p.R)
    {r s : Nat} {U : FGBlock (Fin p.n)} (hU : U.slot ≤ r * p.R)
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s) :
    U.slot + p.δt ≤ s := by
  exact FGCompose.healing_promotion_maturity_of_action
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p) hδ hU hs

/-- Blueprint 21:1592–1638; plan §3.2 step 7.
DC: INTENTIONAL the age-sensitive trigger is on the proposal grid.
This is the deadline component, not an acceptance or service producer. -/
theorem healing_promotion_age_gap (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (r : Nat) (q : Slot)
    (hgst : E.t_GST ≤ (r : Time) * P p)
    (hwin : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon) :
    let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ)
    U_F + G ≤ rho.horizon ∧
    ∃ s, U_F < SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.proposalTime p.toParams s + p.Δ ≤
        max (p.actionTime r + Γ p G - p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams q + 2 * P p + Γ p G - 3 * p.Δ) ∧
      SA.gateTime p.toParams s ≤
        max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
          (SA.proposalTime p.toParams q + 2 * P p + Γ p G + 2 * p.Δ) := by
  have hF : 0 ≤ ΔF := by
    have := hrec.deltaF
    rw [hrec.base.delta] at this
    linarith [p.deltaPos]
  apply FGCompose.healing_promotion_age_gap
    (p0d3_arith_timing p) (p0d3_arith_timing_laws p) (fgsaInterface p c) E rho
    (hF := hF) (r := r) (q := q) (hgst := hgst) (hwin := hwin)
  intro t ht hh
  obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t ht hh
  rw [proposalTime_fgsa] at hlo hhi
  exact ⟨s, hlo, hhi, hs⟩

end AvailableChain.FGSA.Run
end
