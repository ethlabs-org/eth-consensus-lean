module
public import AvailableChainFGCompose.Proofs.Healing.CommonEntry
public import AvailableChainFGSAProofs.Proofs.Healing.OpeningServiceBody
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

/-! H-COMMON arithmetic, raw-result compatibility, and entry laws (plan §3F.1–3).
The selected source is a fresh fast-write prefix of its actual raw result. Same-label
compatibility then applies to those results. Entry equality uses the height plateau. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def p0d3_common_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private def p0d3_common_core (p : Params) {In : Type} (c : AppCodec In) :
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
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.1. DC: SAME first-opening minimality bounds its label. -/
theorem common_first_opening_labels (q r : Nat)
    (hle : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r') :
    q ≤ r * p.R ∧ r * p.R < q + p.R := by
  refine ⟨hle, ?_⟩
  by_cases hz : r = 0
  · subst r; have := p.RLarge; omega
  · have hn : ¬ q ≤ (r - 1) * p.R := by
      intro h; have := hfirst (r - 1) h; omega
    have he : r * p.R = (r - 1) * p.R + p.R := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.1. DC: SAME the private OpeningSource time bound,
proved here from the label interval and positive Δ. -/
theorem common_first_time_bound (q r : Nat)
    (hle : q ≤ r * p.R) (hfirst : ∀ r', q ≤ r' * p.R → r ≤ r') :
    0 ≤ p.actionTime r - SA.gateTime p.toParams q ∧
      p.actionTime r - SA.gateTime p.toParams q ≤ P p - 4 * p.Δ := by
  obtain ⟨ha, hb⟩ := common_first_opening_labels (p := p) q r hle hfirst
  have haI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast ha
  have hbI : ((r * p.R : Nat) : Int) < (q : Int) + (p.R : Int) := by exact_mod_cast hb
  have hbI' : ((r * p.R : Nat) : Int) ≤ (q : Int) + (p.R : Int) - 1 := by omega
  change 0 ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ -
    (4 * p.Δ * (q : Int) + 6 * p.Δ) ∧
    4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ -
    (4 * p.Δ * (q : Int) + 6 * p.Δ) ≤ 4 * (p.R : Int) * p.Δ - 4 * p.Δ
  have := p.deltaPos
  constructor <;> nlinarith

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Read bridge. DC: SAME a selected action source has an actual opening tick.
See opening_action_tick in Healing/OpeningServiceOne for the postClock route. -/
theorem common_source_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho x r = some (some K)) :
    ∃ i : Nat, rho.events[i]? = some (.tick x (p.actionTime r)) := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hK; contradiction
  | some i => exact ⟨i, V2.D.Run.tickIdx?_spec hi⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.7, H.9; plan §3F.3. DC: SAME the selected source is stored at
its opening read, so the phase frontier caps its own height. -/
theorem common_source_height_le (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho)
    {u : Time} {m r : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    {x : V} {K : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho x r = some (some K)) :
    (heightView p K).h ≤ m := by
  obtain ⟨i, ht⟩ := common_source_tick E rho hK
  obtain ⟨_, hdom, _, _⟩ := opening_source_body E rho hs ht hK
  have hKT : K ∈ (storeAt p c E rho i x).fg.TF := by
    have h := ((KitFG.mem_filteredFromView _ _ _ _).mp hdom).1
    change K ∈ (FGSA.clock p (storeAt p c E rho i x) (p.actionTime r)).fg.TF at h
    rwa [clock_fg] at h
  have hui := healing_support_idxBefore_le p c E rho hs ht hphase.1
  have hiv := (healing_phase_lt_timeIdx p c E rho hs ht le_rfl).le
  have hH := (hphase.2.2.2 i x hui hiv hx).1
  exact hH ▸ healing_phase_height_le p c E rho hKT

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.2. DC: SAME each selected source is below its
actual raw result at rR, by its fresh fast-write membership. No INLINE sourceBodies
premise is needed: H-GATE's opening_fastWrite_spec gives this fact directly. -/
theorem common_source_below_raw (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {r : Nat} {K : FGBlock (Fin p.n)}
    (hK : actionSourceFG p c E rho x r = some (some K)) :
    ∃ B, gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG K) B := by
  classical
  obtain ⟨i, ht⟩ := common_source_tick E rho hK
  obtain ⟨_, _, _, hfw⟩ := opening_source_body E rho hs ht hK
  have hgate : IsGateTick p c rho i x (r * p.R) := ht
  obtain ⟨B, hraw, _, _, _, hKB, _⟩ := opening_fastWrite_spec E rho hs hgate hfw
  refine ⟨B, ?_, hKB⟩
  rw [gateResult_eq_saved p c E rho hs hgate]
  have hJoined := healing_fastWrite_joined E rho hs hgate hfw
  have hSaved := fgsa_gate_saved_result E rho hs hgate hJoined
  exact hSaved.trans (congrArg some hraw)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.2. DC: INTENTIONAL compatible raw results at the
synchronized opening label imply compatibility of their selected prefixes. -/
theorem common_sources_compatible [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {q r : Nat}
    (hScope : SameLabelServiceScope E rho (r * p.R))
    (hready : recoveryStart p E ≤ u) (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    ∀ x y K K', x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG p c E rho x r = some (some K) →
      actionSourceFG p c E rho y r = some (some K') →
      Block.Compatible (eraseFG K) (eraseFG K') := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hS := hrec.base.valid.toScheduleWellFormed
  have hqI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
  have hd := p.deltaPos
  have hvgst : E.t_GST ≤ SA.voteTime p.toParams (r * p.R) := by
    refine hGST.trans (hu.trans ?_)
    change 4 * p.Δ * (q : Int) ≤ 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ
    nlinarith
  have hvd : SA.voteTime p.toParams (r * p.R) + E.Δ ≤ SA.gateTime p.toParams (r * p.R) := by
    rw [hrec.base.delta]
    change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ + p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    linarith
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hvgst hvd hphase.2.1
  intro x y K K' hx hy hK hK'
  obtain ⟨B, hB, hKB⟩ := common_source_below_raw E rho hS hK
  obtain ⟨C, hC, hKC⟩ := common_source_below_raw E rho hS hK'
  have hBC := fgsa_sameLabel_on p c E rho hrec.base.valid
    (r * p.R) hScope hrec.base.idealization x y B C hx hy hB hC
  have hCB : Block.Compatible C B := by
    change Block.compatible C B = true
    rw [block_compatible_comm]
    exact hBC
  have hK'B := block_compatible_of_preceq_compatible hKC hCB
  have hBK' : Block.Compatible B (eraseFG K') := by
    change Block.compatible B (eraseFG K') = true
    rw [block_compatible_comm]
    exact hK'B
  exact block_compatible_of_preceq_compatible hKB hBK'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3. DC: SAME sources above a pivot at equal height
have the same T_h.root by entry_plateau. Empty universal source sets are allowed. -/
theorem common_entry_of_plateau (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (r m : Nat) (Qfg : FGBlock (Fin p.n)) (hh : (heightView p Qfg).h = m)
    (hsources : ∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (heightView p K).h ≤ m) :
    OpeningEntry p c E rho r m := by
  exact FGCompose.common_entry_of_plateau (p0d3_common_core p c) E rho
    (heightView p) (p0d3_common_timing p) p.E (fgCertificateLaws p).height
    r m Qfg hh hsources

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3. DC: INTENTIONAL at a low pivot, either all
sources are low with one entry, or an actual honest source has height m. -/
theorem common_low_or_high (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (r m : Nat) (Qfg : FGBlock (Fin p.n)) (hh : (heightView p Qfg).h = m - 1)
    (hsources : ∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (heightView p K).h ≤ m) :
    OpeningEntry p c E rho r (m - 1) ∨
      ∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
        (heightView p K).h = m := by
  exact FGCompose.common_low_or_high (p0d3_common_core p c) E rho
    (heightView p) (p0d3_common_timing p) p.E (fgCertificateLaws p).height
    r m Qfg hh hsources

end AvailableChain.FGSA.Run
end
