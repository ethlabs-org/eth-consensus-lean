module
public import AvailableChainFGSAProofs.Proofs.Healing.PostReset
public import AvailableChainFGSAProofs.Proofs.Healing.Time

public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchFull
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJointStep2
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCone
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRawStep
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetHealed
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetTHigh
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetH2Prime
public import AvailableChainFGSAProofs.Proofs.Healing.Reset

public section

/-! Blueprint 21 H.18 and H.22; plan S5 J10 E1/E2; B1/B13/B17/B31.
DC: SAME frozen fields and full reset horizon. Each input supplies its
exact field type under the guards of HealingInputOfH0Statement.
The J9 and J11 statements are used without changes. -/

namespace AvailableChain.FGSA.Run

/-- Project full H0 to PostResetStart. All fields come from H0.
This is the converse of PostResetStart.toH0 with its source prefix. -/
theorem healing_postResetStart_of_h0 (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {w : HealingWitness} (h0 : H0 p c E rho w) : PostResetStart p c E rho w :=
  { toH0Reset := h0.toH0Reset
    proposal_lower := h0.proposal_lower
    proposal := h0.proposal
    proposal_first := h0.proposal_first
    after_gst := h0.after_gst }

section
variable (p : Params) (G ΔF : Time)

variable (healed : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → Healed p c E rho (tstar p w))

variable (sourcePrefix : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → Block.Preceq w.CStar w.QStar)

variable (tHigh : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → THigh p c E rho w)

variable (tCarrier : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → TCarrier p c E rho w)

variable (rows : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      TRows p c E rho ΔF)

variable (h2A : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H2A p c E rho w)

variable (h2Prime : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H2Prime p c E rho w)

variable (h3 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H3 p c E rho w)

variable (h4 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H4 p c E rho w)

variable (h5 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H5RawTransfer p c E rho w)

variable (h6 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H6GateService p c E rho w)

variable (timeBound : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ)

include healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound

/-- S5 J10 E1: build J11's H.18 interface from J9 C/D.
Each remaining named input has the following planned producer job:
- `healed`: J7 H.18.
- `sourcePrefix`: J7 H.18.
- `tHigh`: J3 rest.
- `tCarrier`: J3 rest.
- `rows`: Foundations RowService.
- `h2A`: J3 rest.
- `h2Prime`: J3 rest.
- `h3`: J6-2 S1 rerun / lf-j6; healing_postReset_exactService from complete-cut PostResetService.
- `h4`: J7 H.18.
- `h5`: J5-A.
- `h6`: J6-2 / lf-j6; healing_postReset_h6GateService.
- `timeBound`: J7 H.18.
Keep h3 and h6 named for a later mechanical swap to the listed lf-j6 producers.
The Healed field supplies no upper time bound, so timeBound remains named. -/
theorem healing_healingInputOfH0 : HealingInputOfH0Statement p G ΔF := by
  rw [HealingInputOfH0Statement_def]
  intro hClock V _ _ In c E rho hSet hLive hHorizon w h0
  have start := healing_postResetStart_of_h0 p c E rho h0
  have t := healing_healT_of p c E rho
    (tHigh hClock c E rho hSet hLive hHorizon w h0)
    (tCarrier hClock c E rho hSet hLive hHorizon w h0)
    (rows hClock c E rho hSet hLive hHorizon)
  have ac := healing_healAC_of p c E rho
    (h2A hClock c E rho hSet hLive hHorizon w h0)
    (h2Prime hClock c E rho hSet hLive hHorizon w h0)
    (h3 hClock c E rho hSet hLive hHorizon w h0)
    (h4 hClock c E rho hSet hLive hHorizon w h0)
    (h5 hClock c E rho hSet hLive hHorizon w h0)
    (h6 hClock c E rho hSet hLive hHorizon w h0)
  exact ⟨healing_healingInput_of p c E rho
    (healed hClock c E rho hSet hLive hHorizon w h0) start
    (sourcePrefix hClock c E rho hSet hLive hHorizon w h0) t ac,
    timeBound hClock c E rho hSet hLive hHorizon w h0⟩

/-- S5 J10 E2: compose E1 with J11 healing_hTime_of.
The planned producer jobs for the same named inputs are:
- `healed`: J7 H.18.
- `sourcePrefix`: J7 H.18.
- `tHigh`: J3 rest.
- `tCarrier`: J3 rest.
- `rows`: Foundations RowService.
- `h2A`: J3 rest.
- `h2Prime`: J3 rest.
- `h3`: J6-2 S1 rerun / lf-j6; healing_postReset_exactService from complete-cut PostResetService.
- `h4`: J7 H.18.
- `h5`: J5-A.
- `h6`: J6-2 / lf-j6; healing_postReset_h6GateService.
- `timeBound`: J7 H.18.
The additional named input `hReset` is ResetArrivalFullStatement: J8 H-RESET (H.11, HG.5).
Keep h3 and h6 named for the later lf-j6 producer swap. -/
theorem healing_hTime_of_inputs (hReset : ResetArrivalFullStatement p G ΔF) :
    HTimeStatement p G ΔF :=
  healing_hTime_of p G ΔF hReset
    (healing_healingInputOfH0 p G ΔF
      healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound)

end
open AvailableChain.SimplexFG
variable (p : Params)

/-- An actual emitted proposal is served at its finite one-delta deadline. -/
theorem healing_proposal_receipt_recovery {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {ip : Nat} {v x : V} {s : Slot}
    {N : NamedProposal p.n} (hv : v ∈ rho.honest) (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick v (SA.proposalTime p.toParams s)))
    (hem : ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E ip)
    (hSync : E.t_GST ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon)
    (hCompat : Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
      (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F)) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
      (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x) := by
  let dl := fun t => max t E.t_GST + p.Δ
  have he : dl (SA.proposalTime p.toParams s) = SA.proposalTime p.toParams s + p.Δ := by
    dsimp only [dl]
    rw [max_eq_left hSync]
  have hD := Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hrec.sync
    (fun o => ¬ isRowObject o) p.Δ (fun o hn => by
      rw [fgsaDelay_nonrow E.Δ ΔF o hn, hrec.base.delta])
  apply fgsa_proposal_service_of_emission hrec.base.valid hrec.base.delta dl rho.horizon
    hv hip hem hD
  · rw [he]
    exact lt_add_of_pos_right _ p.deltaPos
  · exact he ▸ hhor
  · exact he ▸ hhor
  · exact he.le
  · intro t hat htd
    exact hrec.awake x hx t (hSync.trans hat) (htd.le.trans (he ▸ hhor))
  · exact healing_recovery_restartFree hrec hx hSync hhor
  · rw [he]
    exact hCompat

/-- Every suffix reader has passed its own enabled gate and all prior wakes. -/
theorem healing_postReset_confirmed_reader {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {w : HealingWitness} (h0 : H0 p c E rho w)
    (hhor : tstar p w ≤ rho.horizon) {i : Nat} (hi : HealSuffix p c rho (tstar p w) i)
    {x : V} (hx : x ∈ rho.honest) : confirmedReaderIdx p c E rho x i := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hgate : tstar p w = SA.gateTime p.toParams w.u := rfl
  have hstart : afterTicksIdx rho (tstar p w) ≤ i := by
    have hh := hi.1
    unfold healStart at hh
    have hg : isGateTime p (tstar p w) = true :=
      (isGateTime_iff p _).mpr ⟨w.u, rfl⟩
    rw [hg, ite_eq_left rfl] at hh
    exact hh
  have hCut := healing_reset_gate_cutoff h0.toH0Reset
    (Nat.le_add_right w.sStar 2 |>.trans h0.proposal_lower)
  have htime : ((4 * w.u + 6 : Nat) : Time) * p.Δ = tstar p w := by
    rw [hgate]
    change ((4 * w.u + 6 : Nat) : Time) * p.Δ = 4 * p.Δ * (w.u : Int) + 6 * p.Δ
    push_cast
    ring
  have hGST : E.t_GST < tstar p w := by
    change E.t_GST ≤ 4 * p.Δ * (w.u : Int) at hCut
    rw [hgate]
    change E.t_GST < 4 * p.Δ * (w.u : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨j, hj, _⟩ := fgsa_tick_total E rho hs hrec.base.delta x hx (4 * w.u + 6)
    (htime ▸ hhor) (htime ▸ hrec.awake x hx _ hGST.le hhor)
  rw [htime, hgate] at hj
  have hji := healing_postReset_tick_lt_cut E rho hs hj (hgate ▸ hstart)
  have hl : i - 1 < rho.events.length := by have := hi.2; omega
  have he : (rho.events.take i).getLast? = some rho.events[i - 1] := by
    rw [List.getLast?_eq_getElem?]
    simp only [List.length_take, min_eq_left hi.2]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hl]
  have hp : prefixTime rho i = rho.events[i - 1].time := by
    change ((rho.events.take i).getLast?.map (fun e => e.time)).getD 0 = _
    rw [he]
    rfl
  have hpH : prefixTime rho i ≤ rho.horizon := by
    rw [hp]
    exact (hs.in_horizon _ (List.getElem_mem hl)).2
  have hgp : SA.gateTime p.toParams w.u ≤ prefixTime rho i := by
    rw [hp]
    rcases (show j ≤ i - 1 by omega).lt_or_eq with hlt | rfl
    · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      have hsort := List.pairwise_iff_getElem.mp hs.sorted j (i - 1) hjl hl hlt
      rw [hje] at hsort
      exact V2.D.Engine.time_le_of_key_le _ _ hsort
    · have hh := Option.some.inj ((List.getElem?_eq_getElem hl).symm.trans hj)
      rw [hh]
      exact le_rfl
  have hb (k : Nat) : ∀ t, (storeAt p c E rho k x).restartTime = some t →
      t ≤ slotStartZ p (w.u : Int) := by
    apply fgsa_restartTime_bound E rho k x _
    intro q t _ hq
    exact (healing_recovery_restart_bound E rho hrec hx hq).trans hCut
  have enabled : enabledGateAt p c E rho j x w.u := by
    refine ⟨hj, ?_⟩
    cases hr : (storeAt p c E rho j x).restartTime with
    | none => trivial
    | some t => exact hb j t hr
  have hcp : E.t_GST ≤ prefixTime rho i := hGST.le.trans (hgate ▸ hgp)
  refine ⟨⟨hx, hrec.awake x hx _ hcp hpH, ?_⟩, ?_⟩
  · cases hr : (storeAt p c E rho i x).restartTime with
    | none => trivial
    | some t =>
      refine ⟨w.u, j, hb i t hr, hgp, hji, enabled, ?_, ?_⟩
      · intro v _ hcv hvp
        exact hrec.awake x hx v (hCut.trans hcv) (hvp.trans hpH)
      · intro v hcv hvp hm
        obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hm
        exact hrec.suffixNoRestart x hx q v hq (hCut.trans_lt hcv)
          (by dsimp [Time] at *; omega)
  · intro t ht0 htp hw
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp
      (hrec.base.valid.wake_restart x hx t ht0 (htp.trans hpH) hw)
    refine ⟨q, ?_, hq⟩
    have ht := healing_recovery_restart_bound E rho hrec hx hq
    have hqj := healing_idx_lt_of_time_lt p c E rho hs hq hj (ht.trans_lt (hgate ▸ hGST))
    exact hqj.trans hji

section RecoveryProducers
variable {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (cap : RCap p c E rho) (source : TSrc p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (finalityCap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include hrec mono emittedNonempty emittedName writes xing origin cap source
    heldRows finalityCap hhead rowCovered

/-- Recovery constructs all six guarded steps of the joint induction. -/
theorem healing_postReset_joint_recovery {w : HealingWitness}
    (hreset : H0Reset p c E rho w) :
    ∀ i, PostResetInv p c E rho w i ∧ PostResetResetLeaseCompatible p c E rho w i ∧
      PostResetOpeningDomain p c E rho w i ∧ PostResetRetainedConeP p c E rho w i := by
  exact postReset_joint₂_all p c E rho hrec mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead hreset
    (postReset_resetLease_succ' p c E rho hrec emittedNonempty emittedName mono xing
      hreset cap source)
    (postReset_leaseSafe_succ p c E rho hrec mono source emittedNonempty emittedName writes
      xing origin hreset)
    (postReset_rawTransfer_succ p c E rho hrec emittedNonempty emittedName writes mono source
      xing origin hreset)
    (healing_postReset_coneStep p c E rho hrec mono emittedNonempty emittedName writes
      xing origin hreset cap source rowCovered)
    (healing_postReset_openingDomainStep₂ E rho hrec w hreset cap rowCovered mono xing origin)
    (healing_postReset_serviceStep₂ E rho hrec w hreset cap rowCovered mono writes)

/-- The all-cut invariant has no assumed successor step. -/
theorem healing_postReset_inv_recovery {w : HealingWitness}
    (hreset : H0Reset p c E rho w) : ∀ i, PostResetInv p c E rho w i :=
  fun i => (healing_postReset_joint_recovery p c E rho hrec mono emittedNonempty emittedName
    writes xing origin cap source heldRows finalityCap hhead rowCovered hreset i).1

/-- Extend the selected reset witness. Only its proposal slot and block change. -/
theorem healing_h0_extension_recovery (_hδ : p.δt = 2 * p.R) :
    ∀ w, H0Reset p c E rho w →
      p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∃ u Q, H0 p c E rho {w with u := u, QStar := Q} := by
  intro w hreset hhor
  have inv := healing_postReset_inv_recovery p c E rho hrec mono emittedNonempty emittedName
    writes xing origin cap source heldRows finalityCap hhead rowCovered hreset
  have carrier := postReset_tCarrier_reset p c E rho hrec.toRecovery₂ cap source rowCovered
    hreset inv
  obtain ⟨u, Q, h0, _⟩ := healing_h0_of p c E rho hrec carrier hreset hhor
  exact ⟨u, Q, h0⟩

/-- The local input uses the selected witness's own finite horizon. -/
theorem healing_localInput_recovery (rows : TRows p c E rho ΔF)
    (_hδ : p.δt = 2 * p.R) :
    ∀ w, H0 p c E rho w → tstar p w ≤ rho.horizon → HealingInput p c E rho w ΔF := by
  intro w h0 hhor
  have inv := healing_postReset_inv_recovery p c E rho hrec mono emittedNonempty emittedName
    writes xing origin cap source heldRows finalityCap hhead rowCovered h0.toH0Reset
  have start := healing_postResetStart_of_h0 p c E rho h0
  have carrier := postReset_tCarrier_reset p c E rho hrec.toRecovery₂ cap source rowCovered
    h0.toH0Reset inv
  have h2A := postReset_h2A_reset p c E rho hrec.toRecovery₂ cap source rowCovered
    h0.toH0Reset inv
  have h3 := healing_postReset_exactService E rho w rho.events.length le_rfl
    (inv rho.events.length).service
  have h5 := postReset_h5RawTransfer_body p c E rho h0.toH0Reset
    (fun i => (inv i).raw_transfer)
  have h4 := healing_h4 p c E rho hrec start h2A h3 h5 inv hhor
    (fun _ _ hi hx => healing_postReset_confirmed_reader p c E rho hrec h0 hhor hi hx)
  have high := postReset_tHigh_reset p c E rho hrec mono emittedNonempty emittedName writes
    xing origin h0.toH0Reset cap source rowCovered inv
  have h2Prime := postReset_h2Prime_reset p c E rho hrec mono cap source rowCovered
    h0.toH0Reset xing origin inv
  have h6 := healing_postReset_h6GateService E rho hrec mono w rho.events.length le_rfl
    (inv rho.events.length).raw_transfer writes
  exact healing_healingInput_of p c E rho (healing_healed p c E rho hrec start h4 h3) start
    h0.source_prefix (healing_healT_of p c E rho high carrier rows)
    (healing_healAC_of p c E rho h2A h2Prime h3 h4 h5 h6)

omit hrec in
/-- Full input retains the complete Jst horizon and the same selected reset witness. -/
theorem healing_fullInput_recovery (hset : HealingSet p c E rho G ΔF)
    (hbound : LivenessBoundW p ΔF) (rows : TRows p c E rho ΔF)
    (emittedPairs : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n}
      {e : Height × BlockId}, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho)) :
    p.δt = 2 * p.R →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w →
        HealingInput p c E rho w ΔF ∧
          tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  intro hδ hfull w h0
  have search := healing_frontierSearch_recovery E rho hset mono xing cap origin writes
    (rowCovered hset.base hset.fault) rows.receipt progressCoverage hfold faultQ honestQuorum
  have hg : 0 ≤ Γ p G := by
    have hgap := hset.gapPos
    have hround := (fgsa_gamma_bounds p G).1
    linarith [p.deltaPos]
  obtain ⟨w', hreset', htime⟩ := healing_resetWitness p c E rho emittedPairs hset hδ hbound
    search (by linarith [p.deltaPos])
  have hr := healing_reset_rStar_unique p c E rho h0.toH0Reset hreset'
  have hhor : p.actionTime w.rStar + Γ p G + 4 * p.Δ ≤ rho.horizon := by
    rw [hr]
    linarith
  have ht := healing_tstar_le_of_h0 p c E rho hset h0 hhor
  exact ⟨healing_localInput_recovery p c E rho hset mono emittedNonempty emittedName writes
    xing origin cap source heldRows finalityCap hhead rowCovered rows hδ w h0
    (ht.trans hhor), ht⟩

end RecoveryProducers

end AvailableChain.FGSA.Run
end
