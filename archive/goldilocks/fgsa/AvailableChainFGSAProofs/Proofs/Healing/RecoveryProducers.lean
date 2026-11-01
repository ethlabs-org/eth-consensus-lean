module
public import AvailableChainFGSAProofs.Proofs.Healing.RelayProducers
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierRead
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRaw

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Recovery supplies the exact read epoch, including all restarts at GST. -/
theorem healing_recovery_epoch_after_vote {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest)
    {s : Slot} (hSync : E.t_GST ≤ SA.voteTime p.toParams s)
    {a : Time} (ha : SA.voteTime p.toParams s < a) (i : Nat) :
    V2.D.restartFree rho x (V2.D.Run.idxBefore rho a) i := by
  apply healing_recovery_epoch E rho hrec hx (fgsa_idxBefore_mono rho ?_)
  dsimp [Time] at *
  omega

/-- Recovery serves the jointly selected HEAD carrier and its actual direct target. -/
theorem healing_carriers_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (s : Slot) (iy : Nat) (y : V) (t : Time) :
    HealingCarriersAt E rho s iy y t := by
  intro hSync hRead hDeadline hhor j z hz hj hJoin
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = ((4 * s + 1 : Nat) : Int) * p.Δ
    push_cast
    ring
  have service (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho j z).fg.TF)
      (hCompat : Block.Compatible (eraseFG W)
        (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams s + p.Δ) y).st.fg.F)) :
      TargetReceiptService E rho (eraseFG W) (SA.voteTime p.toParams s + p.Δ) y :=
    healing_target_service_of_tick E rho hrec hz hRead.1 hj
      (((storeBundle_stateBefore E rho j z).cstore.baseTree _).mpr ⟨W, hW, rfl⟩)
      hpub hSync (hDeadline.trans hhor) hCompat
  constructor
  · intro demand
    obtain ⟨K, hK, he, W, hW, hKW, hlo, hCompat⟩ := demand.witness
    have hW0 : W ∈ (storeAt p c E rho j z).fg.TF := by
      change W ∈ (clock p (storeAt p c E rho j z) _).fg.TF at hW
      rwa [clock_fg] at hW
    exact ⟨⟨K, hK, he, W, hW, hKW, hlo, hCompat, service W hW0 hCompat⟩⟩
  · intro K hK he hFloor
    exact service K hK (Bool.or_eq_true_iff.mpr (Or.inr hFloor))

/-- The first transfer's selected target keeps its strict early source stamp. -/
theorem healing_first_target_receipt_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {ix iy : Nat} {x y : V} {K : Block}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hK : K ∈ (storeAt p c E rho ix x).base.blocks)
    (hStamp : GridCO.stampBlock (storeAt p c E rho ix x).base K < SA.earlyTime p.toParams s)
    (hFloor : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) K) :
    TargetReceiptService E rho K (SA.freezeTime p.toParams s) y := by
  have he : SA.earlyTime p.toParams s + p.Δ = SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hfr : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hFE := healing_receipt_floor_before_tick E rho hrec.base.valid.toScheduleWellFormed
    mono hy hiy hfr hFloor
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = _
    push_cast
    ring
  rw [← he] at hFE ⊢
  apply healing_target_service_of_stored E rho hrec hx hy hK hStamp hpub
  · apply le_trans hSync
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · exact he ▸ hfr.trans (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hiy)).2
  · exact Bool.or_eq_true_iff.mpr (Or.inr hFE)

/-- The first transfer's guards and epoch are produced from recovery.
The four object-service inputs are the remaining OPEN/P-H1 obligations. -/
theorem healing_first_transfer_scope_of_services {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    {s : Slot} {ix iy : Nat} {x y : V}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hxGate : enabledGateAt p c E rho ix x s)
    (hyJoin : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (forward : ∀ q b,
      (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        GridCO.cleanSupport p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x)
            (SA.gateTime p.toParams s))) s →
      HeadRelayLocalServiceScope E rho s q b (SA.freezeTime p.toParams s) iy y)
    (backward : ∀ q b,
      ((⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
          GridCO.votesAt (storeAt p c E rho iy y).base s ∨
        (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
          headVotes p (clock p (storeAt p c E rho iy y)
            (SA.voteTime p.toParams (s + 1))) (s + 1)) →
      HeadRelayLocalServiceScope E rho s q b (SA.gateTime p.toParams s) ix x)
    (targets : ∀ K, K ∈ (storeAt p c E rho ix x).base.blocks →
      GridCO.stampBlock (storeAt p c E rho ix x).base K <
        SA.earlyTime p.toParams s →
      Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) K →
      TargetReceiptService E rho K (SA.freezeTime p.toParams s) y)
    (carriers : HealingCarriersAt E rho s iy y
      (SA.voteTime p.toParams (s + 1))) : FirstTransferScope E rho ix iy x y s := by
  have hj := fgsa_head_joined_of_joinedAt E rho
    hrec.base.valid.toScheduleWellFormed hiy hyJoin
  change joinedNow p (clock p (storeAt p c E rho iy y)
    (SA.voteTime p.toParams (s + 1))) = true at hj
  have he : SA.releaseTime p.toParams s = SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 5 * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    ring
  refine ⟨hxGate, ?_, ?_, forward, backward, targets, carriers⟩
  · rw [he]
    simpa only [joinedNow, fgsa_clock_restartTime, (clock_vn _ _).2] using hj
  · apply healing_recovery_epoch_after_vote E rho hrec hy hSync _ iy
    change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]

/-- The later transfer's counts and epoch are produced from recovery.
Fresh HEAD, relay and selected carrier services remain OPEN/P-H1. -/
theorem healing_next_transfer_scope_of_services {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {iy : Nat} {y : V}
    (hCut : HealingWindow p E 1 s) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (fresh : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K⟩) (SA.voteTime p.toParams s) →
      Nonempty (FreshHeadService E rho s q K (SA.freezeTime p.toParams s) y))
    (reads : ∀ q b,
      (⟨.seat s q, .head b⟩ : GridCO.Wire p.n .root) ∈
        headVotes p (clock p (storeAt p c E rho iy y)
          (SA.voteTime p.toParams (s + 1))) (s + 1) →
      HeadRelayLocalServiceScope E rho s q b (SA.voteTime p.toParams (s + 1)) iy y)
    (carriers : HealingCarriersAt E rho s iy y
      (SA.voteTime p.toParams (s + 1))) : NextTransferScope E rho iy y s := by
  have hhor := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hh : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ hhor
    change 4 * p.Δ * (s : Int) + p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  let instOld : Fintype V := inferInstance
  obtain ⟨hrelease, _⟩ := healing_recovery_seat_counts E rho hrec hCut hh
  refine ⟨hrelease, ?_, ?_, ?_, fresh, reads, carriers⟩
  · intro inst
    have he : inst = instOld := Subsingleton.elim _ _
    cases he
    exact healing_recovery_seat_counts E rho hrec hCut hh |>.2
  · intro inst
    have he : inst = instOld := Subsingleton.elim _ _
    cases he
    exact healing_recovery_seat_rivals E rho hrec hCut hh _
  · apply healing_recovery_epoch_after_vote E rho hrec hy hCut.sync _ iy
    exact lt_add_of_pos_right _ p.deltaPos

/-- P1 has a recovery producer for stored and carried HEADs, including cap witnesses. -/
theorem healing_first_transfer_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {ix iy : Nat} {x y : V}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hy : y ∈ rho.honest) (_hix : IsGateTick p c rho ix x s)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hG : enabledGateAt p c E rho ix x s)
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1))) :
    FirstTransferScope E rho ix iy x y s := by
  apply healing_first_transfer_scope_of_services E rho hrec hSync hy hiy hG hJ
  · exact healing_head_forward_receipt E rho hrec hSync hx hy hG hiy hJ
  · exact healing_head_backward_receipt E rho hrec hSync hx hy hG hiy hJ
  · intro K hK hStamp hFloor
    exact healing_first_target_receipt_recovery E rho hrec mono hSync hx hy hiy
      hK hStamp hFloor
  · exact healing_carriers_recovery E rho hrec s iy y _

/-- P2 uses local stamped read evidence, with no invented late-object delivery window. -/
theorem healing_next_transfer_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {iy : Nat} {y : V}
    (hCut : HealingWindow p E 1 s) (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1))) :
    NextTransferScope E rho iy y s := by
  have hh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hiy)).2
  apply healing_next_transfer_scope_of_services E rho hrec hCut hy hiy
  · intro q K hq hem
    apply healing_fresh_head_service E rho hrec hy hq hem hCut.sync
    · change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
      linarith [p.deltaPos]
    · apply le_trans _ hh
      change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤
        4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith [p.deltaPos]
  · exact healing_head_local_service_recovery E rho hrec hCut.sync hy hiy hJ
  · exact healing_carriers_recovery E rho hrec s iy y _

/-- Proposal and late-gate support share the same proved seat counts and epoch.
The actual tick remains the read; no proposal event is invented at a gate. -/
theorem healing_proposal_support_scope_of_services {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {r : Slot} {ip : Nat} {x : V} {t : Time}
    (hCut : HealingWindow p E 1 r) (hRead : HealingJoinedTick E rho ip x t)
    (hTime : t = SA.proposalTime p.toParams (r + 1) ∨ t = SA.gateTime p.toParams r)
    (fresh : ∀ q K, rho.seatOf (.base (.head r)) q ∈ rho.honest →
      V2.D.Run.emits E rho (rho.seatOf (.base (.head r)) q)
        (ofHead p ⟨.seat (.head r) q, K⟩) (SA.voteTime p.toParams r) →
      Nonempty (FreshHeadService E rho r q K (SA.earlyTime p.toParams r) x))
    (carriers : HealingCarriersAt E rho r ip x t) :
    ProposalSupportScope E rho ip x r t := by
  have hhor := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hRead.2.1)).2
  have hh : SA.voteTime p.toParams r ≤ rho.horizon := by
    apply le_trans _ hhor
    rcases hTime with rfl | rfl
    · change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      linarith [p.deltaPos]
    · change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ
      linarith [p.deltaPos]
  let instOld : Fintype V := inferInstance
  refine ⟨?_, ?_, ?_, ?_, fresh, carriers⟩
  · intro inst
    have he : inst = instOld := Subsingleton.elim _ _
    cases he
    exact healing_recovery_seat_counts E rho hrec hCut hh |>.2
  · intro inst
    have he : inst = instOld := Subsingleton.elim _ _
    cases he
    exact healing_recovery_seat_rivals E rho hrec hCut hh _
  · intro inst
    have he : inst = instOld := Subsingleton.elim _ _
    cases he
    exact healing_recovery_seat_rivals E rho hrec hCut hh _
  · apply healing_recovery_epoch_after_vote E rho hrec hRead.1 hCut.sync _ ip
    change 4 * p.Δ * (r : Int) + p.Δ < 4 * p.Δ * (r : Int) + 2 * p.Δ
    linarith [p.deltaPos]

/-- Recovery constructs the proposal/gate HEAD support factory. -/
theorem healing_proposal_support_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {r : Slot} {ip : Nat} {x : V} {t : Time}
    (hCut : HealingWindow p E 1 r) (hRead : HealingJoinedTick E rho ip x t)
    (hTime : t = SA.proposalTime p.toParams (r + 1) ∨ t = SA.gateTime p.toParams r) :
    ProposalSupportScope E rho ip x r t := by
  apply healing_proposal_support_scope_of_services E rho hrec hCut hRead hTime
  · intro q b hh hem
    apply healing_fresh_head_service E rho hrec hRead.1 hh hem hCut.sync le_rfl
    have hhor := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hRead.2.1)).2
    apply le_trans _ hhor
    rcases hTime with rfl | rfl
    · change 4 * p.Δ * (r : Int) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int)
      push_cast
      linarith [p.deltaPos]
    · change 4 * p.Δ * (r : Int) + 2 * p.Δ ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ
      linarith [p.deltaPos]
  · exact healing_carriers_recovery E rho hrec r ip x t

/-- An enabled gate needs its actual guard, not a synthetic slot-start premise.
The paired fresh HEAD and target service is the remaining OPEN/P-H1 input. -/
theorem healing_gate_receipt_scope_of_services {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {i : Nat} {x : V}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hGate : enabledGateAt p c E rho i x s)
    (services : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Nonempty (FreshHeadService E rho s q K.root (SA.earlyTime p.toParams s) x) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams s) x) :
    GateReceiptScope E rho i x s := by
  have hg := fgsa_gate_joined_of_enabled E rho hGate
  have hRead := healing_joined_tick_of_guard p c E rho hrec.base.valid hx hGate.1
    (by simpa only [joinedNow, fgsa_clock_restartTime, (clock_vn _ _).2, storeAt] using hg)
  have hs : slotAt p (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  refine ⟨hGate, hs ▸ hRead.2.2, ?_, services⟩
  apply healing_recovery_epoch_after_vote E rho hrec hx hSync _ i
  change 4 * p.Δ * (s : Int) + p.Δ < 4 * p.Δ * (s : Int) + 2 * p.Δ
  linarith [p.deltaPos]

/-- Current-batch support adds the proved joined count to the enabled gate service. -/
theorem healing_support_gate_scope_of_services {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {i : Nat} {x : V}
    (hCut : HealingWindow p E 1 s) (hx : x ∈ rho.honest)
    (hGate : enabledGateAt p c E rho i x s)
    (services : ∀ q K, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Nonempty (FreshHeadService E rho s q K.root (SA.earlyTime p.toParams s) x) ∧
      TargetReceiptService E rho K (SA.earlyTime p.toParams s) x) :
    SupportGateScope E rho i x s := by
  have hh : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hGate.1)).2
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact healing_support_gate_scope_of_cut E rho hrec hCut.2 hCut.sync hh
    (healing_gate_receipt_scope_of_services E rho hrec hCut.sync hx hGate services)

/-- The actual gate geometry supplies the selected emitted targets' receiver floors. -/
theorem healing_gate_receipt_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {i : Nat} {x : V} {B : Block}
    (hSync : E.t_GST ≤ SA.voteTime p.toParams s) (hx : x ∈ rho.honest)
    (hGate : enabledGateAt p c E rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    GateReceiptScope E rho i x s := by
  apply healing_gate_receipt_scope_of_services E rho hrec hSync hx hGate
  intro q K hh hObs
  have hObs0 := hObs
  obtain ⟨j, _, _, hj, hem, _, _⟩ := hObs0
  have hhor := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hGate.1)).2
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  refine ⟨healing_fresh_head_service E rho hrec hx hh ⟨j, hj, hem⟩ hSync le_rfl
    (heg.trans hhor), ?_⟩
  have hK := headTargetAtEmission_at_tick E rho hrec.base.valid.toScheduleWellFormed hObs hj
    (show (ofHead p ⟨.seat (.head s) q, K.root⟩).auth = .seat (.base (.head s)) q from rfl)
  have hm := headVote_stored p
    (clock p (storeAt p c E rho j (rho.seatOf (.base (.head s)) q))
      (SA.voteTime p.toParams s))
    (storeBundle_postClock E rho j (rho.seatOf (.base (.head s)) q)
      (SA.voteTime p.toParams s)).cstore s
  simp only [storeAt] at hm
  rw [← hK] at hm
  change K ∈ (clock p (storeAt p c E rho j _) _).base.blocks at hm
  rw [(clock_cumulative p _ _).2.1] at hm
  have hFloor := hgeom.target_floor q hh
    (hrec.base.valid.tick_awake _ _ (List.mem_of_getElem? hj)) K hObs
  rw [clockPre_fg] at hFloor
  have hFE := healing_receipt_floor_before_tick E rho hrec.base.valid.toScheduleWellFormed
    mono hx hGate.1 heg hFloor
  have hpub : V2.PublicTime E (SA.voteTime p.toParams s) := by
    refine ⟨4 * s + 1, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ = _
    push_cast
    ring
  have he : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  rw [← he] at hFE ⊢
  exact healing_target_service_of_tick E rho hrec hh hx hj hm hpub hSync
    (he ▸ heg.trans hhor) (Bool.or_eq_true_iff.mpr (Or.inr hFE))

/-- Current full-batch gates use the produced selected receipt scopes. -/
theorem healing_support_gate_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {i : Nat} {x : V} {B : Block}
    (hCut : HealingWindow p E 1 s) (hx : x ∈ rho.honest)
    (hGate : enabledGateAt p c E rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    SupportGateScope E rho i x s := by
  have hh : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hGate.1)).2
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  exact healing_support_gate_scope_of_cut E rho hrec hCut.2 hCut.sync hh
    (healing_gate_receipt_scope_recovery E rho hrec mono hCut.sync hx hGate hgeom)

/-- A full joined batch supplies the release threshold for its covered prefix. -/
theorem healing_support_gate_prefix_count {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {i : Nat} {x : V} {B : Block}
    (hCut : HealingWindow p E 1 s) (hi : IsGateTick p c rho i x s)
    (hScope : SupportGateScope E rho i x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s))) s B := by
  classical
  have hE := hrec.base.valid
  have hh := (hE.in_horizon _ (List.mem_of_getElem? hi)).2
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvh : SA.voteTime p.toParams s ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hCut.sync hvd hh
  let H := healingJoinedSeats E rho s
  let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
  let view := actView pre
  obtain ⟨hrelease, hbatch⟩ := healing_recovery_seat_counts E rho hrec hCut hvh
  have receipts := fgsa_gateReceipt_on (hroots := hrec.base.receiptIdealization)
    E rho hE hrec.base.delta hrec.base.cstar s hSync hi B hgeom hScope.toGateReceiptScope
  have hsupp : ∀ k ∈ H, Gen.AC.Root.poolSupports view.blocks
      (GridCO.cleanSupport p.toParams.engine view s) k B = true := by
    intro k hk
    obtain ⟨hhon, hjoin⟩ := (healingJoinedSeats_mem E rho s k).mp hk
    obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, _, hBK⟩ :=
      receipts.2.2 k hhon hjoin
    exact fgsa_active_support_of_receipt E rho hE i x s k K B t hh he hv hK hslot hvs hbs hBK
  have hrest := fgsa_late_rest_bound_joined E rho hrec.base.cstar hE i x s H
    (fun k hk hj => (healingJoinedSeats_mem E rho s k).mpr ⟨hk, hj⟩)
  have hc := Gen.AC.Root.batch_counts view.blocks (GridCO.lateVotes p.toParams.engine view s)
    (GridCO.cleanSupport p.toParams.engine view s) (GridCO.cleanSupport p.toParams.engine view s)
    H H.card (Gen.V2.Duty.faulty rho).card B
    (fun _ ho => fgsa_early_subset_late p view s (List.mem_filter.mp ho).1)
    (fun _ ho => ho) rfl (fun k _ => fgsa_cleanSupport_no_equivocation p view s k)
    hsupp hrest hbatch
  have he := actView_score p pre
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _)
    (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i x))
    (GridCO.cleanSupport p.toParams.engine view s) (GridCO.cleanSupport p.toParams.engine view s) B
  have hcount : H.card ≤ SA.Root.prefixSupport p.toParams view s B := by
    change _ ≤ GridCO.goldfishScoreOn (GridCO.resolutionTree view) view.blocks _ _ B
    rw [he]
    exact (hc.2.2.1 B (Gen.Pure.block_preceq_refl B)).1
  exact hrelease.trans hcount

/-- N4: a later full post-Jst batch releases incompatible leases of every age.
No expiry bound or upper bound on k is used. Object relay remains in first/gate scopes. -/
theorem healing_ready_batch_release_compat {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {ix iy : Nat} {x y : V} {B : Block}
    (hready : recoveryStart p E ≤ SA.voteTime p.toParams s)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (gate : SupportGateScope E rho ix x s)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)) s B)
    (first : FirstTransferScope E rho ix iy x y s)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B) :
    ∀ row ∈ (clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 B := by
  have hCut := healing_window_of_cut E (healing_ready_vote_cutoff E hready)
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [hrec.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hix)).2
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hCut.sync hvd hh
  exact healing_support_release_compat (hroots := hrec.base.receiptIdealization)
    E rho hrec.base.valid hrec.base.delta s hSync hx hy hix hiy first
    (healing_support_gate_prefix_count E rho hrec hCut hix gate hgeom) hFB

section Factories

-- These are exact OPEN/P-H1 leaf factories. Their consumers do not prove them.
variable
    (first : ∀ s ix iy x y, E.t_GST ≤ SA.voteTime p.toParams s →
      x ∈ rho.honest → y ∈ rho.honest → IsGateTick p c rho ix x s →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      enabledGateAt p c E rho ix x s →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      FirstTransferScope E rho ix iy x y s)
    (next : ∀ s iy y, HealingWindow p E 1 s → y ∈ rho.honest →
      rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      NextTransferScope E rho iy y s)
    (gates : ∀ s i x, HealingWindow p E 1 s → x ∈ rho.honest →
      IsGateTick p c rho i x s → enabledGateAt p c E rho i x s →
      ∀ B, GateReceiptGeometry E rho
        (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B →
      SupportGateScope E rho i x s)
    (carriers : ∀ s iy y t, HealingCarriersAt E rho s iy y t)
    (proposal : ∀ r ip x t, HealingWindow p E 1 r →
      HealingJoinedTick E rho ip x t →
      (t = SA.proposalTime p.toParams (r + 1) ∨ t = SA.gateTime p.toParams r) →
      ProposalSupportScope E rho ip x r t)

include first next gates carriers

/-- Conditional P3 assembly. Recovery proves the source guard and same-label service.
Production closure still requires the four exact leaf factories above. -/
theorem healing_fast_support_scope_of_factories {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {v : Time} {x : V}
    (hCut : HealingWindow p E 1 s) (hx : x ∈ rho.honest) :
    FastSupportScope E rho s v x := by
  refine ⟨?_, ?_, ?_, ?_, ?_, healing_recovery_same_label E rho hrec s hCut.sync⟩
  · intro ix hi
    exact healing_recovery_gate_enabled E rho hrec hx hi
      (healing_gate_cut_of_batch_cut E s hCut.2)
  · intro ix iy y hy hi hj _ hg hJ
    exact first s ix iy x y hCut.sync hx hy hi hj hg hJ
  · intro w hw _ iy y hy hi hj
    exact next w iy y (hCut.cut_mono ((Nat.le_succ s).trans hw)) hy hi hj
  · intro w hw _ j y hy hi hg B hgeom
    exact gates w j y (hCut.cut_mono ((Nat.le_succ s).trans hw)) hy hi hg B hgeom
  · intro w _ iy y t _
    exact carriers w iy y t

include proposal

/-- Conditional P4 assembly. The saved window uses GST and same-label uniqueness.
It requests no release count for the slow source. -/
theorem healing_slow_support_scope_of_factories {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {v : Time} {x : V}
    (hCut : HealingWindow p E 1 s)
    (hWindow : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k))
    (hx : x ∈ rho.honest) : SlowSupportScope E rho s v x := by
  refine ⟨healing_fast_support_scope_of_factories E rho first next gates carriers
    hrec hCut hx, ?_, ?_⟩
  · intro j hi hg
    have hguard := fgsa_gate_joined_of_enabled E rho hg
    have hread := healing_joined_tick_of_guard p c E rho hrec.base.valid hx hi
      (by simpa only [joinedNow, fgsa_clock_restartTime, (clock_vn _ _).2, storeAt] using hguard)
    exact proposal s j x _ hCut hread (Or.inr rfl)
  · intro w hw _
    apply healing_recovery_same_label E rho hrec w
    apply le_trans hWindow
    change 4 * p.Δ * ((s + 1 - p.k : Nat) : Int) + p.Δ ≤
      4 * p.Δ * (w : Int) + p.Δ
    have h : ((s + 1 - p.k : Nat) : Int) ≤ w := by exact_mod_cast hw
    nlinarith [p.deltaPos]

/-- Conditional uniform P5 assembly over one ready phase.
The same leaf factories serve both bodies and every later bounded proposal. -/
theorem healing_support_permanence_of_factories {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (_hready : recoveryStart p E ≤ u)
    (_hphase : PhaseInterval p c E rho u v m J contested) :
    SupportPermanenceServices E rho u v m J contested := by
  refine ⟨?_, ?_, ?_⟩
  · intro s x nd B hCut _ _ hx _ _
    exact healing_fast_support_scope_of_factories E rho first next gates carriers hrec hCut hx
  · intro s x st C B j hCut _ _ hx hWindow _ _ _ _ _
    exact healing_slow_support_scope_of_factories E rho first next gates carriers proposal
      hrec hCut hWindow hx
  · intro s B hCut _ _ _ r hr _ ip x hx hip hjoin
    have hread : HealingJoinedTick E rho ip x (SA.proposalTime p.toParams (r + 1)) := by
      refine ⟨hx, hip, ?_⟩
      have hs : slotAt p (SA.proposalTime p.toParams (r + 1)) = r + 1 :=
        (fgsa_postClock_slot (c := c) (rho.stateBefore E ip x) _).2.symm.trans
          (fgsa_proposal_slot (c := c) _ (r + 1))
      simpa only [hs] using hjoin
    exact proposal r ip x _ (hCut.cut_mono ((Nat.le_succ s).trans hr)) hread (Or.inl rfl)

omit [Fintype V] next proposal in
/-- Conditional P7 assembly keeps each gate's selected geometry. -/
theorem healing_repair_gate_scope_of_factories {s : Slot}
    (hCut : HealingWindow p E 1 s) : RepairGateScope E rho s := by
  refine ⟨hCut.2, ?_, ?_, ?_⟩
  · intro i x hx hi hg B hgeom
    exact (gates s i x hCut hx hi hg B hgeom).toGateReceiptScope
  · intro i iq x hx hi hq hg hj
    exact first s i iq x x hCut.sync hx hx hi hq hg hj
  · intro iy y t _ _
    exact carriers s iy y t

/-- Conditional P8 assembly produces its seed readers from recovery. -/
theorem healing_frontier_read_scope_of_factories {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {q : Slot} {v : Time}
    (hCut : HealingWindow p E 1 q)
    (hGate : SA.gateTime p.toParams q ≤ v) (hHor : v ≤ rho.horizon) :
    FrontierReadScope E rho q v := by
  have _hBound : SA.gateTime p.toParams q ≤ rho.horizon := hGate.trans hHor
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact healing_fast_support_scope_of_factories E rho first next gates carriers hrec hCut hx
  · intro s _ _ hSync i iq x hx hi hg hq hj
    exact first s i iq x x hSync hx hx hi hq hg hj
  · intro w hw _ x nd B hx _ _
    exact healing_fast_support_scope_of_factories E rho first next gates carriers
      hrec (hCut.cut_mono ((Nat.le_succ q).trans hw)) hx
  · intro w hw _ hWindow x st C B j hx _ _ _ _ _
    exact healing_slow_support_scope_of_factories E rho first next gates carriers proposal
      hrec (hCut.cut_mono ((Nat.le_succ q).trans hw)) hWindow hx
  · intro r hr _ ip x hx hip hj
    have hs : slotAt p (SA.proposalTime p.toParams (r + 1)) = r + 1 :=
      (fgsa_postClock_slot (c := c) (rho.stateBefore E ip x) _).2.symm.trans
        (fgsa_proposal_slot (c := c) _ (r + 1))
    exact proposal r ip x _ (hCut.cut_mono ((Nat.le_succ q).trans hr))
      ⟨hx, hip, by simpa only [hs] using hj⟩ (Or.inl rfl)
  · intro r hr _ ih y hy hi hj
    exact next r ih y (hCut.cut_mono ((Nat.le_succ q).trans hr)) hy hi hj
  · intro r _ iy y t _
    exact carriers r iy y t

omit first next gates carriers in
/-- Conditional P6 assembly produces the prior proposal scope at its real tick.
The retained object-service input remains OPEN/P-H1 with P-ShA. -/
theorem healing_repair_head_services_of_factories {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s : Slot} {ip : Nat} {x : V}
    {N : NamedProposal p.n} (hCut : HealingWindow p E 2 s) (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (_hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip)
    (scopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      Block.Preceq (eraseFG (rho.stateBeforeTime E
        (SA.voteTime p.toParams s) y).st.fg.F) N.erase →
      RetainedServiceScope E rho ip ih x y s N) : RepairHeadServices E rho s ip x N := by
  have hh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hip)).2
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    have hc := hCut.2
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 2) at hc
    change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
    linarith [p.deltaPos]
  have hsync : E.t_GST ≤ SA.proposalTime p.toParams s := by
    apply le_trans hcut
    change 4 * p.Δ * ((s : Int) - 1) ≤ 4 * p.Δ * (s : Int)
    linarith [p.deltaPos]
  have hjoin := healing_recovery_joined E rho hrec hx hcut hsync hh
  have hs : slotAt p (SA.proposalTime p.toParams s) = s :=
    (fgsa_postClock_slot (c := c) (rho.stateBefore E ip x) _).2.symm.trans
      (fgsa_proposal_slot (c := c) _ s)
  have hread : HealingJoinedTick E rho ip x (SA.proposalTime p.toParams s) :=
    ⟨hx, hip, by simpa only [hs] using hjoin⟩
  refine ⟨proposal (s - 1) ip x _ hCut.prior hread ?_, scopes⟩
  left
  have hs : (s - 1 : Nat) + 1 = s := Nat.sub_add_cancel
    (Nat.le_trans (by decide : 1 ≤ 2) hCut.1)
  rw [hs]

omit first next gates carriers proposal in
/-- Recovery constructs the retained proposal and every selected score service. -/
theorem healing_retained_service_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {ip ih : Nat} {x y : V} {N : NamedProposal p.n}
    (hCut : HealingWindow p E 2 s) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip)
    (hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
      (SA.voteTime p.toParams s) y).st.fg.F) N.erase) :
    RetainedServiceScope E rho ip ih x y s N := by
  have hs : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by have := hCut.1; omega
  have hSync : E.t_GST ≤ SA.proposalTime p.toParams (s - 1) := by
    apply le_trans hCut.2
    change 4 * p.Δ * ((s : Int) - 2) ≤ 4 * p.Δ * ((s - 1 : Nat) : Int)
    rw [hs]
    linarith [p.deltaPos]
  have hpp : SA.proposalTime p.toParams (s - 1) ≤ SA.proposalTime p.toParams s := by
    change 4 * p.Δ * ((s - 1 : Nat) : Int) ≤ 4 * p.Δ * (s : Int)
    rw [hs]
    linarith [p.deltaPos]
  have he : SA.freezeTime p.toParams (s - 1) + p.Δ = SA.proposalTime p.toParams s := by
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ + p.Δ = 4 * p.Δ * (s : Int)
    rw [hs]
    ring
  have hpf : SA.proposalTime p.toParams (s - 1) ≤ SA.freezeTime p.toParams (s - 1) := by
    change 4 * p.Δ * ((s - 1 : Nat) : Int) ≤
      4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ
    linarith [p.deltaPos]
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams (s - 1)) := by
    refine ⟨4 * (s - 1) + 3, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ = _
    push_cast
    ring
  have hh := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hih)).2
  have hhp := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hip)).2
  refine ⟨healing_retained_proposal_service E rho hrec hx hy hip hem
    (hSync.trans hpp) hh hFloor, ?_⟩
  intro D hgeom
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply healing_recovery_epoch_after_vote E rho hrec hx hCut.prior.sync _ ip
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + p.Δ < 4 * p.Δ * (s : Int)
    rw [hs]
    linarith [p.deltaPos]
  · intro q b hm hstamp hNX
    rw [← he] at hNX
    apply healing_stored_head_service E rho hrec hy hx hm hstamp hSync hpf hpub
      he.le hhp hNX
  · intro B hDB hB
    have hFB : Block.Preceq (eraseFG (storeAt p c E rho ih y).fg.F) B := by
      apply Gen.Pure.block_preceq_trans _ hDB
      simpa only [clock_fg, storeAt] using hgeom.target_floor
    have hFloorB := healing_receipt_floor_before_tick E rho
      hrec.base.valid.toScheduleWellFormed mono hy hih le_rfl hFB
    have hpubP : V2.PublicTime E (SA.proposalTime p.toParams s) := by
      refine ⟨4 * s, ?_⟩
      rw [hrec.base.delta]
      change 4 * p.Δ * (s : Int) = _
      push_cast
      ring
    exact healing_target_service_of_tick E rho hrec hx hy hip hB hpubP (hSync.trans hpp)
      hh (Bool.or_eq_true_iff.mpr (Or.inr hFloorB))
  · intro B hDB hB hstamp
    have hFB : Block.Preceq (eraseFG (storeAt p c E rho ip x).fg.F) B := by
      apply Gen.Pure.block_preceq_trans _ hDB
      simpa only [clock_fg, storeAt] using hgeom.source_floor
    have hFloorB := healing_receipt_floor_before_tick E rho
      hrec.base.valid.toScheduleWellFormed mono hx hip le_rfl hFB
    rw [← he] at hFloorB ⊢
    exact healing_target_service_of_stored E rho hrec hy hx hB hstamp hpub
      (hSync.trans hpf) (he ▸ hhp) (Bool.or_eq_true_iff.mpr (Or.inr hFloorB))

omit first next gates carriers proposal in
/-- Repair HEAD services now use the produced retained scope at each actual reader. -/
theorem healing_repair_head_services_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {ip : Nat} {x : V} {N : NamedProposal p.n}
    (hCut : HealingWindow p E 2 s) (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈ rho.emitsAt E ip) :
    RepairHeadServices E rho s ip x N := by
  apply healing_repair_head_services_of_factories E rho
    (proposal := fun r j z t hC hR hT =>
      healing_proposal_support_scope_recovery E rho hrec hC hR hT) hrec hCut hx hip hem
  intro y hy ih hih hJoin hFloor
  exact healing_retained_service_scope_recovery E rho hrec mono hCut hx hy hip hih hem hFloor

variable
    (rawGates : ∀ s i x, E.t_GST ≤ SA.voteTime p.toParams s → x ∈ rho.honest →
      IsGateTick p c rho i x s → enabledGateAt p c E rho i x s →
      ∀ B, GateReceiptGeometry E rho
        (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B →
      GateReceiptScope E rho i x s)

omit next gates carriers in
include rawGates in
/-- Conditional P10 assembly; same-label service is produced for every synchronous label.
The gate factory uses its actual enabled guard even at the minimum GST vote cut. -/
theorem healing_raw_service_scope_of_factories {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) : RawServiceScope p c E rho := by
  refine ⟨?_, first, ?_, rawGates, ?_⟩
  · intro s ix x hCut hx hi hg
    have hg' := fgsa_gate_joined_of_enabled E rho hg
    have hread := healing_joined_tick_of_guard p c E rho hrec.base.valid hx hi
      (by simpa only [joinedNow, fgsa_clock_restartTime, (clock_vn _ _).2, storeAt] using hg')
    exact proposal s ix x _ hCut hread (Or.inr rfl)
  · intro r ip x hCut hx hip hj
    have hs : slotAt p (SA.proposalTime p.toParams (r + 1)) = r + 1 :=
      (fgsa_postClock_slot (c := c) (rho.stateBefore E ip x) _).2.symm.trans
        (fgsa_proposal_slot (c := c) _ (r + 1))
    exact proposal r ip x _ hCut ⟨hx, hip, by simpa only [hs] using hj⟩ (Or.inl rfl)
  · intro s hSync
    exact healing_recovery_same_label E rho hrec s hSync

omit first next gates carriers proposal rawGates in
/-- A selected prior source is served from its honest supporting HEAD history. -/
theorem healing_source_before_receipt_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (source : TSrc p c E rho) {i k : Nat} {K : FGBlock (Fin p.n)} {s u : Slot} {x : V}
    (hSource : SourceBefore p c E rho i K s) (hsu : s ≤ u)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams u) (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (u + 1))))
    (hFloor : FGBlock.Preceq (storeAt p c E rho k x).fg.F K) :
    TargetReceiptService E rho (eraseFG K) (SA.freezeTime p.toParams u) x := by
  unfold SourceBefore at hSource
  obtain ⟨j, y, r, a, _, ha, hK, rfl⟩ := hSource
  obtain ⟨jz, z, W, hz, hjz, hW, hKW⟩ :=
    healing_source_supporter_head E rho hrec.toRecovery₂ source ha.1 hK
  have hKs := KitFG.ancestor_closed_of_parent_closed _
    (storeBundle_stateBefore E rho jz z).cstore.fg.closed W hW K hKW
  have he : SA.earlyTime p.toParams u + p.Δ = SA.freezeTime p.toParams u := by
    change 4 * p.Δ * (u : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (u : Int) + 3 * p.Δ
    ring
  have hfr : SA.freezeTime p.toParams u ≤ SA.voteTime p.toParams (u + 1) := by
    change 4 * p.Δ * (u : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((u + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hFE := healing_receipt_floor_before_tick E rho hrec.base.valid.toScheduleWellFormed
    mono hx hk hfr (eraseFG_preceq hFloor)
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams u) := by
    refine ⟨4 * u + 2, ?_⟩
    rw [hrec.base.delta]
    change 4 * p.Δ * (u : Int) + 2 * p.Δ = _
    push_cast
    ring
  rw [← he] at hFE ⊢
  refine healing_target_service_of_earlier_tick E rho hrec hz hx hjz
    (((storeBundle_stateBefore E rho jz z).cstore.baseTree _).mpr ⟨K, hKs, rfl⟩)
    ?_ hpub ?_ ?_ ?_
  · change 4 * p.Δ * ((r * p.R : Nat) : Int) + p.Δ < 4 * p.Δ * (u : Int) + 2 * p.Δ
    have hsuI : ((r * p.R : Nat) : Int) ≤ u := by exact_mod_cast hsu
    nlinarith [p.deltaPos]
  · apply le_trans hSync
    change 4 * p.Δ * (u : Int) + p.Δ ≤ 4 * p.Δ * (u : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · exact he ▸ hfr.trans (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hk)).2
  · exact Bool.or_eq_true_iff.mpr (Or.inr hFE)

variable
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (receipts : ∀ i K s u k x, SourceBefore p c E rho i K s → s ≤ u →
      E.t_GST ≤ SA.voteTime p.toParams u → x ∈ rho.honest →
      rho.events[k]? = some (.tick x (SA.voteTime p.toParams (u + 1))) →
      joinedAt p E rho x (u + 1) (SA.voteTime p.toParams (u + 1)) →
      FGBlock.Preceq (storeAt p c E rho k x).fg.F K →
      TargetReceiptService E rho (eraseFG K) (SA.freezeTime p.toParams u) x)

omit proposal in
include emittedNonempty emittedName receipts in
/-- Conditional P9 assembly uses the named Foundation source-origin telescope.
Readiness of each high source is proved; receipt keeps its original selected source. -/
theorem healing_loss_service_scope_of_factories {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) : LossServiceScope p c E rho := by
  refine ⟨?_, ?_, ?_, ?_, receipts⟩
  · intro i K K' s hK _ hc _
    exact healing_recovery_same_label E rho hrec s
      (healing_high_source_sync p c E rho emittedNonempty emittedName hK hc)
  · intro B sB iy y hB hy hiy hJ ix xs hx hi hres
    rw [HighSrcN_def, SrcN_def] at hB
    have hSync := healing_high_source_sync p c E rho emittedNonempty emittedName hB.1 hB.2
    obtain ⟨C, hres, _⟩ := hres
    exact first sB ix iy xs y hSync hx hy hi hiy
      (healing_gate_enabled_of_result E rho hrec.base.valid.toScheduleWellFormed hi hres) hJ
  · intro B sB i iy y hB hi hy hiy hJ
    rw [HighSrcN_def, SrcN_def] at hB
    have hCut := healing_high_source_window p c E rho emittedNonempty emittedName hB.1 hB.2
    exact next i iy y (hCut.cut_mono ((Nat.le_succ sB).trans hi)) hy hiy hJ
  · intro B sB l k x hB _ _ _ y nd hy _ _
    rw [HighSrcN_def, SrcN_def] at hB
    have hCut := healing_high_source_window p c E rho emittedNonempty emittedName hB.1 hB.2
    exact healing_fast_support_scope_of_factories E rho first next gates carriers hrec hCut hy

end Factories

/-- P3: all fast phase services have recovery producers, including the cap branches. -/
theorem healing_fast_support_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {v : Time} {x : V} (hCut : HealingWindow p E 1 s)
    (hx : x ∈ rho.honest) : FastSupportScope E rho s v x := by
  apply healing_fast_support_scope_of_factories E rho
    (first := fun _ _ _ _ _ hSync hx hy hi hj hg hJ =>
      healing_first_transfer_scope_recovery E rho hrec mono hSync hx hy hi hj hg hJ)
    (next := fun _ _ _ hCut hy hi hJ =>
      healing_next_transfer_scope_recovery E rho hrec hCut hy hi hJ)
    (gates := fun _ _ _ hCut hx _ hg _ hgeom =>
      healing_support_gate_scope_recovery E rho hrec mono hCut hx hg hgeom)
    (carriers := fun s iy y t => healing_carriers_recovery E rho hrec s iy y t)
    hrec hCut hx

/-- P4: slow phase services use the full saved window and same-label uniqueness. -/
theorem healing_slow_support_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {v : Time} {x : V} (hCut : HealingWindow p E 1 s)
    (hWindow : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k))
    (hx : x ∈ rho.honest) : SlowSupportScope E rho s v x := by
  refine ⟨healing_fast_support_scope_recovery E rho hrec mono hCut hx, ?_, ?_⟩
  · intro j hi hg
    have hguard := fgsa_gate_joined_of_enabled E rho hg
    have hread := healing_joined_tick_of_guard p c E rho hrec.base.valid hx hi
      (by simpa only [joinedNow, fgsa_clock_restartTime, (clock_vn _ _).2, storeAt] using hguard)
    exact healing_proposal_support_scope_recovery E rho hrec hCut hread (Or.inr rfl)
  · intro w hw _
    apply healing_recovery_same_label E rho hrec w
    apply le_trans hWindow
    change 4 * p.Δ * ((s + 1 - p.k : Nat) : Int) + p.Δ ≤
      4 * p.Δ * (w : Int) + p.Δ
    have h : ((s + 1 - p.k : Nat) : Int) ≤ w := by exact_mod_cast hw
    nlinarith [p.deltaPos]

/-- P5: recovery produces both body arms and every bounded proposal service.
There is no service callback in this producer. -/
theorem healing_support_permanence_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (_hready : recoveryStart p E ≤ u)
    (_hphase : PhaseInterval p c E rho u v m J contested) :
    SupportPermanenceServices E rho u v m J contested := by
  refine ⟨?_, ?_, ?_⟩
  · intro s x nd B hCut _ _ hx _ _
    exact healing_fast_support_scope_recovery E rho hrec mono hCut hx
  · intro s x st C B j hCut _ _ hx hWindow _ _ _ _ _
    exact healing_slow_support_scope_recovery E rho hrec mono hCut hWindow hx
  · intro s B hCut _ _ _ r hr _ ip x hx hip hjoin
    have hread : HealingJoinedTick E rho ip x (SA.proposalTime p.toParams (r + 1)) := by
      refine ⟨hx, hip, ?_⟩
      have hs : slotAt p (SA.proposalTime p.toParams (r + 1)) = r + 1 :=
        (fgsa_postClock_slot (c := c) (rho.stateBefore E ip x) _).2.symm.trans
          (fgsa_proposal_slot (c := c) _ (r + 1))
      simpa only [hs] using hjoin
    exact healing_proposal_support_scope_recovery E rho hrec
      (hCut.cut_mono ((Nat.le_succ s).trans hr)) hread (Or.inl rfl)

/-- P7: selected repair gate services have complete recovery factories. -/
theorem healing_repair_gate_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} (hCut : HealingWindow p E 1 s) : RepairGateScope E rho s := by
  apply healing_repair_gate_scope_of_factories E rho
    (first := fun _ _ _ _ _ hSync hx hy hi hj hg hJ =>
      healing_first_transfer_scope_recovery E rho hrec mono hSync hx hy hi hj hg hJ)
    (gates := fun _ _ _ hCut hx _ hg _ hgeom =>
      healing_support_gate_scope_recovery E rho hrec mono hCut hx hg hgeom)
    (carriers := fun s iy y t => healing_carriers_recovery E rho hrec s iy y t)
    hCut

/-- P8: the bounded frontier read services are produced from recovery. -/
theorem healing_frontier_read_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {q : Slot} {v : Time} (hCut : HealingWindow p E 1 q)
    (hGate : SA.gateTime p.toParams q ≤ v) (hHor : v ≤ rho.horizon) :
    FrontierReadScope E rho q v := by
  apply healing_frontier_read_scope_of_factories E rho
    (first := fun _ _ _ _ _ hSync hx hy hi hj hg hJ =>
      healing_first_transfer_scope_recovery E rho hrec mono hSync hx hy hi hj hg hJ)
    (next := fun _ _ _ hCut hy hi hJ =>
      healing_next_transfer_scope_recovery E rho hrec hCut hy hi hJ)
    (gates := fun _ _ _ hCut hx _ hg _ hgeom =>
      healing_support_gate_scope_recovery E rho hrec mono hCut hx hg hgeom)
    (carriers := fun s iy y t => healing_carriers_recovery E rho hrec s iy y t)
    (proposal := fun _ _ _ _ hCut hRead hTime =>
      healing_proposal_support_scope_recovery E rho hrec hCut hRead hTime)
    hrec hCut hGate hHor

/-- P10: enabled raw gates keep their actual geometry and GST vote-time cut. -/
theorem healing_raw_service_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho) :
    RawServiceScope p c E rho := by
  apply healing_raw_service_scope_of_factories E rho
    (first := fun _ _ _ _ _ hSync hx hy hi hj hg hJ =>
      healing_first_transfer_scope_recovery E rho hrec mono hSync hx hy hi hj hg hJ)
    (proposal := fun _ _ _ _ hCut hRead hTime =>
      healing_proposal_support_scope_recovery E rho hrec hCut hRead hTime)
    (rawGates := fun _ _ _ hSync hx _ hg _ hgeom =>
      healing_gate_receipt_scope_recovery E rho hrec mono hSync hx hg hgeom) hrec

/-- P9: selected high-source loss services use the named source-origin Foundations. -/
theorem healing_loss_service_scope_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (source : TSrc p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
 : LossServiceScope p c E rho := by
  apply healing_loss_service_scope_of_factories E rho
    (first := fun _ _ _ _ _ hSync hx hy hi hj hg hJ =>
      healing_first_transfer_scope_recovery E rho hrec mono hSync hx hy hi hj hg hJ)
    (next := fun _ _ _ hCut hy hi hJ =>
      healing_next_transfer_scope_recovery E rho hrec hCut hy hi hJ)
    (gates := fun _ _ _ hCut hx _ hg _ hgeom =>
      healing_support_gate_scope_recovery E rho hrec mono hCut hx hg hgeom)
    (carriers := fun s iy y t => healing_carriers_recovery E rho hrec s iy y t)
    emittedNonempty emittedName
    (receipts := fun _ _ _ _ _ _ hSource hsu hSync hx hk _ hFloor =>
      healing_source_before_receipt_recovery E rho hrec mono source hSource hsu hSync hx hk
        hFloor) hrec

/-- N4: a full batch after Jst releases incompatible leases, with all services produced.
The result has no lease-age assumption and no upper bound on k. -/
theorem healing_ready_batch_release_compat_recovery {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    {s : Slot} {ix iy : Nat} {x y : V} {B : Block}
    (hready : recoveryStart p E ≤ SA.voteTime p.toParams s)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hix : IsGateTick p c rho ix x s)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s)) s B)
    (hFB : Block.Preceq (eraseFG (storeAt p c E rho iy y).fg.F) B) :
    ∀ row ∈ (clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))).base.obligations, Block.Compatible row.1 B := by
  have hCut := healing_window_of_cut E (healing_ready_vote_cutoff E hready)
  have hG := healing_recovery_gate_enabled E rho hrec hx hix
    (healing_gate_cut_of_batch_cut E s hCut.2)
  have hhor := (hrec.base.valid.in_horizon _ (List.mem_of_getElem? hiy)).2
  have hJ := healing_recovery_joined E rho hrec hy (s := s + 1)
    (hCut.cut_mono (Nat.le_succ s)).2 (hCut.sync.trans ?_) hhor
  · exact healing_ready_batch_release_compat E rho hrec hready hx hy hix hiy
      (healing_support_gate_scope_recovery E rho hrec mono hCut hx hG hgeom) hgeom
      (healing_first_transfer_scope_recovery E rho hrec mono hCut.sync hx hy hix hiy hG hJ) hFB
  · change SA.voteTime p.toParams s ≤ SA.voteTime p.toParams (s + 1)
    change 4 * p.Δ * (s : Int) + p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]

end AvailableChain.FGSA.Run
end
