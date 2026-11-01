module
public import AvailableChainFGSAProofs.Proofs.Shared.Count
public import AvailableChainFGSAProofs.Proofs.Healing.SupportRecovery

public section

/-! H-SUPPORT gate cover (plan §4 steps 7–8; G7). At a label where every honest HEAD
covers B, the raw confirmation of each honest gate in the synchronous window covers B. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.AC.Root

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- One enabled gate and a batch of joined voters at its actual source label. -/
structure SupportGateScope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (x : V) (s : Slot) : Prop extends GateReceiptScope E rho i x s where
  batch : ∀ [Fintype V], Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams s)).card
    (Gen.V2.Duty.faulty rho).card

/-- Actual joined-voter counts assemble this one receipt scope. -/
theorem healing_support_gate_scope_of_batch [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {i : Nat} {x : V} {s : Slot}
    (hScope : GateReceiptScope E rho i x s)
    (hBatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams s)).card
      (Gen.V2.Duty.faulty rho).card) : SupportGateScope E rho i x s := by
  let instOld : Fintype V := inferInstance
  refine ⟨hScope, ?_⟩
  intro instNew
  have he : instNew = instOld := Subsingleton.elim _ _
  cases he
  exact hBatch

/-- The regime constructs the selected batch only when the caller has this cut. -/
theorem healing_support_gate_scope_of_cut [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {s : Slot}
    (hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon)
    (hScope : GateReceiptScope E rho i x s) : SupportGateScope E rho i x s := by
  let instOld : Fintype V := inferInstance
  refine ⟨hScope, ?_⟩
  intro instNew
  have he : instNew = instOld := Subsingleton.elim _ _
  cases he
  exact (healing_recovery_joined_counts E rho hrec s hcut hgst hhor).2

/-- The gate join test gives the enabled actor at this tick. -/
theorem healing_gate_enabled_of_joined (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {i : Nat} {x : V} {s : Slot}
    (hi : IsGateTick p c rho i x s)
    (hj : joinedAtTime p (storeAt p c E rho i x).restartTime
      (SA.gateTime p.toParams s) = true) : enabledGateAt p c E rho i x s := by
  refine ⟨hi, ?_⟩
  have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) _ s)
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some t =>
    change t ≤ 4 * p.Δ * (s : Int)
    simpa only [joinedAtTime, hr, hs, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, decide_eq_true_eq] using hj

/-- A nonempty saved result was produced by an enabled gate. -/
theorem healing_gate_enabled_of_result (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} {B : Block} (hi : IsGateTick p c rho i x s)
    (hr : gateResultAt p c E rho i = some (some B)) : enabledGateAt p c E rho i x s := by
  apply healing_gate_enabled_of_joined E rho hi
  exact (fgsa_gate_raw_of_nonempty p c E rho hS hi
    ((gateResultAt_eq_gateResult p c E rho hS hi).symm.trans hr)).1

/-- The actual gate's integer cutoff supplies its enabled guard in recovery. -/
theorem healing_recovery_gate_enabled [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x s)
    (hc : E.t_GST ≤ slotStartZ p (s : Int)) : enabledGateAt p c E rho i x s := by
  refine ⟨hi, ?_⟩
  have hb := fgsa_restartTime_bound E rho i x (slotStartZ p (s : Int)) (by
    intro j t _ hj
    exact (healing_recovery_restart_bound E rho hrec hx hj).trans hc)
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some t => exact hb t hr

omit [DecidableEq V] in
/-- A current-batch cutoff also includes the gate's own cutoff. -/
theorem healing_gate_cut_of_batch_cut (E : Generic.Env V) (s : Slot)
    (hc : E.t_GST ≤ slotStartZ p ((s : Int) - 1)) :
    E.t_GST ≤ slotStartZ p (s : Int) := by
  change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1) at hc
  change E.t_GST ≤ 4 * p.Δ * (s : Int)
  linarith [p.deltaPos]

/-- Later gate actors use their own cutoff, not the previous vote-label cutoff. -/
theorem healing_recovery_later_gate [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {s w : Slot}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s) (hw : s + 1 ≤ w)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (hi : IsGateTick p c rho i x w) :
    enabledGateAt p c E rho i x w := by
  refine ⟨hi, ?_⟩
  have hcut : E.t_GST ≤ slotStartZ p (w : Int) := by
    have hsw : (s : Int) + 1 ≤ w := by exact_mod_cast hw
    change E.t_GST ≤ 4 * p.Δ * (s : Int) + p.Δ at hgst
    change E.t_GST ≤ 4 * p.Δ * (w : Int)
    nlinarith [p.deltaPos]
  have hb := fgsa_restartTime_bound E rho i x (slotStartZ p (w : Int)) (by
    intro k t _ hk
    exact (healing_recovery_restart_bound E rho hrec hx hk).trans hcut)
  cases hr : (storeAt p c E rho i x).restartTime with
  | none => trivial
  | some t => exact hb t hr

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:709–715 (H.2 S1); plan H-SUPPORT §4 step 7.
DC: SAME a HEAD that an honest seat emits is its HEAD read at that label. -/
theorem healing_support_emitted_head (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (w : Slot) (q : Fin p.n) (K : Block) (t : Time)
    (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head w)) q)
      (ofHead p ⟨.seat (.head w) q, K.root⟩) t K) :
    headAtLabel p c E rho (rho.seatOf (.base (.head w)) q) w = some K := by
  have hObserver := he
  obtain ⟨j, _, _, hj, hem, _, _⟩ := he
  have hK := headTargetAtEmission_at_tick E rho hs hObserver hj rfl
  rw [(V2.D.Run.step_tick_eq E rho hj).2] at hem
  obtain ⟨_, ht, _, _⟩ := (fgsa_emits_head E rho _ _ _ w q K.root).mp hem
  subst t
  change (postClock E rho _ (SA.voteTime p.toParams w)).map
    (fun nd => headVote p nd.st w) = some K
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hj]
  exact congrArg some hK.symm

/-- The actual covering HEADs and receiver floor construct the gate geometry. -/
theorem healing_support_gate_geometry (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) {w : Slot} {B : Block} {i : Nat} {y : V}
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K)
    (hFB : Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams w)).fg.F) B) :
    GateReceiptGeometry E rho (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams w)) w B := by
  have hK q hq K t he := hcov _ hq K
    (healing_support_emitted_head E rho hS w q K t he)
  exact ⟨fun q hq _ K he => Gen.Pure.block_preceq_trans hFB (hK q hq K _ he),
    fun q hq _ K he => hK q hq K _ he⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:709–733 (H.2 S1–S3), 02 §5.4:541; plan H-SUPPORT §4 steps 7–8.
DC: INTENTIONAL the covering-batch gate read. If every honest HEAD of label w covers B
and the gate floor is at or below B, the raw confirmation of an honest gate at w covers
B. The per-seat HEADs may differ (`fgsa_gate_batch_premises`); no exact HEAD is needed. -/
theorem healing_support_gate_cover [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    {w : Slot} {B : Block} (hgst : E.t_GST ≤ SA.voteTime p.toParams w)
    (hhor : SA.gateTime p.toParams w ≤ rho.horizon)
    (hcov : ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq B K)
    {j : Nat} {y : V} (ht : IsGateTick p c rho j y w)
    (hScope : SupportGateScope E rho j y w)
    (hFB : Block.Preceq (eraseFG (clockPre p (storeAt p c E rho j y)
      (SA.gateTime p.toParams w)).fg.F) B) :
    ∃ C, SA.Root.confirmationFrom p.toParams
        (eraseFG (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)).fg.F)
        (actView (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w))) w = some C ∧
      Block.Preceq B C := by
  classical
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hDelta := hrec.base.delta
  have hC := hrec.base.cstar
  have hvg : SA.voteTime p.toParams w ≤ SA.gateTime p.toParams w := by
    change 4 * p.Δ * (w : Int) + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvd : SA.voteTime p.toParams w + E.Δ ≤ SA.gateTime p.toParams w := by
    rw [hDelta]
    change 4 * p.Δ * (w : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (w : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hhorv : SA.voteTime p.toParams w ≤ rho.horizon := hvg.trans hhor
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hgst hvd hhor
  have hcovK (q : Fin p.n) (hq : rho.seatOf (.base (.head w)) q ∈ rho.honest) (K : Block)
      (t : Time) (he : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head w)) q)
        (ofHead p ⟨.seat (.head w) q, K.root⟩) t K) : Block.Preceq B K :=
    hcov _ hq K (healing_support_emitted_head (c := c) E rho hS w q K t he)
  have hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho j y) (SA.gateTime p.toParams w)) w B :=
    ⟨fun q hq _ K he => Gen.Pure.block_preceq_trans hFB (hcovK q hq K _ he),
      fun q hq _ K he => hcovK q hq K _ he⟩
  let H : Finset (Fin p.n) := Finset.univ.filter
    (fun k => rho.seatOf (.base (.head w)) k ∈
      joinedHonest p E rho (SA.voteTime p.toParams w))
  have hslot : slotAt p (SA.voteTime p.toParams w) = w := by
    exact (fgsa_postClock_slot (c := c) (rho.stateBefore E 0 y) _).2.symm.trans
      (fgsa_vote_slot (c := c) _ w)
  have hHmem (k : Fin p.n) : k ∈ H ↔
      rho.seatOf (.base (.head w)) k ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head w)) k) w
        (SA.voteTime p.toParams w) := by
    simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
    change rho.seatOf (.base (.head w)) k ∈ rho.honest.filter (fun z =>
      joinedAt p E rho z (slotAt p (SA.voteTime p.toParams w))
        (SA.voteTime p.toParams w)) ↔ _
    simp only [Finset.mem_filter, hslot]
  have hbij : Function.Bijective (fun k : Fin p.n => rho.seatOf (.base (.head w)) k) :=
    hC (.base (.head w)) trivial
  have hHcard : H.card = (joinedHonest p E rho (SA.voteTime p.toParams w)).card := by
    rw [← Finset.card_image_of_injective H hbij.1]
    congr 1
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact Finset.mem_filter.mpr (by
        simpa only [hslot] using (hHmem k).mp hk)
    · intro hz
      obtain ⟨k, rfl⟩ := hbij.2 z
      exact ⟨k, (hHmem k).mpr (by
        change rho.seatOf (.base (.head w)) k ∈ rho.honest.filter (fun z =>
          joinedAt p E rho z (slotAt p (SA.voteTime p.toParams w))
            (SA.voteTime p.toParams w)) at hz
        simpa only [Finset.mem_filter, hslot] using hz), rfl⟩
  have hbatch : Gen.Pure.Batch H.card (Gen.V2.Duty.faulty rho).card :=
    hHcard ▸ hScope.batch
  have receipts := fgsa_gateReceipt_on (hroots := hrec.base.receiptIdealization)
    E rho hE hDelta hC w hSync ht B hgeom hScope.toGateReceiptScope
  have hcover := fgsa_gate_batch_premises_joined E rho hE hC j y w B H hbatch
    (fun k hk hj => (hHmem k).mpr ⟨hk, hj⟩) (by
      intro k hk
      obtain ⟨hq, hj⟩ := (hHmem k).mp hk
      exact receipts.2.2 k hq hj)
  exact fgsa_confirmationFrom_covers_majority p _ _ B w B.root
    (Bool.or_eq_true_iff.mpr (Or.inl hFB)) hcover.1 hcover.2.1 hcover.2.2

end AvailableChain.FGSA.Run
end
