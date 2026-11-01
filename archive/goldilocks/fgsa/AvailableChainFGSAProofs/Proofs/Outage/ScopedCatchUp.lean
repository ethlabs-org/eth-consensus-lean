module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedEarly

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The public W-reader branch names its actual post-E gate and awake suffix.
The regime produces the batch again at that gate, and the enabled guard supplies
the receipt epoch. No batch is inferred at the gate actor's earlier HEAD tick. -/
theorem outage_caught_up_gate_scope [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    {x : V} {t : Time}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t)
    (hOutside : x ∉ coveredNodes p E rho fast b₀) (hhor : t ≤ rho.horizon) :
    ∃ s j, restoredLabel p b₁ + p.k ≤ s ∧ j < timeIdx rho t ∧
      enabledGateAt p c E rho j x s ∧
      BatchReceiptAt p c E rho x s (SA.earlyTime p.toParams s) ∧
      AwakeClosed E x (SA.gateTime p.toParams s) t ∧
      RestartFreeTime rho x (SA.gateTime p.toParams s) t ∧
      V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
        (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) := by
  obtain ⟨hConfirmed, hCovered | ⟨s, j, hEnd, hst, hj, hG, _, hAw, hRF⟩⟩ := hReader
  · exact (hOutside hCovered).elim
  have hLabel : restoredLabel p b₁ + p.k ≤ s := by
    change 4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ ≤
      4 * p.Δ * (s : Int) + 6 * p.Δ at hEnd
    have hlt : ((restoredLabel p b₁ + p.k : Nat) : Int) < (s : Int) + 1 := by
      nlinarith [p.deltaPos]
    dsimp only [Slot] at *
    omega
  have hrs : restoredLabel p b₁ ≤ s := (Nat.le_add_right _ _).trans hLabel
  have hJ := outage_enabled_gate_joined h.pre.base.valid hConfirmed.1 hG
  have hEG : SA.earlyTime p.toParams s < SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hBatch := (outage_continuation_receipt h).2.1 x s hrs
    (hEG.le.trans (hst.trans hhor)) ⟨hConfirmed.1, hJ⟩
  have hEpoch := outage_restored_reader_epoch h.pre.base.valid.toScheduleWellFormed hJ
    (a := SA.voteTime p.toParams s)
    (by change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
        linarith [p.deltaPos]) (fgsa_vote_lt_gate p s)
  exact ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF,
    hEpoch.mono le_rfl (fgsa_idxBefore_mono rho hEG.le)⟩

/-- The finalized branch supplies inclusion at the actual inclusive read.
This branch needs no covering target demand on later HEADs. -/
theorem outage_finalized_continuation_read {x : V} {t : Time} {B : Block}
    (hs : V2.D.ScheduleWellFormed E rho)
    (hBF : Block.Preceq B (F_at p c E rho (timeIdx rho t) x)) :
    Block.Preceq B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  have hFS := fgsaAC_anchor_le_output E rho (timeIdx rho t) x
  have hBS := Gen.Pure.block_preceq_trans hBF hFS
  exact ⟨hBS, outage_continuation_inclusive_read hs hBS
    (Gen.Pure.block_compatible_of_common (Gen.Pure.block_preceq_refl _) hBF)⟩

/-- The actual W gate uses the produced global HEAD invariant. Its batch,
awake suffix and epoch remain explicit; raw result compatibility is produced. -/
theorem outage_caught_up_gate_result_history [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {x : V} {t : Time}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t)
    (hOutside : x ∉ coveredNodes p E rho fast b₀) (hhor : t ≤ rho.horizon) :
    ∃ s j, restoredLabel p b₁ + p.k ≤ s ∧ j < timeIdx rho t ∧
      enabledGateAt p c E rho j x s ∧
      BatchReceiptAt p c E rho x s (SA.earlyTime p.toParams s) ∧
      AwakeClosed E x (SA.gateTime p.toParams s) t ∧
      RestartFreeTime rho x (SA.gateTime p.toParams s) t ∧
      V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
        (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) ∧
      ∀ C, gateResultAt p c E rho j = some (some C) → Block.Compatible C B := by
  obtain ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF, hEpoch⟩ :=
    outage_caught_up_gate_scope h hReader hOutside hhor
  refine ⟨s, j, hLabel, hj, hG, hBatch, hAw, hRF, hEpoch, ?_⟩
  intro C hC
  have hks := p.kLarge
  have hrs : restoredLabel p b₁ < s := by dsimp only [Slot] at *; omega
  exact outage_continuation_result_of_head_history h hReader.1.1 hrs hG hC
    (fun q K hR hK => outage_continuation_scoped_heads h hf origin htsrc hnamed hsrc
      hState hprov hne hc hβ s q K hrs hR hK)

/-- If old S conflicts with B, each lease below S and compatible with B is
also compatible with every compatible result. Thus no such lease vetoes it. -/
theorem outage_conflicting_stable_no_lease_veto {n : Nat}
    (v : GridCO.State n .root) {B C : Block}
    (hBad : ¬ Block.Compatible v.stableRecord B)
    (hBelow : ∀ row ∈ v.obligations, Block.Preceq row.1 v.stableRecord)
    (hRows : ∀ row ∈ v.obligations, Block.Compatible row.1 B)
    (hC : Block.Compatible C B) :
    v.obligations.any (fun row => !Block.compatible row.1 C) = false := by
  apply List.any_eq_false.mpr
  intro row hr
  have hAB : Block.Preceq row.1 B := by
    rcases Bool.or_eq_true_iff.mp (hRows row hr) with hAB | hBA
    · exact hAB
    · exact (hBad (Bool.or_eq_true_iff.mpr
        (Or.inr (block_preceq_trans hBA (hBelow row hr))))).elim
  have hBC : Block.Compatible B C := by
    simpa only [Block.Compatible, block_compatible_comm C B] using hC
  have hAC := block_compatible_of_preceq_compatible hAB hBC
  simp only [show Block.compatible row.1 C = true from hAC, Bool.not_true,
    Bool.false_eq_true, not_false_eq_true]

/-- For a conflicting old S, a compatible result corrects S exactly when
the result is not below old S. A common-ancestor result retains the conflict. -/
theorem outage_conflicting_stable_advance_iff {S B C F : Block}
    (hBad : ¬ Block.Compatible S B) (hC : Block.Compatible C B)
    (hFS : Block.Preceq F S) (hFC : Block.Preceq F C) :
    Block.Compatible (Gen.AC.normalizeOutput F (GridCO.advance S C)) B ↔
      ¬ Block.Preceq C S := by
  unfold GridCO.advance
  change Block.Compatible (Gen.AC.normalizeOutput F (if Block.Preceq C S then S else C)) B ↔
    ¬ Block.Preceq C S
  by_cases hCS : Block.Preceq C S
  · rw [ite_eq_left hCS, Gen.AC.normalizeOutput_def]
    change Block.Compatible (if Block.Preceq F S then S else F) B ↔ ¬ Block.Preceq C S
    rw [ite_eq_left hFS]
    exact iff_of_false hBad (not_not_intro hCS)
  · rw [ite_eq_right hCS, Gen.AC.normalizeOutput_def]
    change Block.Compatible (if Block.Preceq F C then C else F) B ↔ ¬ Block.Preceq C S
    rw [ite_eq_left hFC]
    exact iff_of_true hC hCS

/-- At a fresh joined gate, the residual correction condition is exact.
Compatible live rows remove the veto. Normalization cannot correct an old
conflict while F remains below old S. -/
theorem outage_gateStep_conflicting_stable_iff (st : State p.n) (s : Slot) (B : Block)
    (hinv : CStoreInv p st)
    (hFresh : GridCO.savedGenuine st.base s = none) (hJ : joinedNow p st = true)
    (hFS : Block.Preceq (eraseFG st.fg.F) st.base.stableRecord)
    (hBad : ¬ Block.Compatible st.base.stableRecord B)
    (hBelow : ∀ row ∈ st.base.obligations, Block.Preceq row.1 st.base.stableRecord)
    (hRows : ∀ row ∈ st.base.obligations, Block.Compatible row.1 B)
    (hResults : ∀ C, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
      (actView st) s = some C → Block.Compatible C B) :
    Block.Compatible (gateStep p st s).base.stableRecord B ↔
      ∃ C, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s = some C ∧
        ¬ Block.Preceq C st.base.stableRecord := by
  let Q : State p.n := { onView
    (fun v => SA.Root.gateFrom p.toParams (eraseFG st.fg.F) v s) st with
    fastWrite := st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)] }
  have hStep : (gateStep p st s).base.stableRecord =
      Gen.AC.normalizeOutput (eraseFG st.fg.F) Q.base.stableRecord := by
    unfold gateStep
    rw [hFresh, hJ]
    simp only [Option.isSome_none, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [normalizeS_fields]
    rfl
  rw [hStep]
  cases hRaw : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s with
  | none =>
    have hQ : Q.base.stableRecord = st.base.stableRecord := by
      change (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).stableRecord = _
      unfold SA.Root.gateFrom GridCO.gateFrom
      rw [show GridCO.confirmationFrom p.toParams.engine (eraseFG st.fg.F)
        (actView st) s = none from hRaw]
      rfl
    rw [hQ, Gen.AC.normalizeOutput_def]
    change Block.Compatible (if Block.Preceq (eraseFG st.fg.F) st.base.stableRecord
      then st.base.stableRecord else eraseFG st.fg.F) B ↔ _
    rw [ite_eq_left hFS]
    exact iff_of_false hBad (by rintro ⟨C, hC, _⟩; cases hC)
  | some C =>
    have hC := hResults C hRaw
    have hVeto := outage_conflicting_stable_no_lease_veto (actView st) hBad hBelow hRows hC
    have hQ : Q.base.stableRecord = GridCO.advance st.base.stableRecord C := by
      have he := @gateFrom_eq_writeKeys_fgsa p.toParams p.n
        (eraseFG st.fg.F) (actView st) s C hRaw hVeto
      change SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s = _ at he
      change (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).stableRecord = _
      rw [he]
      exact (writeKeys_keys { actView st with
        goldfishRecord := GridCO.advance (actView st).goldfishRecord C
        genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root
          (actView st) s (some C)
        stableRecord := GridCO.advance (actView st).stableRecord C } _ _
        (SA.releaseThreshold p.toParams) hinv.leaseKeys.1 hinv.leaseKeys.2
        (saGateWriteKeys_level p.toParams (actView st) s C)).2.2.1
    rw [hQ, outage_conflicting_stable_advance_iff hBad hC hFS
      (outageV_result_extends_anchor p.toParams.engine (actView st) _ C s hRaw)]
    constructor
    · intro hCS
      exact ⟨C, rfl, hCS⟩
    · rintro ⟨D, hD, hDS⟩
      cases Option.some.inj hD
      exact hDS

/-- A gate preserves stable compatibility when the old record and its result are compatible. -/
theorem outage_gateStep_stable_compatible (p : Params) (st : State p.n)
    (hinv : CStoreInv p st) (s : Slot) (B : Block)
    (hS : Block.Compatible st.base.stableRecord B)
    (hF : Block.Compatible (eraseFG st.fg.F) B)
    (hC : joinedNow p st = true → ∀ C, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F)
      (actView st) s = some C → Block.Compatible C B) :
    Block.Compatible (gateStep p st s).base.stableRecord B := by
  have norm (q : State p.n) (hQ : Block.Compatible q.base.stableRecord B)
      (hFQ : Block.Compatible (eraseFG q.fg.F) B) :
      Block.Compatible (normalizeS q).base.stableRecord B := by
    rw [normalizeS_fields]
    change Block.Compatible (if Block.preceq (eraseFG q.fg.F) q.base.stableRecord
      then q.base.stableRecord else eraseFG q.fg.F) B
    split <;> assumption
  by_cases hJ : joinedNow p st = true
  swap
  · have hN := Bool.eq_false_iff.mpr hJ
    unfold gateStep
    rw [hN]
    simp only [Bool.not_false, ite_true]
    split <;> exact norm _ hS hF
  let Q : State p.n := { onView
    (fun v => SA.Root.gateFrom p.toParams (eraseFG st.fg.F) v s) st with
    fastWrite := st.fastWrite ++ [(s, fastSet p (eraseFG st.fg.F) (actView st) s)] }
  have hQ : Block.Compatible Q.base.stableRecord B := by
    change Block.Compatible
      (SA.Root.gateFrom p.toParams (eraseFG st.fg.F) (actView st) s).stableRecord B
    rcases (saGate_cases p.toParams (eraseFG st.fg.F) (actView st) s
      hinv.leaseKeys.1 hinv.leaseKeys.2).2.2 with he | ⟨C, hRaw, he⟩
    · rw [he]; exact hS
    · rw [he]
      unfold GridCO.advance
      split
      · exact hS
      · exact hC hJ C hRaw
  unfold gateStep
  rw [hJ]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  change Block.Compatible
    (normalizeS (if (GridCO.savedGenuine st.base s).isSome then st else Q)).base.stableRecord B
  split
  · exact norm st hS hF
  · exact norm Q hQ hF

/-- The local inclusive suffix needs only compatible enabled results and current F.
It includes restart and same-time delivery events. -/
theorem outage_stable_compatible_suffix
    (hBase : Base₂ p c E rho) {x : V} {B : Block} {s : Slot} {j I : Nat}
    (_hG : enabledGateAt p c E rho j x s) (hjI : j < I)
    (hSeed : Block.Compatible (S_at p c E rho (j + 1) x) B)
    (hF : ∀ i, j + 1 ≤ i → i ≤ I → Block.Compatible (F_at p c E rho i x) B)
    (hResults : ∀ i q C, j < i → i < I → enabledGateAt p c E rho i x q →
      gateResultAt p c E rho i = some (some C) → Block.Compatible C B) :
    Block.Compatible (S_at p c E rho I x) B := by
  have hs := hBase.valid.toScheduleWellFormed
  have suff : ∀ i, j + 1 ≤ i → i ≤ I → Block.Compatible (S_at p c E rho i x) B := by
    intro i hji
    induction i, hji using Nat.le_induction with
    | base => intro _; exact hSeed
    | succ i hji ih =>
      intro hi
      have hiI : i < I := by omega
      have hSi := ih hiI.le
      rcases fgsaAC_output_step E rho i x with he | ⟨q, ht⟩ |
          ⟨o, t, b, _, _, _, hn⟩ | ⟨t, hr, _⟩
      · change S_at p c E rho (i + 1) x = S_at p c E rho i x at he
        rw [he]; exact hSi
      · have post : storeAt p c E rho (i + 1) x =
            clock p (storeAt p c E rho i x) (SA.gateTime p.toParams q) := by
          change (rho.stateBefore E (i + 1) x).st = _
          rw [(rho.step_tick_eq E ht).1]
          exact tick_st (c := c) E rho _ x _
        change Block.Compatible (storeAt p c E rho (i + 1) x).base.stableRecord B
        rw [post, arming_clock_gate]
        apply outage_gateStep_stable_compatible p _
          (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho i x) _) q B
        · rw [clockPre_stable]; exact hSi
        · rw [clockPre_fg]; exact hF i hji hiI.le
        · intro hJ C hC
          have hguard : joinedAtTime p (storeAt p c E rho i x).restartTime
              (SA.gateTime p.toParams q) = true := by
            rw [clockPre_joined] at hJ
            exact hJ
          have hslot : p.slotOf (SA.gateTime p.toParams q) = q + 1 :=
            (fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
              (fgsa_gate_slot (c := c) (rho.stateBefore E i x) q)
          have hEnabled : enabledGateAt p c E rho i x q := by
            refine ⟨ht, ?_⟩
            cases hr : (storeAt p c E rho i x).restartTime with
            | none => trivial
            | some w =>
              simp only [joinedAtTime, hr, hslot, Nat.cast_add, Nat.cast_one,
                add_sub_cancel_right, decide_eq_true_eq] at hguard
              exact hguard
          exact hResults i q C (by omega) hiI hEnabled
            ((inclusion_gate_raw_at_tick E rho hs hEnabled).trans (congrArg some hC))
      · change S_at p c E rho (i + 1) x =
          Gen.AC.normalizeOutput (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hn
        rw [hn, Gen.AC.normalizeOutput_def]
        split
        · exact hSi
        · exact hF (i + 1) (by omega) hi
      · change Block.Compatible (storeAt p c E rho (i + 1) x).base.stableRecord B
        have post : storeAt p c E rho (i + 1) x = acRestart p (storeAt p c E rho i x) t := by
          change (rho.stateBefore E (i + 1) x).st = _
          rw [V2.D.Engine.state_after_restart hr]; rfl
        rw [post, acRestart_stableRecord]
        exact hSi
  exact suff I (Nat.succ_le_of_lt hjI) le_rfl

/-- O11-W-READ carries the actual post-gate seed to the inclusive public read.
The global producer supplies all later enabled results and durable F compatibility. -/
theorem outage_caught_up_public_read_from_seed [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {x : V} {t : Time} {s : Slot} {j : Nat}
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t)
    (_hhor : t ≤ rho.horizon) (hLabel : restoredLabel p b₁ + p.k ≤ s)
    (hj : j < timeIdx rho t) (hG : enabledGateAt p c E rho j x s)
    (hSeed : Block.Compatible B (S_at p c E rho (j + 1) x)) :
    Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hrs : restoredLabel p b₁ < s := by
    have := p.kLarge; dsimp only [Slot] at *; omega
  have hEarly : SA.earlyTime p.toParams (restoredLabel p b₁) <
      SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]
    have hc := Int.ofNat_le.mpr hrs.le
    nlinarith [p.deltaPos]
  have hGateHor := (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hHor := hEarly.le.trans hGateHor
  have hStart : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ j :=
    le_of_not_gt (fun hn => (not_lt_of_ge (arming_tick_le hs hG.1
      (hn.trans_le (preIdx_le_afterTicksIdx E rho hs _).2))) hEarly)
  have state {i : Nat} (hi : j ≤ i) (hlen : i ≤ rho.events.length) :=
    outage_continuation_event_state h hf origin htsrc hnamed hsrc hState hprov hne hc hβ
      hHor (hStart.trans hi) hlen
  have hLen : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
  have current := state hj.le hLen
  have hS := outage_stable_compatible_suffix h.pre.base hG hj
    (Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp hSeed)))
    (fun i hji hi => (state (by omega) (hi.trans hLen)).2.2.2.1 x hReader.1.1)
    (by
      intro i q C hji hi hEnabled hC
      have htime : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams q := by
        apply le_of_not_gt
        intro hn
        have hij := V2.D.Engine.eventIndex_lt_of_time_lt hs hEnabled.1 hG.1 hn
        omega
      have hsq : s ≤ q := (arming_gate_le_iff p s q).mp htime
      exact current.1 i x q C hi hReader.1.1 (hrs.trans_le hsq) hEnabled hC)
  have hStable : V2.D.outputAt E rho (fgsaInterface p c).stable x t =
      S_at p c E rho (timeIdx rho t) x := arming_stable_read hs x t
  have hConfirmed : V2.D.outputAt E rho (fgsaInterface p c).confirmed x t =
      S_at p c E rho (timeIdx rho t) x := arming_stable_read hs x t
  have symm (A : Block) (h : Block.Compatible A B) : Block.Compatible B A :=
    Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp h))
  exact ⟨symm _ hS, hStable.symm ▸ symm _ hS, hConfirmed.symm ▸ symm _ hS,
    symm _ (current.2.2.2.1 x hReader.1.1)⟩

/-- At each actual post-E enabled gate, every live row is compatible with B.
An incompatible old write cannot survive its handover deadline. This proves the
live-row input for a repairing gate; it does not assert that a repair occurs. -/
theorem outage_caught_up_gate_rows [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {x : V} {s : Slot} {j : Nat}
    (hLabel : restoredLabel p b₁ + p.k ≤ s) (hG : enabledGateAt p c E rho j x s) :
    ∀ row ∈ (clockPre p (storeAt p c E rho j x)
      (SA.gateTime p.toParams s)).base.obligations, Block.Compatible row.1 B := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hx := hs.honest_only _ (List.mem_of_getElem? hG.1)
  have hrs : restoredLabel p b₁ < s := by
    have := p.kLarge; dsimp only [Slot] at *; omega
  have hEarly : SA.earlyTime p.toParams (restoredLabel p b₁) <
      SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]
    have hc := Int.ofNat_le.mpr hrs.le
    nlinarith [p.deltaPos]
  have hGateHor := (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hStart : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ j :=
    le_of_not_gt (fun hn => (not_lt_of_ge (arming_tick_le hs hG.1
      (hn.trans_le (preIdx_le_afterTicksIdx E rho hs _).2))) hEarly)
  have state := outage_continuation_event_state h hf origin htsrc hnamed hsrc hState hprov
    hne hc hβ (hEarly.le.trans hGateHor) hStart
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hG.1).1)
  have hEnd : OutageEnd p (restoredLabel p b₁) ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ ≤
      4 * p.Δ * (s : Int) + 6 * p.Δ
    have hcast := Int.ofNat_le.mpr hLabel
    nlinarith [p.deltaPos]
  intro row hr
  by_contra hn
  have hd := outage_conflicting_row_deadline hs (restoredLabel p b₁) B j x
    (fun k q C hk hq hEnabled hC => state.1 k x q C hk hx hq hEnabled hC)
    row ((clockPre_obligations_sublist p _ _).subset hr) hn
  have hl : SA.gateTime p.toParams s < row.2.2 :=
    of_decide_eq_true (List.mem_filter.mp (outage_clockPre_expired_rows _ _ hr)).2
  exact (not_lt_of_ge (hd.trans hEnd)) hl

/-- At the actual W gate, all existing producers reduce the conflicting-S
branch to a genuine result that is not below old S. No correction is assumed. -/
theorem outage_caught_up_gate_seed_iff [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {x : V} {s : Slot} {j : Nat}
    (hLabel : restoredLabel p b₁ + p.k ≤ s) (hG : enabledGateAt p c E rho j x s)
    (hBad : ¬ Block.Compatible (S_at p c E rho j x) B) :
    Block.Compatible B (S_at p c E rho (j + 1) x) ↔
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        ¬ Block.Preceq C (S_at p c E rho j x) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hx := hs.honest_only _ (List.mem_of_getElem? hG.1)
  let P := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
  have hRows := outage_caught_up_gate_rows h hf origin htsrc hnamed hsrc hState hprov
    hne hc hβ hLabel hG
  have hBelow : ∀ row ∈ P.base.obligations, Block.Preceq row.1 P.base.stableRecord := by
    intro row hr
    have hLive : SA.gateTime p.toParams s < row.2.2 :=
      of_decide_eq_true (List.mem_filter.mp (outage_clockPre_expired_rows _ _ hr)).2
    have hb := leaseBelowOutput_stateBefore E rho j x row
      ((clockPre_obligations_sublist p _ _).subset hr)
      ((fgsa_preTick_now_le E rho hs hG.1).trans_lt hLive)
    simpa only [P, clockPre_stable, storeAt] using hb
  have hRaw := inclusion_gate_raw_at_tick E rho hs hG
  have hFresh : GridCO.savedGenuine P.base s = none := by
    rw [savedGenuine_congr (clockPre_genuine p _ _) s]
    exact fgsa_gate_fresh E rho hs hG.1
  have hJoined : joinedNow p P = true := by
    rw [clockPre_joined]
    exact fgsa_gate_joined_of_enabled E rho hG
  have hFS : Block.Preceq (eraseFG P.fg.F) P.base.stableRecord := by
    have hn := nestOK_stateBefore E rho j x
    change Block.Preceq (eraseFG (rho.stateBefore E j x).st.fg.F)
      (rho.stateBefore E j x).st.base.stableRecord at hn
    simpa only [P, clockPre_fg, clockPre_stable, storeAt] using hn
  have hBadP : ¬ Block.Compatible P.base.stableRecord B := by
    simpa only [P, clockPre_stable, S_at_def] using hBad
  have hIff := outage_gateStep_conflicting_stable_iff P s B
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x) _) hFresh hJoined hFS
    hBadP hBelow hRows (by
      intro C hC
      have hrs : restoredLabel p b₁ < s := by
        have := p.kLarge; dsimp only [Slot] at *; omega
      exact outage_continuation_result_of_head_history h hx hrs hG
        (hRaw.trans (congrArg some hC))
        (fun q K hR hK => outage_continuation_scoped_heads h hf origin htsrc hnamed hsrc
          hState hprov hne hc hβ s q K hrs hR hK))
  have hPost : S_at p c E rho (j + 1) x = (gateStep p P s).base.stableRecord := by
    have post : storeAt p c E rho (j + 1) x =
        clock p (storeAt p c E rho j x) (SA.gateTime p.toParams s) := by
      change (rho.stateBefore E (j + 1) x).st = _
      rw [(rho.step_tick_eq E hG.1).1]
      exact tick_st (c := c) E rho _ x _
    rw [S_at_def, post, arming_clock_gate]
  rw [hPost]
  change Block.compatible B _ = true ↔ _
  rw [block_compatible_comm]
  refine hIff.trans ?_
  apply exists_congr
  intro C
  dsimp only [P]
  rw [clockPre_stable]
  exact and_congr (by
    rw [hRaw]
    exact ⟨congrArg some, Option.some.inj⟩) Iff.rfl

/-- The gate named by repair readiness supplies a compatible post-gate S.
Freshness, compatible results and live rows are proved at this exact witness. -/
theorem outage_repair_gate_seed [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {x : V} {s : Slot} {j : Nat}
    (hLabel : restoredLabel p b₁ + p.k ≤ s) (hG : enabledGateAt p c E rho j x s)
    (hReady :
      let st := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
      Block.Compatible B st.base.stableRecord ∨
        ∃ C, SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s = some C ∧
          ¬ Block.Preceq C st.base.stableRecord) :
    Block.Compatible B (S_at p c E rho (j + 1) x) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  let P := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)
  have hRaw := inclusion_gate_raw_at_tick E rho hs hG
  by_cases hBad : ¬ Block.Compatible (S_at p c E rho j x) B
  · apply (outage_caught_up_gate_seed_iff h hf origin htsrc hnamed hsrc hState hprov
      hne hc hβ hLabel hG hBad).mpr
    rcases hReady with hOld | ⟨C, hC, hCS⟩
    · exact (hBad (by
        simpa only [clockPre_stable, S_at_def, Block.Compatible, block_compatible_comm]
          using hOld)).elim
    · refine ⟨C, hRaw.trans (congrArg some hC), ?_⟩
      simpa only [clockPre_stable, S_at_def] using hCS
  have hOld : Block.Compatible P.base.stableRecord B := by
    simpa only [P, clockPre_stable, S_at_def] using not_not.mp hBad
  have hrs : restoredLabel p b₁ < s := by
    have := p.kLarge; dsimp only [Slot] at *; omega
  have hEarly : SA.earlyTime p.toParams (restoredLabel p b₁) <
      SA.gateTime p.toParams s := by
    rw [arming_early_eq, arming_gate_eq]
    have hc := Int.ofNat_le.mpr hrs.le
    nlinarith [p.deltaPos]
  have hHor := hEarly.le.trans (hs.in_horizon _ (List.mem_of_getElem? hG.1)).2
  have hStart : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ j :=
    le_of_not_gt (fun hn => (not_lt_of_ge (arming_tick_le hs hG.1
      (hn.trans_le (preIdx_le_afterTicksIdx E rho hs _).2))) hEarly)
  have current := outage_continuation_event_state h hf origin htsrc hnamed hsrc hState
    hprov hne hc hβ hHor hStart
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hG.1).1)
  have hx := hs.honest_only _ (List.mem_of_getElem? hG.1)
  have hF : Block.Compatible (eraseFG P.fg.F) B := by
    dsimp only [P]
    rw [clockPre_fg]
    exact current.2.2.2.1 x hx
  have hPost : S_at p c E rho (j + 1) x = (gateStep p P s).base.stableRecord := by
    have post : storeAt p c E rho (j + 1) x =
        clock p (storeAt p c E rho j x) (SA.gateTime p.toParams s) := by
      change (rho.stateBefore E (j + 1) x).st = _
      rw [(rho.step_tick_eq E hG.1).1]
      exact tick_st (c := c) E rho _ x _
    rw [S_at_def, post, arming_clock_gate]
  rw [hPost]
  change Block.compatible B _ = true
  rw [block_compatible_comm]
  apply outage_gateStep_stable_compatible p P
    (cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x) _) s B hOld hF
  intro _ C hC
  exact outage_continuation_result_of_head_history h hx hrs hG
    (hRaw.trans (congrArg some hC))
    (fun q K hR hK => outage_continuation_scoped_heads h hf origin htsrc hnamed hsrc
      hState hprov hne hc hβ s q K hrs hR hK)

/-- Join covered inclusion, finality inclusion and the qualified repair-gate suffix. -/
theorem outage_continuation_public_reads [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y)) :
    ∀ x t, b₀ ≤ t → t ≤ rho.horizon →
      outageConfirmedReader p c E rho fast b₀ b₁ x t →
      OutageRepairReady p c E rho fast b₀ b₁ B x t →
      Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      (x ∈ coveredNodes p E rho fast b₀ →
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x) ∧
        Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
        Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t)) := by
  classical
  intro x t hb hhor hReader hReady
  have hs := h.pre.base.valid.toScheduleWellFormed
  by_cases hEarly : t < SA.earlyTime p.toParams (restoredLabel p b₁)
  · exact outage_early_public_read h hf htsrc hnamed hsrc hState hprov hne hc hβ
      hHist hOutput hb hhor hEarly hReader
  have ht := le_of_not_gt hEarly
  by_cases hxG : x ∈ coveredNodes p E rho fast b₀
  · obtain ⟨hStable, hConfirmed, _⟩ := outage_covered_public_read_after_seed h hf origin
      htsrc hnamed hsrc hState hprov hne hc hβ hxG ht hhor
    have hS : Block.Preceq B (S_at p c E rho (timeIdx rho t) x) := by
      rwa [arming_stable_read hs] at hStable
    exact ⟨block_compatible_of_common hS (block_preceq_refl _),
      block_compatible_of_common hStable (block_preceq_refl _),
      block_compatible_of_common hConfirmed (block_preceq_refl _),
      fun _ => ⟨hS, hStable, hConfirmed⟩⟩
  have hRead : Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) := by
    rcases hReady with hx | hBF | ⟨s, j, hLabel, hj, hG, hRepair⟩
    · exact (hxG hx).elim
    · obtain ⟨hS, hStable, hConfirmed, _⟩ := outage_finalized_continuation_read hs hBF
      exact ⟨block_compatible_of_common hS (block_preceq_refl _),
        block_compatible_of_common hStable (block_preceq_refl _),
        block_compatible_of_common hConfirmed (block_preceq_refl _)⟩
    · have hSeed := outage_repair_gate_seed h hf origin htsrc hnamed hsrc hState hprov
        hne hc hβ hLabel hG hRepair
      obtain ⟨hS, hStable, hConfirmed, _⟩ := outage_caught_up_public_read_from_seed h hf origin
        htsrc hnamed hsrc hState hprov hne hc hβ hReader hhor hLabel hj hG hSeed
      exact ⟨hS, hStable, hConfirmed⟩
  exact ⟨hRead.1, hRead.2.1, hRead.2.2, fun hx => (hxG hx).elim⟩

/-- The complete scoped HEAD and F consumers have no continuation callback.
Early labels use covered duty history; later labels use ScopedBridge's global producer. -/
theorem outage_continuation_public_heads_and_finality [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
 :
    (∀ y t o H, b₀ ≤ t → t ≤ rho.horizon →
      outageHeadReader p E rho fast b₀ b₁ y t →
      V2.D.Run.emits E rho y o t → HeadTargetAtEmission p c E rho y o t H →
      Block.Compatible B H) ∧
    (∀ y t, y ∈ rho.honest → b₀ ≤ t → t ≤ rho.horizon →
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y)) := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  have symm (A : Block) (h : Block.Compatible A B) : Block.Compatible B A :=
    Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp h))
  constructor
  · intro y t o H hb hhor hReader hem hTarget
    have hKeep := hTarget
    obtain ⟨i, s, q, hi, hm, ho, _⟩ := hTarget
    have hm' := hm
    rw [ho, (rho.step_tick_eq E hi).2] at hm'
    have hFields := (fgsa_emits_head E rho _ y t s q H.root).mp hm'
    have ht : t = SA.voteTime p.toParams s := hFields.2.1.symm
    have hy : y = rho.seatOf (.base (.head s)) q := hFields.2.2.1.symm
    subst t; subst y
    have hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, H.root⟩) (SA.voteTime p.toParams s) H := by
      rwa [ho] at hKeep
    by_cases hsr : s ≤ restoredLabel p b₁
    · have hBH := outage_early_scoped_head h hf htsrc hnamed hsrc hState hprov hne hc hβ
        hsr hb hhor hReader hK
      exact block_compatible_of_common hBH (block_preceq_refl _)
    · exact symm H (outage_continuation_scoped_heads h hf origin htsrc hnamed hsrc
        hState hprov hne hc hβ s q H (Nat.lt_of_not_ge hsr) hReader hK)
  · intro y t hy hb hhor
    by_cases hEarly : t < SA.earlyTime p.toParams (restoredLabel p b₁)
    · exact outage_early_finalized_read h hf htsrc hnamed hsrc hState hprov hne hc hβ
        hy hb hhor hEarly
    have ht := le_of_not_gt hEarly
    have hI : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤
        timeIdx rho t := (preIdx_le_afterTicksIdx E rho hs _).2.trans
          (arming_timeIdx_mono rho ht)
    exact symm _ ((outage_continuation_event_state h hf origin htsrc hnamed hsrc hState
      hprov hne hc hβ (ht.trans hhor) hI (List.length_filter_le _ _)).2.2.2.1 y hy)

end AvailableChain.FGSA.Run
end
