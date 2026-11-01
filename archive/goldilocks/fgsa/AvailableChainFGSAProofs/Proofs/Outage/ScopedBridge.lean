module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedPaths

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- An early marker also protects later actual scoped HEADs before handover.
The causal state supplies their live rows rather than an expiry restriction. -/
theorem outage_marker_head_on_scoped_prefix [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) {B P : FGBlock (Fin p.n)}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ (eraseFG B) l D Dh)
    {k i : Nat} {y x : V} {m s : Slot}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m)))
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hy : y ∈ rho.honest)
    (hReader : outageHeadReader p E rho fast b₀ b₁ x (SA.voteTime p.toParams s))
    (hrm : restoredLabel p b₁ ≤ m) (hms : m < s)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF)
    (hBJ : FGBlock.Preceq B (heightView p P).J) (hnz : (heightView p P).h_j ≠ 0)
    (hNames : OutageNamedHistory p c E rho B i)
    (hCover : x ∈ coveredNodes p E rho fast b₀ →
      Block.Preceq (eraseFG B) (S_at p c E rho i x))
    (hResults : ∀ j q C, j < i → restoredLabel p b₁ < q →
      enabledGateAt p c E rho j x q → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C (eraseFG B)) :
    Block.Compatible (headVote p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s)) s) (eraseFG B) := by
  have heq : s - 1 + 1 = s := Nat.sub_add_cancel
    (by dsimp only [Slot] at *; omega)
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have := p.deltaPos; dsimp [Time] at *; omega)
  have hJ : joinedAt p E rho x s (SA.voteTime p.toParams s) := by
    simpa only [hslot] using hReader.1.2
  have hLocks := outage_scoped_head_rows h hc hi hReader hCover hResults
  have hHead := outage_later_marker_head h.pre.base h.sync hf hk
    (heq.symm ▸ hi) hy hReader.1.1 (heq.symm ▸ hJ)
    (show m ≤ s - 1 by dsimp only [Slot] at *; omega)
    (h.gst.trans (outage_restored_vote_cut p b₁ hrm)) hP hBJ hnz hNames
    (by
      intro row hr hl
      apply hLocks row (by simpa only [heq] using hr)
      rw [(clock_vn _ _).2]
      simpa only [heq] using hl)
  simpa only [heq] using hHead

/-- The finite continuation is produced from the first-label marker. All reads
at that label use their own contested frame; later reads use marker receipt.
No restored result, future HEAD, source seed or all-honest stable seed is an input. -/
theorem outage_regression_continuation [Fintype V]
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
    {k : Nat} {m : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k m)
    (hNo : ∀ j q, q < m → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q)
    {i : Nat}
    (hI : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ i)
    (hi : i ≤ rho.events.length) :
    (∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) ∧
    OutageSourceHistory p c E rho B i ∧ OutageNamedHistory p c E rho β i ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho i x) B) ∧
      ∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho i x) := by
  classical
  subst B
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hrm := hReg.1
  obtain ⟨y, P, hk, hy, _, hP, hBJ, hnz, _⟩ := outage_regression_marker_no_lower h hf
    origin htsrc hnamed hsrc hState hprov hne hc rfl hReg hNo
  have hHor : SA.earlyTime p.toParams (restoredLabel p b₁) ≤ rho.horizon := by
    have hbound : SA.voteTime p.toParams m ≤ rho.horizon :=
      (hs.in_horizon _ (List.mem_of_getElem? hk)).2
    apply le_trans _ hbound
    rw [arming_early_eq, arming_vote_eq]
    have hcast := Int.ofNat_le.mpr (Nat.succ_le_of_lt hrm)
    push_cast at hcast; nlinarith [p.deltaPos]
  let I := afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁))
  have state {a : Nat} (hIa : I ≤ a) (ha : a ≤ rho.events.length)
      (hResults : ∀ j x s C, j < a → x ∈ rho.honest → restoredLabel p b₁ < s →
        enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
        Block.Compatible C (eraseFG β)) :=
    outage_continuation_of_results h hf htsrc hnamed hsrc hState hprov hne hc rfl
      hHor hIa ha hResults
  have hAll : ∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C (eraseFG β) := by
    induction i, hI using Nat.le_induction with
    | base =>
      intro j x s C hj _ hrs hG _
      have hTime := arming_tick_le hs hG.1
        (hj.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)
      change SA.gateTime p.toParams s ≤ SA.earlyTime p.toParams (restoredLabel p b₁) at hTime
      rw [arming_gate_eq, arming_early_eq] at hTime
      have hcast := Int.ofNat_lt.mpr hrs
      nlinarith [p.deltaPos]
    | succ n hIn ih =>
      have hn : n < rho.events.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hi
      have hResults := ih (Nat.le_of_lt hn)
      intro j x s C hj hx hrs hG hC
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjn | rfl
      · exact hResults j x s C hjn hx hrs hG hC
      apply outage_continuation_result_of_head_history h hx hrs hG hC
      intro q K hReader hK
      have hKeep := hK
      obtain ⟨a, _, _, ha, _, _, _⟩ := hK
      have han := V2.D.Engine.eventIndex_lt_of_time_lt hs ha hG.1 (fgsa_vote_lt_gate p s)
      rcases lt_trichotomy s m with hsm | he | hms
      · apply Bool.or_eq_true_iff.mpr
        right
        by_contra hBad
        exact hNo a s hsm ⟨hrs, q, K, ha, hReader, hKeep, hBad⟩
      · subst s
        by_cases hBK : Block.Preceq (eraseFG β) K
        · exact Bool.or_eq_true_iff.mpr (Or.inr hBK)
        have hLocal : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
            fast b₀ b₁ (eraseFG β) a m := ⟨hrs, q, K, ha, hReader, hKeep, hBK⟩
        obtain ⟨z, _, hz, _, _, _, _, _, hHead⟩ := outage_regression_marker_no_lower h hf
          origin htsrc hnamed hsrc hState hprov hne hc rfl hLocal hNo
        have hzx : z = rho.seatOf (.base (.head m)) q :=
          (V2.Event.tick.inj (Option.some.inj (hz.symm.trans ha))).1
        subst z
        exact (headTargetAtEmission_at_tick E rho hs hKeep ha rfl).symm ▸ hHead
      · have hEV : SA.earlyTime p.toParams (restoredLabel p b₁) <
            SA.voteTime p.toParams s := by
          rw [arming_early_eq, arming_vote_eq]
          have hcast := Int.ofNat_le.mpr (Nat.succ_le_of_lt hrs)
          push_cast at hcast; nlinarith [p.deltaPos]
        have hIdx : rho.idxBefore (SA.voteTime p.toParams s) ≤ a := by
          apply Nat.le_of_not_gt
          intro hlt
          exact (lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs ha _).mp hlt)).elim
        have hIa : I ≤ a := ((preIdx_le_afterTicksIdx E rho hs _).2.trans
          (arming_timeIdx_le_idxBefore rho hEV)).trans hIdx
        have hStateA := state hIa (Nat.le_of_lt (han.trans hn))
          (fun j x s C hj hx hrs hG hC => hResults j x s C (hj.trans han) hx hrs hG hC)
        have hHead := outage_marker_head_on_scoped_prefix h hf hc hk ha hy hReader
          hrm.le hms hP hBJ hnz hStateA.2.2.1 (hStateA.2.2.2.2 _)
          (fun j s C hj => hResults j _ s C (hj.trans han) hReader.1.1)
        exact (headTargetAtEmission_at_tick E rho hs hKeep ha rfl).symm ▸ hHead
  exact state hI hi hAll

/-- The no-marker branch, first-label reads and causal marker continuation
produce all restored actual scoped HEAD compatibility. -/
theorem outage_continuation_scoped_heads [Fintype V]
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
    ∀ s q K, restoredLabel p b₁ < s →
      outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
        (SA.voteTime p.toParams s) →
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
      Block.Compatible K B := by
  classical
  subst B
  rcases outage_first_scoped_regression_event (p := p) (c := c) (E := E) (rho := rho)
      (fast := fast) (b₀ := b₀) (b₁ := b₁) (B := eraseFG β) with hNo | ⟨k, m, hReg, hFirst⟩
  · intro s q K hrs hReader hK
    have hKeep := hK
    obtain ⟨a, _, _, ha, _, _, _⟩ := hK
    apply Bool.or_eq_true_iff.mpr
    right
    by_contra hBad
    exact hNo a s ⟨hrs, q, K, ha, hReader, hKeep, hBad⟩
  · have hs := h.pre.base.valid.toScheduleWellFormed
    have hNo := outage_no_lower_of_first_event hs hReg hFirst
    obtain ⟨y, P, hk, hy, _, hP, hBJ, hnz, _⟩ := outage_regression_marker_no_lower h hf
      origin htsrc hnamed hsrc hState hprov hne hc rfl hReg hNo
    intro s q K hrs hReader hK
    have hKeep := hK
    obtain ⟨a, _, _, ha, _, _, _⟩ := hK
    rcases lt_trichotomy s m with hsm | he | hms
    · apply Bool.or_eq_true_iff.mpr
      right
      by_contra hBad
      exact hNo a s hsm ⟨hrs, q, K, ha, hReader, hKeep, hBad⟩
    · subst s
      by_cases hBK : Block.Preceq (eraseFG β) K
      · exact Bool.or_eq_true_iff.mpr (Or.inr hBK)
      have hLocal : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
          fast b₀ b₁ (eraseFG β) a m := ⟨hrs, q, K, ha, hReader, hKeep, hBK⟩
      obtain ⟨z, _, hz, _, _, _, _, _, hHead⟩ := outage_regression_marker_no_lower h hf
        origin htsrc hnamed hsrc hState hprov hne hc rfl hLocal hNo
      have hzx : z = rho.seatOf (.base (.head m)) q :=
        (V2.Event.tick.inj (Option.some.inj (hz.symm.trans ha))).1
      subst z
      exact (headTargetAtEmission_at_tick E rho hs hKeep ha rfl).symm ▸ hHead
    · have hEV : SA.earlyTime p.toParams (restoredLabel p b₁) <
          SA.voteTime p.toParams s := by
        rw [arming_early_eq, arming_vote_eq]
        have hcast := Int.ofNat_le.mpr (Nat.succ_le_of_lt hrs)
        push_cast at hcast; nlinarith [p.deltaPos]
      have hIdx : rho.idxBefore (SA.voteTime p.toParams s) ≤ a := by
        apply Nat.le_of_not_gt
        intro hlt
        exact (lt_irrefl _ ((Gen.V2.Duty.index_lt_idxBefore_iff hs ha _).mp hlt)).elim
      have hIa : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ a :=
        ((preIdx_le_afterTicksIdx E rho hs _).2.trans
          (arming_timeIdx_le_idxBefore rho hEV)).trans hIdx
      have hStateA := outage_regression_continuation h hf origin htsrc hnamed hsrc hState
        hprov hne hc rfl hReg hNo hIa (Nat.le_of_lt (List.getElem?_eq_some_iff.mp ha).1)
      have hHead := outage_marker_head_on_scoped_prefix h hf hc hk ha hy hReader
        hReg.1.le hms hP hBJ hnz hStateA.2.2.1 (hStateA.2.2.2.2 _)
        (fun j s C hj => hStateA.1 j _ s C hj hReader.1.1)
      exact (headTargetAtEmission_at_tick E rho hs hKeep ha rfl).symm ▸ hHead

/-- The exact finite prefix requested by the marker suffix is produced.
The cut is after gate max(m,r+k), including markers before handover. -/
theorem outage_first_marker_finite_prefix [Fintype V]
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
    {k : Nat} {m : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k m)
    (hFirst : ∀ j, j < k → ∀ q, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    let I := afterTicksIdx rho (SA.gateTime p.toParams (max m (restoredLabel p b₁ + p.k)))
    OutageSourceHistory p c E rho B I ∧
      (∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho I x)) ∧
      ∀ j x s C, j < I → x ∈ rho.honest → restoredLabel p b₁ < s →
        enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
        Block.Compatible C B := by
  intro I
  have hTime : SA.earlyTime p.toParams (restoredLabel p b₁) ≤
      SA.gateTime p.toParams (max m (restoredLabel p b₁ + p.k)) := by
    rw [arming_early_eq, arming_gate_eq]
    have hlabel := hReg.1.le.trans (le_max_left m (restoredLabel p b₁ + p.k))
    have hcast := Int.ofNat_le.mpr hlabel
    nlinarith [p.deltaPos]
  have hLength : I ≤ rho.events.length := List.length_filter_le _ _
  obtain ⟨hResults, hSource, _, _, hCover⟩ := outage_regression_continuation h hf origin
    htsrc hnamed hsrc hState hprov hne hc hβ hReg
    (outage_no_lower_of_first_event h.pre.base.valid.toScheduleWellFormed hReg hFirst)
    (afterTicksIdx_mono rho hTime) hLength
  exact ⟨hSource, hCover, hResults⟩

/-- Both first-event branches supply the actual bounded event state. -/
theorem outage_continuation_event_state [Fintype V]
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
    (hHor : SA.earlyTime p.toParams (restoredLabel p b₁) ≤ rho.horizon)
    {i : Nat}
    (hI : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ i)
    (hi : i ≤ rho.events.length) :
    (∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) ∧
    OutageSourceHistory p c E rho B i ∧ OutageNamedHistory p c E rho β i ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho i x) B) ∧
      ∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho i x) := by
  rcases outage_first_scoped_regression_event (p := p) (c := c) (E := E) (rho := rho)
      (fast := fast) (b₀ := b₀) (b₁ := b₁) (B := B) with hNo | ⟨k, m, hReg, hFirst⟩
  · exact outage_no_regression_continuation h hf htsrc hnamed hsrc hState hprov hne hc hβ
      hHor hI hi (fun k s _ => hNo k s)
  · exact outage_regression_continuation h hf origin htsrc hnamed hsrc hState hprov hne hc hβ
      hReg (outage_no_lower_of_first_event h.pre.base.valid.toScheduleWellFormed hReg hFirst)
      hI hi

/-- The produced event state reaches both inclusive public outputs after the
restored seed. Only covered readers request inclusion. -/
theorem outage_covered_public_read_after_seed [Fintype V]
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
    {x : V} {t : Time} (hx : x ∈ coveredNodes p E rho fast b₀)
    (ht : SA.earlyTime p.toParams (restoredLabel p b₁) ≤ t)
    (hhor : t ≤ rho.horizon) :
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  classical
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hI : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤
      timeIdx rho t := (preIdx_le_afterTicksIdx E rho hs _).2.trans (arming_timeIdx_mono rho ht)
  have hi : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
  obtain ⟨_, _, _, hF, hS⟩ := outage_continuation_event_state h hf origin htsrc hnamed hsrc
    hState hprov hne hc hβ (ht.trans hhor) hI hi
  exact outage_continuation_inclusive_read hs (hS x hx) (hF x (Finset.mem_filter.mp hx).1)

end AvailableChain.FGSA.Run
end
