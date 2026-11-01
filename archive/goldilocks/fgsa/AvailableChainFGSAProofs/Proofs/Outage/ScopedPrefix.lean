module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedScores

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A regression is an actual emitted HEAD at a scoped joined read.
It is not a deterministic HEAD computation at a suppressed tick. -/
@[expose] def OutageScopedRegression (fast : Bool) (b₀ b₁ : Time) (B : Block)
    (k : Nat) (s : Slot) : Prop :=
  restoredLabel p b₁ < s ∧ ∃ q K,
    rho.events[k]? = some
      (.tick (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s)) ∧
    outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
      (SA.voteTime p.toParams s) ∧
    HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K ∧
    ¬ Block.Preceq B K

theorem OutageScopedRegression_def (fast : Bool) (b₀ b₁ : Time) (B : Block)
    (k : Nat) (s : Slot) :
    OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho) fast b₀ b₁ B k s =
      (restoredLabel p b₁ < s ∧ ∃ q K,
        rho.events[k]? = some
          (.tick (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s)) ∧
        outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
          (SA.voteTime p.toParams s) ∧
        HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K ∧
        ¬ Block.Preceq B K) := rfl

/-- The first regression is selected only among actual scoped reads in this finite run.
The other branch says that every such emitted target covers B. -/
theorem outage_first_scoped_regression {fast : Bool} {b₀ b₁ : Time} {B : Block} :
    (∀ k s, ¬ OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s) ∨
    ∃ m k, OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k m ∧
      ∀ s, s < m → ∀ j, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
        (rho := rho) fast b₀ b₁ B j s := by
  classical
  by_cases h : ∃ s k, OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s
  · obtain ⟨k, hk⟩ := Nat.find_spec h
    exact Or.inr ⟨Nat.find h, k, hk, fun s hs j hj => Nat.find_min h hs ⟨j, hj⟩⟩
  · exact Or.inl (fun k s hk => h ⟨s, k, hk⟩)

/-- The first event witness also excludes regressions at earlier same-label reads. -/
theorem outage_first_scoped_regression_event {fast : Bool} {b₀ b₁ : Time} {B : Block} :
    (∀ k s, ¬ OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s) ∨
    ∃ k s, OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s ∧
      ∀ j, j < k → ∀ q, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
        (rho := rho) fast b₀ b₁ B j q := by
  classical
  by_cases h : ∃ k s, OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s
  · obtain ⟨s, hs⟩ := Nat.find_spec h
    exact Or.inr ⟨Nat.find h, s, hs, fun j hj q hq => Nat.find_min h hj ⟨q, hq⟩⟩
  · exact Or.inl (fun k s hk => h ⟨k, s, hk⟩)

/-- Absence of regression in an event prefix produces all restored results in that prefix.
HEAD ticks precede their gate. No HEAD outside the prefix is requested. -/
theorem outage_results_before_regression [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) {B : Block} {I : Nat}
    (hNo : ∀ k s, k < I → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B k s) :
    ∀ j x s C, j < I → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B := by
  intro j x s C hj hx hrs hG hC
  apply outage_continuation_result_of_head_history h hx hrs hG hC
  intro q K hReader hK
  have hKeep := hK
  obtain ⟨k, _, _, hk, _, _, _⟩ := hK
  have hkj := V2.D.Engine.eventIndex_lt_of_time_lt h.pre.base.valid.toScheduleWellFormed
    hk hG.1 (fgsa_vote_lt_gate p s)
  apply Bool.or_eq_true_iff.mpr
  right
  by_contra hn
  exact hNo k s (hkj.trans hj) ⟨hrs, q, K, hk, hReader, hKeep, hn⟩

/-- The auxiliary zero-length outage uses the same healthy prefix.
Its smaller W set inherits E1 from the actual continuation regime. -/
theorem outage_continuation_arming_regime [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutageSleep₂ p c fast E rho T b₀ b₀ ΔF := by
  classical
  obtain ⟨r, hr, hCount⟩ := outage_e1_of_e p c E rho fast b₀ b₁ h.pre.base h.protection
  have hr₀ := outage_first_restored_label p b₀
  have hrr : restoredLabel p b₀ ≤ r :=
    (hr₀ r).mp (h.order.2.2.1.trans ((hr r).mpr le_rfl))
  have hW : outageW p E rho fast b₀ (restoredLabel p b₀) ⊆ outageW p E rho fast b₀ r := by
    intro y hy
    obtain ⟨hy, hn, s, hb, hs, ha⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy, hn, s, hb, hs.trans hrr, ha⟩
  refine ⟨outageV_arming_prem h.toOutageContinuationPrem, h.sleepPre,
    h.joinedSleepy, h.joinedFastPart, restoredLabel p b₀, hr₀, ?_⟩
  have hcard := Finset.card_le_card
    (Finset.union_subset_union (Finset.Subset.refl (Gen.V2.Duty.faulty rho)) hW)
  omega

section Prefix

variable [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

include h hf htsrc hnamed in
/-- The no-regression branch supplies the complete finite result prefix and event state.
The two seeds are at the first restored gate, not at every honest receiver. -/
theorem outage_no_regression_prefix {B : FGBlock (Fin p.n)} {I i : Nat}
    (hStart : afterTicksIdx rho (SA.gateTime p.toParams (restoredLabel p b₁)) ≤ I)
    (hSeed : OutageSourceHistory p c E rho (eraseFG B) I)
    (hCover : ∀ x ∈ coveredNodes p E rho fast b₀,
      Block.Preceq (eraseFG B) (S_at p c E rho I x))
    (hNo : ∀ k s, k < i → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ (eraseFG B) k s)
    (hI : I ≤ i) (hi : i ≤ rho.events.length) :
    (∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C (eraseFG B)) ∧
    OutageSourceHistory p c E rho (eraseFG B) i ∧ OutageNamedHistory p c E rho B i ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho i x) (eraseFG B)) ∧
      ∀ x ∈ coveredNodes p E rho fast b₀,
        Block.Preceq (eraseFG B) (S_at p c E rho i x) := by
  have hResults := outage_results_before_regression h hNo
  exact ⟨hResults, outage_continuation_event_induction h.pre.base hf htsrc hnamed rfl
    hStart hSeed hCover (fun j x s C _ hj => hResults j x s C hj) hI hi⟩

include h hf htsrc hnamed in
/-- The arming certificate produces the protected seed at earlyTime(r).
This cut contains the label-(r-1) gates and every label-r good HEAD.
Its horizon guard is supplied by any later actual restored gate. -/
theorem outage_restored_vote_seed
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hβ : eraseFG β = B)
    (hHor : SA.earlyTime p.toParams (restoredLabel p b₁) ≤ rho.horizon) :
    let r := restoredLabel p b₁
    let I := afterTicksIdx rho (SA.earlyTime p.toParams r)
    OutageSourceHistory p c E rho B I ∧ OutageNamedHistory p c E rho β I ∧
      (∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho I x)) ∧
      ∀ q K, rho.seatOf (.base (.head r)) q ∈ outageH p E rho r \ outageW p E rho fast b₀ r →
        HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head r)) q)
          (ofHead p ⟨.seat (.head r) q, K.root⟩) (SA.voteTime p.toParams r) K →
        Block.Preceq B K := by
  classical
  intro r I
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hr := outage_first_restored_label p b₁
  have hjr : l + 1 < r := by
    by_contra hn
    have hrj : r ≤ l + 1 := by dsimp only [Slot] at hn ⊢; omega
    have hv := (hr (l + 1)).mpr hrj
    have hjb : SA.voteTime p.toParams (l + 1) < b₀ := by
      apply lt_of_lt_of_le _ hc.gate_le_cut
      rw [arming_vote_eq, arming_gate_eq]
      push_cast
      linarith [p.deltaPos]
    exact (not_lt_of_ge (h.order.2.2.1.trans hv)) hjb
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hh := ((arming_gate_le_iff p 0 l).mpr (Nat.zero_le l)).trans hc.gate_le_cut
    simpa only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] using hh
  have hBoundR : r ≤ l + 1 + p.k := by
    have hb := (outageV_iff_restored_label p b₀ b₁ h6 r hr).mp h.lengthV
    change r ≤ coverLabel p b₀ + p.k at hb
    rwa [hc.cover_label] at hb
  have hGate : SA.gateTime p.toParams (l + 1) ≤ SA.earlyTime p.toParams r := by
    rw [arming_gate_eq, arming_early_eq]
    have hcast := Int.ofNat_le.mpr (Nat.succ_le_of_lt hjr)
    push_cast at hcast ⊢
    nlinarith [p.deltaPos]
  have hEnd : SA.freezeTime p.toParams r ≤ SA.gateTime p.toParams (l + 1) + L p := by
    rw [arming_freeze_eq, arming_gate_eq]
    change 4 * p.Δ * (r : Int) + 3 * p.Δ ≤
      4 * p.Δ * ((l + 1 : Nat) : Int) + 6 * p.Δ + (4 * (p.k : Int) - 1) * p.Δ
    have hcast := Int.ofNat_le.mpr hBoundR
    push_cast at hcast ⊢
    nlinarith [p.deltaPos]
  have hEarly : SA.earlyTime p.toParams r < SA.freezeTime p.toParams r := by
    rw [arming_early_eq, arming_freeze_eq]
    linarith [p.deltaPos]
  have hVotes : ∀ s, SA.voteTime p.toParams s < SA.freezeTime p.toParams r → s ≤ r := by
    intro s hv
    rw [arming_vote_eq, arming_freeze_eq] at hv
    have hslt : (s : Int) < (r : Int) + 1 := by nlinarith [p.deltaPos]
    dsimp only [Slot] at *
    omega
  obtain ⟨r', hr', hBad⟩ := outage_e1_release_bound
    (outage_e1_of_e p c E rho fast b₀ b₁ h.pre.base h.protection)
  have heq : r' = r := Nat.le_antisymm
    ((hr' r).mp ((hr r).mpr le_rfl)) ((hr r').mp ((hr' r').mpr le_rfl))
  subst r'
  have hAux := outage_continuation_arming_regime h
  have hFlight := arming_inflight_heads_sleep hAux hf hsrc hState hprov hc hne
  obtain ⟨hSource, hDuty, hNames, hLocal⟩ := outage_event_induction_before_vote_cut
    h.pre.base hf hsrc htsrc hnamed hVotes hc.cut_lt_pending hBad hβ hEnd
    (outage_arming_sources_scoped h.sleepPre htsrc hc)
    (fun x hx => (outage_arming_protection_scoped h.sleepPre hf htsrc hne hc hnamed
      (hGate.trans hHor) x hx).1) hFlight
    (afterTicksIdx_mono rho hGate)
    ((preIdx_le_afterTicksIdx E rho hs _).2.trans (arming_timeIdx_le_idxBefore rho hEarly))
  refine ⟨hSource, hNames, fun x hx => (hLocal x hx).1, ?_⟩
  intro q K hGood hK
  apply outage_good_head_through_restored hc.cut_lt_pending hDuty hFlight hjr le_rfl hGood hK
  intro k hk
  exact ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr (arming_vote_lt_early p r).1).trans_le
    (preIdx_le_afterTicksIdx E rho hs _).1

include h hf htsrc hnamed in
/-- The arming certificate produces the source and G stable seeds internally.
This state consumer takes only the exact bounded restored result history. -/
theorem outage_continuation_of_results
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    (hHor : SA.earlyTime p.toParams (restoredLabel p b₁) ≤ rho.horizon)
    {i : Nat} (hI : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ i)
    (hi : i ≤ rho.events.length)
    (hResults : ∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) :
    (∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) ∧
    OutageSourceHistory p c E rho B i ∧ OutageNamedHistory p c E rho β i ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho i x) B) ∧
      ∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho i x) := by
  classical
  let r := restoredLabel p b₁
  have hr := outage_first_restored_label p b₁
  obtain ⟨hSource, _, hCover, hGood⟩ :=
    outage_restored_vote_seed h hf htsrc hnamed hsrc hState hprov hne hc hβ hHor
  have hr0 : 0 < r := by
    by_contra hn
    have heq : r = 0 := by dsimp only [Slot] at hn ⊢; omega
    have hv := (hr r).mpr le_rfl
    rw [heq, arming_vote_eq] at hv
    have hh := ((arming_gate_le_iff p 0 l).mpr (Nat.zero_le l)).trans hc.gate_le_cut
    simp only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] at hh hv
    linarith [h.order.2.2.1, p.deltaPos]
  have hStart : afterTicksIdx rho (SA.gateTime p.toParams (r - 1)) ≤
      afterTicksIdx rho (SA.earlyTime p.toParams r) := by
    apply afterTicksIdx_mono
    rw [arming_gate_eq, arming_early_eq]
    have hsub : ((r - 1 : Nat) : Int) = (r : Int) - 1 := by
      dsimp only [Slot] at hr0 ⊢; omega
    rw [hsub]
    ring_nf
    exact le_rfl
  obtain ⟨r', hr', hCount⟩ := h.protection
  have heq : r' = r := Nat.le_antisymm
    ((hr' r).mp ((hr r).mpr le_rfl)) ((hr r').mp ((hr' r').mpr le_rfl))
  subst r'
  have hRest : ∀ j x s C, j < i → x ∈ rho.honest → r - 1 < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B := by
    intro j x s C hj hx hrs hG hC
    have hsr : r ≤ s := by dsimp only [Slot] at hr0 hrs ⊢; omega
    rcases hsr.lt_or_eq with hlt | heq
    · exact hResults j x s C hj hx hlt hG hC
    subst s
    exact outage_restored_result_of_compatible_heads h.pre.base h.sync hx hG
      (h.gst.trans ((hr r).mpr le_rfl))
      (hCount r le_rfl (by dsimp only [Slot]; omega))
      (fun q K hq hK => Bool.or_eq_true_iff.mpr (Or.inr (hGood q K hq hK))) hC
  exact ⟨hResults, outage_continuation_event_induction h.pre.base hf htsrc hnamed hβ
    hStart hSource hCover (fun j x s C _ hj => hRest j x s C hj) hI hi⟩

include h hf htsrc hnamed in
/-- Absence of actual regression produces the bounded result input internally. -/
theorem outage_no_regression_continuation
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    (hHor : SA.earlyTime p.toParams (restoredLabel p b₁) ≤ rho.horizon)
    {i : Nat} (hI : afterTicksIdx rho (SA.earlyTime p.toParams (restoredLabel p b₁)) ≤ i)
    (hi : i ≤ rho.events.length)
    (hNo : ∀ k s, k < i → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B k s) :
    (∀ j x s C, j < i → x ∈ rho.honest → restoredLabel p b₁ < s →
      enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) ∧
    OutageSourceHistory p c E rho B i ∧ OutageNamedHistory p c E rho β i ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho i x) B) ∧
      ∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho i x) := by
  exact outage_continuation_of_results h hf htsrc hnamed hsrc hState hprov hne hc hβ
    hHor hI hi (outage_results_before_regression h hNo)

omit [Fintype V] in
/-- Event-first selection excludes every regression at a smaller label. -/
theorem outage_no_lower_of_first_event {fast : Bool} {b₀ b₁ : Time} {B : Block}
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hFirst : ∀ j, j < k → ∀ q, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    ∀ j q, q < s → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q := by
  obtain ⟨_, _, _, hk, _, _, _⟩ := hReg
  intro j q hqs hj
  have hjKeep := hj
  obtain ⟨_, _, _, hjtick, _, _, _⟩ := hj
  have htime : SA.voteTime p.toParams q < SA.voteTime p.toParams s := by
    rw [arming_vote_eq, arming_vote_eq]
    have hcast := Int.ofNat_lt.mpr hqs
    nlinarith [p.deltaPos]
  exact hFirst j (V2.D.Engine.eventIndex_lt_of_time_lt hs hjtick hk htime) q hjKeep

include h hf htsrc hnamed in
/-- The first actual regression has a produced causal prefix at its own read.
Same-label regressions are excluded by selecting the first event witness. -/
theorem outage_regression_prefix_no_lower
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hNo : ∀ j q, q < s → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    (∀ j x q C, j < k → x ∈ rho.honest → restoredLabel p b₁ < q →
      enabledGateAt p c E rho j x q → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) ∧
    OutageSourceHistory p c E rho B k ∧ OutageNamedHistory p c E rho β k ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho k x) B) ∧
      ∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho k x) := by
  obtain ⟨hrs, q, K, hk, _, _, _⟩ := hReg
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hEV : SA.earlyTime p.toParams (restoredLabel p b₁) < SA.voteTime p.toParams s := by
    rw [arming_early_eq, arming_vote_eq]
    have hcast := Int.ofNat_le.mpr (Nat.succ_le_of_lt hrs)
    push_cast at hcast
    nlinarith [p.deltaPos]
  have hIdx : rho.idxBefore (SA.voteTime p.toParams s) ≤ k := by
    by_contra hn
    exact (lt_irrefl _) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mp
      (Nat.lt_of_not_ge hn))
  exact outage_continuation_of_results h hf htsrc hnamed hsrc hState hprov hne hc hβ
    (hEV.le.trans (hs.in_horizon _ (List.mem_of_getElem? hk)).2)
    (((preIdx_le_afterTicksIdx E rho hs _).2.trans
      (arming_timeIdx_le_idxBefore rho hEV)).trans hIdx)
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hk).1)
    (by
      intro j x q C hj hx hrq hG hC
      apply outage_continuation_result_of_head_history h hx hrq hG hC
      intro w L hReader hL
      have hKeep := hL
      obtain ⟨a, _, _, ha, _, _, _⟩ := hL
      have hqm : q < s := by
        have htime := inclusion_time_le_of_tick hs hk j hj _ hG.1
        change SA.gateTime p.toParams q ≤ SA.voteTime p.toParams s at htime
        rw [arming_gate_eq, arming_vote_eq] at htime
        have hcast : (q : Int) < (s : Int) := by nlinarith [p.deltaPos]
        exact_mod_cast hcast
      apply Bool.or_eq_true_iff.mpr
      right
      by_contra hn
      exact hNo a q hqm ⟨hrq, w, L, ha, hReader, hKeep, hn⟩)

include h hf htsrc hnamed in
/-- The first event supplies the absence guard for every lower label. -/
theorem outage_first_regression_prefix
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hFirst : ∀ j, j < k → ∀ q, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    (∀ j x q C, j < k → x ∈ rho.honest → restoredLabel p b₁ < q →
      enabledGateAt p c E rho j x q → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) ∧
    OutageSourceHistory p c E rho B k ∧ OutageNamedHistory p c E rho β k ∧
      (∀ x ∈ rho.honest, Block.Compatible (F_at p c E rho k x) B) ∧
      ∀ x ∈ coveredNodes p E rho fast b₀, Block.Preceq B (S_at p c E rho k x) := by
  exact outage_regression_prefix_no_lower h hf htsrc hnamed hsrc hState hprov hne hc hβ
    hReg (outage_no_lower_of_first_event h.pre.base.valid.toScheduleWellFormed hReg hFirst)

include h hf htsrc hnamed in
/-- The first regression has retained scores from the preceding actual good batch.
E supplies its fixed good set; the healthy suffix supplies the full joined set.
The receiver floor and both receipt epochs are produced at the actual read. -/
theorem outage_regression_scores_no_lower
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hNo : ∀ j q, q < s → ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    ∃ q K, rho.events[k]? = some
      (.tick (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s)) ∧
      outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
        (SA.voteTime p.toParams s) ∧
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K ∧
      ¬ Block.Preceq B K ∧
      RetainedTargetScores p (clock p (storeAt p c E rho k
        (rho.seatOf (.base (.head s)) q)) (SA.voteTime p.toParams s)) s B ∧
      ∃ j y P, rho.events[j]? = some (.tick y (SA.voteTime p.toParams (s - 1))) ∧
        y ∈ rho.honest ∧ P ∈ (storeAt p c E rho j y).fg.TF ∧
        Block.Preceq B (eraseFG P) := by
  classical
  have hRegKeep := hReg
  obtain ⟨hrs, q, K, hk, hReader, hK, hBad⟩ := hReg
  let x := rho.seatOf (.base (.head s)) q
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hslot : slotAt p (SA.voteTime p.toParams s) = s :=
    slotOf_offset p s p.Δ p.deltaPos.le
      (by have := p.deltaPos; dsimp [Time] at *; omega)
  have hx := hReader.1.1
  have hJ : joinedAt p E rho x s (SA.voteTime p.toParams s) := by
    simpa only [hslot, x] using hReader.1.2
  have hpos : 0 < s := (Nat.zero_le _).trans_lt hrs
  have heq : s - 1 + 1 = s := Nat.sub_add_cancel hpos
  have hF := (outage_regression_prefix_no_lower h hf htsrc hnamed hsrc hState hprov
    hne hc hβ hRegKeep hNo).2.2.2.1 x hx
  have hFB : Block.Preceq (F_at p c E rho k x) B := by
    rcases Bool.or_eq_true_iff.mp hF with hlow | hhigh
    · exact hlow
    · apply False.elim
      apply hBad
      have hFK : Block.Preceq (F_at p c E rho k x) K := by
        rw [headTargetAtEmission_at_tick E rho hs hK hk rfl]
        let dst := clock p (storeAt p c E rho k x) (SA.voteTime p.toParams s)
        have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho k x)
          (SA.voteTime p.toParams s)
        have hr := F_preceq_liveRoot p dst hinv
        change Block.Preceq _ (if s = 0 then .genesis else headInTree p dst _ _ _)
        rw [ite_eq_right (Nat.ne_of_gt hpos)]
        apply block_preceq_trans ?_ (liveRoot_preceq_headInTree p dst _ _ _)
        change Block.Preceq (eraseFG (storeAt p c E rho k x).fg.F) _
        simpa only [dst, clock_fg] using hr
      exact block_preceq_trans hhigh hFK
  have hhor : SA.voteTime p.toParams s ≤ rho.horizon :=
    (hs.in_horizon _ (List.mem_of_getElem? hk)).2
  have hprev : restoredLabel p b₁ ≤ s - 1 := by dsimp only [Slot] at *; omega
  have hGST := h.gst.trans ((outage_first_restored_label p b₁ _).mpr hprev)
  have htime : SA.voteTime p.toParams (s - 1) < SA.voteTime p.toParams s := by
    rw [arming_vote_eq, arming_vote_eq]
    have hcast := Int.ofNat_lt.mpr (Nat.sub_lt hpos Nat.one_pos)
    nlinarith [p.deltaPos]
  have hEV : SA.earlyTime p.toParams (restoredLabel p b₁) ≤ rho.horizon := by
    apply le_trans _ hhor
    rw [arming_early_eq, arming_vote_eq]
    have hcast := Int.ofNat_le.mpr (Nat.succ_le_of_lt hrs)
    push_cast at hcast; nlinarith [p.deltaPos]
  have hGood := (outage_restored_vote_seed h hf htsrc hnamed hsrc hState hprov
    hne hc hβ hEV).2.2.2
  have target (w : Fin p.n) (L : Block)
      (hP : restoredLabel p b₁ < s - 1)
      (hR : outageHeadReader p E rho fast b₀ b₁
        (rho.seatOf (.base (.head (s - 1))) w) (SA.voteTime p.toParams (s - 1)))
      (hL : HeadTargetAtEmission p c E rho
        (rho.seatOf (.base (.head (s - 1))) w)
        (ofHead p ⟨.seat (.head (s - 1)) w, L.root⟩) (SA.voteTime p.toParams (s - 1)) L) :
      Block.Preceq B L := by
    have hKeep := hL
    obtain ⟨j, _, _, hj, _, _, _⟩ := hL
    by_contra hn
    exact hNo j (s - 1) (Nat.sub_lt hpos Nat.one_pos) ⟨hP, w, L, hj, hR, hKeep, hn⟩
  refine ⟨q, K, hk, hReader, hK, hBad, ?_⟩
  obtain ⟨r, hr, hCount⟩ := h.protection
  have hrCanon := outage_first_restored_label p b₁
  have hreq : r = restoredLabel p b₁ := Nat.le_antisymm
    ((hr _).mp ((hrCanon _).mpr le_rfl)) ((hrCanon _).mp ((hr _).mpr le_rfl))
  subst r
  by_cases hWindow : s - 1 ≤ restoredLabel p b₁ + p.k + 1
  · obtain ⟨H, hH, hCard⟩ := outage_good_seats E rho h.pre.base.cstar fast b₀
      (restoredLabel p b₁) (s - 1)
    have hSelected : ∀ w ∈ H, rho.seatOf (.base (.head (s - 1))) w ∈ rho.honest ∧
        joinedAt p E rho (rho.seatOf (.base (.head (s - 1))) w) (s - 1)
          (SA.voteTime p.toParams (s - 1)) := by
      intro w hw
      have hm := (Finset.mem_sdiff.mp ((hH w).mp hw)).1
      change _ ∈ rho.honest.filter _ at hm
      have hsl : slotAt p (SA.voteTime p.toParams (s - 1)) = s - 1 :=
        slotOf_offset p _ p.Δ p.deltaPos.le
          (by have := p.deltaPos; dsimp [Time] at *; omega)
      simpa only [hsl] using Finset.mem_filter.mp hm
    have hTargets : ∀ w ∈ H, ∀ L, HeadTargetAtEmission p c E rho
        (rho.seatOf (.base (.head (s - 1))) w)
        (ofHead p ⟨.seat (.head (s - 1)) w, L.root⟩)
        (SA.voteTime p.toParams (s - 1)) L → Block.Preceq B L := by
      intro w hw L hL
      rcases hprev.lt_or_eq with hlt | he
      · apply target w L hlt _ hL
        refine ⟨⟨(hSelected w hw).1, ?_⟩, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
        · have hsl : slotAt p (SA.voteTime p.toParams (s - 1)) = s - 1 :=
            slotOf_offset p _ p.Δ p.deltaPos.le
              (by have := p.deltaPos; dsimp [Time] at *; omega)
          simpa only [hsl] using (hSelected w hw).2
        · exact (Finset.mem_sdiff.mp ((hH w).mp hw)).2
        · rw [arming_vote_eq, arming_vote_eq]
          have hcast := Int.ofNat_le.mpr (Nat.succ_le_of_lt hlt)
          push_cast at hcast ⊢; nlinarith [p.deltaPos]
      · have hGW := (hH w).mp hw
        rw [← he] at hGW hL
        exact hGood w L hGW hL
    have hRec := outage_prior_good_receipts h.pre.base h.sync hf
      (heq.symm ▸ hk) hx (heq.symm ▸ hJ) hGST hFB H hSelected hTargets
    have hPart := hCard.symm ▸ hCount (s - 1) hprev hWindow
    refine ⟨?_, outage_prior_covering_source h.pre.base (htime.le.trans hhor) H
      (Finset.card_pos.mp ((Nat.zero_le _).trans_lt hPart)) hSelected hTargets⟩
    simpa only [heq, storeAt, x] using outage_receiver_scores_of_bound E rho h.pre.base.valid
      h.pre.base.delta (s - 1) (heq.symm ▸ hk) H (fun w hw => (hSelected w hw).1)
      _ ⟨hPart⟩ (fun L => outage_pool_opponent_bound h.pre.base fast b₀
        (restoredLabel p b₁) (s - 1) H hH L) B hRec hx (heq.symm ▸ hJ) B
      (block_preceq_refl B)
  · have hAfter : restoredLabel p b₁ + p.k + 1 ≤ s - 1 := by
      dsimp only [Slot] at *; omega
    obtain ⟨H, hH, hBatch⟩ := inclusion_joined_head_seats E rho h.pre.base.cstar (s - 1)
      ⟨outage_post_e_joined_count h hAfter (htime.le.trans hhor)⟩
    have hTargets : ∀ w ∈ H, ∀ L, HeadTargetAtEmission p c E rho
        (rho.seatOf (.base (.head (s - 1))) w)
        (ofHead p ⟨.seat (.head (s - 1)) w, L.root⟩)
        (SA.voteTime p.toParams (s - 1)) L → Block.Preceq B L := by
      intro w hw L hL
      have hlt : restoredLabel p b₁ < s - 1 := by
        dsimp only [Slot] at *; omega
      apply target w L hlt _ hL
      have hEnd : OutageEnd p (restoredLabel p b₁) ≤ SA.voteTime p.toParams (s - 1) := by
        change 4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ ≤ _
        rw [arming_vote_eq]
        have hcast := Int.ofNat_le.mpr hAfter
        push_cast at hcast ⊢; nlinarith [p.deltaPos]
      refine ⟨?_, Or.inr (Or.inr hEnd)⟩
      have hsl : slotAt p (SA.voteTime p.toParams (s - 1)) = s - 1 :=
        slotOf_offset p _ p.Δ p.deltaPos.le
          (by have := p.deltaPos; dsimp [Time] at *; omega)
      change _ ∈ rho.honest ∧ joinedAt p E rho _ (slotAt p _) _
      simpa only [hsl] using (hH w).mp hw
    have hRec := outage_prior_good_receipts h.pre.base h.sync hf
      (heq.symm ▸ hk) hx (heq.symm ▸ hJ) hGST hFB H (fun w hw => (hH w).mp hw) hTargets
    refine ⟨?_, outage_prior_covering_source h.pre.base (htime.le.trans hhor) H
      (Finset.card_pos.mp ((Nat.zero_le _).trans_lt hBatch.lt))
      (fun w hw => (hH w).mp hw) hTargets⟩
    simpa only [heq, storeAt, x] using outage_receiver_scores_of_bound E rho h.pre.base.valid
      h.pre.base.delta (s - 1) (heq.symm ▸ hk) H (fun w hw => ((hH w).mp hw).1)
      _ hBatch (fun L => inclusion_joined_rest_bound E rho h.pre.base.cstar
        h.pre.base.valid (s - 1) H (fun w hh hJ => (hH w).mpr ⟨hh, hJ⟩) L)
      B hRec hx (heq.symm ▸ hJ) B (block_preceq_refl B)

include h hf htsrc hnamed in
/-- Retained scores and a prior source at the first actual regression event. -/
theorem outage_first_regression_scores
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hFirst : ∀ j, j < k → ∀ q, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    ∃ q K, rho.events[k]? = some
      (.tick (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s)) ∧
      outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
        (SA.voteTime p.toParams s) ∧
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K ∧
      ¬ Block.Preceq B K ∧
      RetainedTargetScores p (clock p (storeAt p c E rho k
        (rho.seatOf (.base (.head s)) q)) (SA.voteTime p.toParams s)) s B ∧
      ∃ j y P, rho.events[j]? = some (.tick y (SA.voteTime p.toParams (s - 1))) ∧
        y ∈ rho.honest ∧ P ∈ (storeAt p c E rho j y).fg.TF ∧
        Block.Preceq B (eraseFG P) := by
  exact outage_regression_scores_no_lower h hf htsrc hnamed hsrc hState hprov hne hc hβ
    hReg (outage_no_lower_of_first_event h.pre.base.valid.toScheduleWellFormed hReg hFirst)

end Prefix

/-- A path held before freeze is in this joined reader's frozen voter set.
The read guard produces the exact stamp epoch; durable TF alone is not enough. -/
theorem outage_frozen_path_at_joined_read
    (hBase : Base₂ p c E rho) (hf : FGFoundation p c E rho)
    {j i : Nat} {x : V} {t : Time} {s : Slot} {P : FGBlock (Fin p.n)}
    (hj : rho.events[j]? = some (.tick x t))
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hJ : joinedAt p E rho x s (SA.voteTime p.toParams s))
    (ht : 0 < t) (hAfter : slotStartZ p ((s : Int) - 1) < t)
    (hFreeze : t ≤ SA.freezeTime p.toParams (s - 1)) (hji : j ≤ i)
    (hP : P ∈ (storeAt p c E rho j x).fg.TF)
    (hFP : FGBlock.Preceq (storeAt p c E rho i x).fg.F P) :
    P ∈ voterBlocks p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s)) s := by
  have hs := hBase.valid.toScheduleWellFormed
  have hx := hs.honest_only _ (List.mem_of_getElem? hi)
  have hBound {k : Nat} {w : Time}
      (hki : k < i) (hk : rho.events[k]? = some (.restart x w)) : w < t := by
    have hw0 := (hs.in_horizon _ (List.mem_of_getElem? hk)).1
    have hwi := inclusion_time_le_of_tick hs hi k hki _ hk
    exact (hJ.2.2 w hw0 hwi (List.mem_of_getElem? hk)).trans_lt hAfter
  have hRF : V2.D.restartFree rho x j i := by
    intro k w hjk hki hk
    exact (Nat.not_lt.mpr hjk)
      (V2.D.Engine.eventIndex_lt_of_time_lt hs hk hj (hBound hki hk))
  have hEpoch : ∀ k w, k < j → rho.events[k]? = some (.restart x w) → w < t :=
    fun k w hkj hk => hBound (hkj.trans_le hji) hk
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hPb : eraseFG P ∈ (storeAt p c E rho j x).base.blocks :=
    ((cstoreInv_stateBefore E rho j x).baseTree _).mpr ⟨P, hP, rfl⟩
  have hKey : eraseFG P ∈ (storeAt p c E rho j x).base.blockStamp.map Prod.fst := by
    change eraseFG P ∈ (rho.stateBefore E j x).st.base.blockStamp.map Prod.fst
    rw [(storeBundle_stateBefore E rho j x).«meta».stampKeys]
    exact hPb
  have hKept := (hf.cumul.2 j i x hx hji
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hi).1) hRF).1
  have hKey' : eraseFG P ∈ (storeAt p c E rho i x).base.blockStamp.map Prod.fst := by
    obtain ⟨row, hr, he⟩ := List.mem_map.mp hKey
    exact List.mem_map.mpr ⟨row, hKept.subset hr, he⟩
  have hStamp : GridCO.stampBlock dst.base (eraseFG P) =
      GridCO.stampBlock (storeAt p c E rho j x).base (eraseFG P) := by
    exact (inclusion_stampBlock_of_prefix
      (show (storeAt p c E rho i x).base.blockStamp <+: dst.base.blockStamp by
        rw [(clock_cumulative p _ _).2.2.1]) hKey').trans
      (inclusion_stampBlock_of_prefix hKept hKey)
  have hPd : P ∈ dst.fg.TF := by
    rw [show dst.fg = (storeAt p c E rho i x).fg from clock_fg p _ _]
    exact (hf.cumul.1 j i x hx hji
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hi).1)).1 hP
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hPd, ?_⟩,
    Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true ?_))⟩
  · simpa only [dst, clock_fg, FGBlock.Preceq] using hFP
  · rw [hStamp]
    exact (fgsa_gateReceipt_block_stamp_lt_on E rho hs hj ht hEpoch _ hPb).trans_le hFreeze

/-- A contested actual read supplies one durable marker from its named source history.
This is a local producer; it requests no transport to other receivers. -/
theorem outage_contested_marker_of_names
    (hf : FGFoundation p c E rho) {B : FGBlock (Fin p.n)} {k : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest)
    (hNames : OutageNamedHistory p c E rho B k)
    (hContest : (controls p (clock p (storeAt p c E rho k x)
      (SA.voteTime p.toParams s))).contest = true) :
    ∃ P ∈ (storeAt p c E rho k x).fg.TF,
      FGBlock.Preceq B (heightView p P).J ∧ (heightView p P).h_j ≠ 0 := by
  have hc : (controls p (storeAt p c E rho k x)).contest = true := by
    change (KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg).contest = true
      at hContest
    rwa [clock_fg] at hContest
  have hBJ := (fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat
    k x B hx hNames.history).2.2.2.2 hc
  obtain ⟨hnz, P, hP, hj, hJ, _⟩ := outageV_contest_carrier p (storeAt p c E rho k x)
    (cstoreInv_stateBefore E rho k x) hc
  exact ⟨P, hP, hJ.symm ▸ hBJ.1, hj.symm ▸ hnz⟩

/-- A regressed read with the prior retained scores must be contested.
Only the uncontested branch needs the local filtered-path witnesses.
Producing these witnesses from the prior joined good batch is P-Ou work. -/
theorem outage_regression_contested_of_retained_batch
    {B : Block} {k : Nat} {x : V} {s : Slot}
    (hs : s ≠ 0)
    (hBad : ¬ Block.Preceq B (headVote p (clock p (storeAt p c E rho k x)
      (SA.voteTime p.toParams s)) s))
    (hRoot : Block.Compatible (liveRoot p (clock p (storeAt p c E rho k x)
      (SA.voteTime p.toParams s))) B)
    (hScores : RetainedTargetScores p (clock p (storeAt p c E rho k x)
      (SA.voteTime p.toParams s)) s B)
    (hPath : (controls p (clock p (storeAt p c E rho k x)
        (SA.voteTime p.toParams s))).contest = false →
      ∀ C, Block.Prec (liveRoot p (clock p (storeAt p c E rho k x)
        (SA.voteTime p.toParams s))) C → Block.Preceq C B →
      ∃ X ∈ voterBlocks p (clock p (storeAt p c E rho k x)
          (SA.voteTime p.toParams s)) s, eraseFG X = C ∧
        ∃ W ∈ voterBlocks p (clock p (storeAt p c E rho k x)
            (SA.voteTime p.toParams s)) s,
          FGBlock.Preceq X W ∧
          (controls p (clock p (storeAt p c E rho k x)
            (SA.voteTime p.toParams s))).lo ≤ (heightView p W).h) :
    (controls p (clock p (storeAt p c E rho k x)
      (SA.voteTime p.toParams s))).contest = true := by
  by_contra hn
  apply hBad
  apply outageV_head_covers_of_witnesses p _
    (cstoreInv_clock p _ (cstoreInv_stateBefore E rho k x) _) B hs hRoot
    (hPath (Bool.eq_false_iff.mpr hn)) hScores.majority
  intro D hD
  have h₁ := hScores.rivals D hD
  have h₂ := hScores.majority
  change 2 * RetainedWalk.ts p _ s D ≤ _ at h₁
  change _ < 2 * RetainedWalk.ts p _ s B at h₂
  change RetainedWalk.ts p _ s D < RetainedWalk.ts p _ s B
  dsimp only [storeAt] at h₁ h₂ ⊢
  omega

end AvailableChain.FGSA.Run
end
