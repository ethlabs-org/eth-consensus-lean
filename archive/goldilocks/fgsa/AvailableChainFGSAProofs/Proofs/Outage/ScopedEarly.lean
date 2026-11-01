module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedBridge -- shake: keep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

section Early

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
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)

include h hf htsrc hnamed hsrc hState hprov hne hc hβ in
/-- Use the current finite prefix before freeze(r). No later seed event is required. -/
theorem outage_early_event_state {i : Nat}
    (hGate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hI : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i)
    (hi : i ≤ rho.idxBefore (SA.freezeTime p.toParams (restoredLabel p b₁))) :
    OutageSourceHistory p c E rho B i ∧
      OutageCoveredDutyHistory (p := p) (c := c) (E := E) (rho := rho)
        fast b₀ B (l + 1) i ∧ OutageNamedHistory p c E rho β i ∧
      ∀ x ∈ coveredNodes p E rho fast b₀,
        OutageProtection p B (l + 1) (storeAt p c E rho i x) := by
  classical
  let r := restoredLabel p b₁
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
  have hGateEarly : SA.gateTime p.toParams (l + 1) ≤ SA.earlyTime p.toParams r := by
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
  exact outage_event_induction_before_vote_cut h.pre.base hf hsrc htsrc hnamed
    hVotes hc.cut_lt_pending hBad hβ hEnd
    (outage_arming_sources_scoped h.sleepPre htsrc hc)
    (fun x hx => (outage_arming_protection_scoped h.sleepPre hf htsrc hne hc hnamed
      hGate x hx).1) hFlight hI hi

include h hf htsrc hnamed hsrc hState hprov hne hc hβ in
/-- O11-EARLY-F at the inclusive read, including a horizon before earlyTime(r). -/
theorem outage_early_finalized_read {x : V} {t : Time} (hx : x ∈ rho.honest)
    (hb : b₀ ≤ t) (hhor : t ≤ rho.horizon)
    (ht : t < SA.earlyTime p.toParams (restoredLabel p b₁)) :
    Block.Compatible B (F_at p c E rho (timeIdx rho t) x) := by
  by_cases hdt : SA.gateTime p.toParams (l + 1) ≤ t
  · obtain ⟨_, _, hNames, _⟩ := outage_early_event_state h hf htsrc hnamed hsrc
      hState hprov hne hc hβ (hdt.trans hhor)
      ((afterTicksIdx_mono rho hdt).trans
        (preIdx_le_afterTicksIdx E rho h.pre.base.valid.toScheduleWellFormed t).2)
      (arming_timeIdx_le_idxBefore rho (ht.trans (by
        rw [arming_early_eq, arming_freeze_eq]; linarith [p.deltaPos])))
    exact Bool.or_eq_true_iff.mpr (Or.symm
      (Bool.or_eq_true_iff.mp (outage_source_frame_compatible hf hβ hNames hx)))
  · exact arming_compat hc.max_read hc.f_below x t hx
      (h.order.1.trans (h.order.2.1.trans hb)) (lt_of_not_ge hdt) hhor

include h hf htsrc hnamed hsrc hState hprov hne hc hβ in
/-- O11-EARLY-READ. Before earlyTime(r), a scoped confirmed reader is covered. -/
theorem outage_early_public_read
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y))
    {x : V} {t : Time} (hb : b₀ ≤ t)
    (hhor : t ≤ rho.horizon) (ht : t < SA.earlyTime p.toParams (restoredLabel p b₁))
    (hReader : outageConfirmedReader p c E rho fast b₀ b₁ x t) :
    Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
      Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
      (x ∈ coveredNodes p E rho fast b₀ →
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x) ∧
        Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
        Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t)) := by
  classical
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hxG : x ∈ coveredNodes p E rho fast b₀ := by
    rcases hReader.2 with hG | ⟨s, j, hEnd, hst, _⟩
    · exact hG
    · have hEndEarly : SA.earlyTime p.toParams (restoredLabel p b₁) <
          OutageEnd p (restoredLabel p b₁) := by
        change 4 * p.Δ * (restoredLabel p b₁ : Int) + 2 * p.Δ <
          4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ
        push_cast; nlinarith [p.deltaPos, Nat.cast_nonneg (α := Int) p.k]
      exact (not_lt_of_ge (hEnd.trans hst) (ht.trans hEndEarly)).elim
  have hBS : Block.Preceq B (S_at p c E rho (timeIdx rho t) x) := by
    by_cases hdt : SA.gateTime p.toParams (l + 1) ≤ t
    · exact (outage_early_event_state h hf htsrc hnamed hsrc hState hprov hne hc hβ
        (hdt.trans hhor) ((afterTicksIdx_mono rho hdt).trans
          (preIdx_le_afterTicksIdx E rho hs t).2)
        (arming_timeIdx_le_idxBefore rho (ht.trans (by
          rw [arming_early_eq, arming_freeze_eq]; linarith [p.deltaPos])))).2.2.2 x hxG |>.1
    · have hAux := outage_continuation_arming_regime h
      exact arming_cover_sleep hAux hState hHist hOutput hc x t hxG hReader.1
        (hc.gate_le_cut.trans hb) (lt_of_not_ge hdt) hhor
  have hBF := outage_early_finalized_read h hf htsrc hnamed hsrc hState hprov hne hc hβ
    hReader.1.1 hb hhor ht
  obtain ⟨hStable, hConfirmed, _⟩ := outage_continuation_inclusive_read hs hBS
    (Bool.or_eq_true_iff.mpr (Or.symm (Bool.or_eq_true_iff.mp hBF)))
  exact ⟨block_compatible_of_common hBS (block_preceq_refl _),
    block_compatible_of_common hStable (block_preceq_refl _),
    block_compatible_of_common hConfirmed (block_preceq_refl _),
    fun _ => ⟨hBS, hStable, hConfirmed⟩⟩

omit [Fintype V] in
/-- Before the next restored vote, the scoped HEAD reader belongs to G. -/
theorem outage_early_head_reader_covered {x : V} {t : Time}
    (hReader : outageHeadReader p E rho fast b₀ b₁ x t)
    (ht : t < SA.voteTime p.toParams (restoredLabel p b₁ + 1)) :
    x ∈ coveredNodes p E rho fast b₀ := by
  rcases hReader.2 with hG | ⟨_, hv⟩ | hEnd
  · exact hG
  · exact (not_lt_of_ge hv ht).elim
  · have hNext : SA.voteTime p.toParams (restoredLabel p b₁ + 1) ≤
        OutageEnd p (restoredLabel p b₁) := by
      change 4 * p.Δ * ((restoredLabel p b₁ + 1 : Nat) : Int) + p.Δ ≤
        4 * p.Δ * ((restoredLabel p b₁ + p.k : Nat) : Int) + 5 * p.Δ
      have hk := Int.ofNat_le.mpr p.kLarge
      push_cast at hk ⊢; nlinarith [p.deltaPos]
    exact (not_lt_of_ge (hNext.trans hEnd) ht).elim

include h hf htsrc hnamed hsrc hState hprov hne hc hβ in
/-- O11-EARLY-HEAD covers actual scoped emissions at labels at most r. -/
theorem outage_early_scoped_head {s : Slot} {q : Fin p.n} {K : Block}
    (hsr : s ≤ restoredLabel p b₁) (hb : b₀ ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon)
    (hReader : outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
      (SA.voteTime p.toParams s))
    (hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K) :
    Block.Preceq B K := by
  classical
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hKeep := hK
  obtain ⟨i, _, _, hi, hem, _, _⟩ := hK
  have hNext : SA.voteTime p.toParams s <
      SA.voteTime p.toParams (restoredLabel p b₁ + 1) := by
    rw [arming_vote_eq, arming_vote_eq]
    have hc := Int.ofNat_lt.mpr (Nat.lt_succ_of_le hsr)
    push_cast at hc ⊢; nlinarith [p.deltaPos]
  have hxG := outage_early_head_reader_covered hReader hNext
  by_cases hdt : SA.gateTime p.toParams (l + 1) ≤ SA.voteTime p.toParams s
  · have ht : SA.voteTime p.toParams s <
        SA.freezeTime p.toParams (restoredLabel p b₁) := by
      rw [arming_vote_eq, arming_freeze_eq]
      have hc := Int.ofNat_le.mpr hsr
      nlinarith [p.deltaPos]
    have hI : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i := by
      apply le_of_not_gt
      intro hn
      have htick := arming_tick_le hs hi
        (hn.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)
      have hne := arming_gate_ne_vote p (l + 1) s
      exact hne (le_antisymm hdt htick)
    obtain ⟨_, hDuty, _, _⟩ := outage_early_event_state h hf htsrc hnamed hsrc hState
      hprov hne hc hβ (hdt.trans hhor) (hI.trans (Nat.le_succ i))
      (Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr ht))
    exact (hDuty.history i _ _ _ (Nat.lt_succ_self i) hxG hdt hi hem).1 K hKeep
  · exact (arming_pending_duties_sleep (outage_continuation_arming_regime h)
      hf hsrc hState hprov hc hne _ _ _ hReader.1.1 (hc.gate_le_cut.trans hb)
      (lt_of_not_ge hdt) ⟨i, hi, hem⟩).1 K hKeep

include h hf htsrc hnamed hsrc hState hprov hne hc hβ in
/-- O11-DUTY uses only actual scoped readers and their emitted duties before b1. -/
theorem outage_early_scoped_duties : DutiesExtendScoped p c E rho fast B b₀ b₁ := by
  classical
  intro x t o hReader hb htb hem
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hr := outage_first_restored_label p b₁
  have hNext : t < SA.voteTime p.toParams (restoredLabel p b₁ + 1) := by
    apply htb.trans_le
    exact (hr _).mpr (Nat.le_succ _)
  have hxG := outage_early_head_reader_covered hReader hNext
  by_cases hdt : SA.gateTime p.toParams (l + 1) ≤ t
  · obtain ⟨i, hi, ho⟩ := hem
    have ht : t < SA.freezeTime p.toParams (restoredLabel p b₁) := by
      apply htb.trans_le
      exact ((hr _).mpr le_rfl).trans (by
        rw [arming_vote_eq, arming_freeze_eq]; linarith [p.deltaPos])
    by_cases heq : t = SA.gateTime p.toParams (l + 1)
    · constructor
      · intro H hH
        obtain ⟨s, _, _, _, he, _, _⟩ := arming_emit_head h.pre.base.valid
          hReader.1.1 ⟨i, hi, ho⟩ hH
        exact (arming_gate_ne_vote p (l + 1) s (heq.symm.trans he)).elim
      · intro N hN
        obtain ⟨s, _, _, he, _, _⟩ := arming_emit_proposal h.pre.base.valid
          hReader.1.1 ⟨i, hi, ho⟩ hN
        exact (arming_gate_ne_proposal p (l + 1) s (heq.symm.trans he)).elim
    have hI : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i := by
      apply le_of_not_gt
      intro hn
      exact heq (le_antisymm (arming_tick_le hs hi
        (hn.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)) hdt)
    obtain ⟨_, hDuty, _, _⟩ := outage_early_event_state h hf htsrc hnamed hsrc hState
      hprov hne hc hβ (hdt.trans (hs.in_horizon _ (List.mem_of_getElem? hi)).2)
      (hI.trans (Nat.le_succ i))
      (Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr ht))
    exact hDuty.history i x t o (Nat.lt_succ_self i) hxG hdt hi ho
  · exact arming_pending_duties_sleep (outage_continuation_arming_regime h)
      hf hsrc hState hprov hc hne x o t hReader.1.1 (hc.gate_le_cut.trans hb)
      (lt_of_not_ge hdt) hem

end Early

end AvailableChain.FGSA.Run
end
