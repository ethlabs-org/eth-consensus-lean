module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks runs: the projections onto the component traces (C0.5)

`ac_projection` and `fg_projection` are in `Run/ACProjection` and `Run/FGProjection`. -/

namespace Consensus.Goldilocks

namespace RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- Block delivery before an outage, for recipient deadlines at most `b`. Unlike `SyncRun`,
the cutoff applies to the deadline including the recipient's latest wake, not merely to
the sender's time. A later call still checks an earlier qualifying deadline, but a wake
whose deadline lies after `b` creates no pre-outage delivery obligation. The processing lower
bound and the strict upper bound are those of `SyncOn`. -/
structure SyncBefore (H : Set (Fin P.n)) (ΔF b : Time) : Prop where
  /-- Block processing for nonnegative acceptances or own blocks, with recipient deadline at most
  `b`. -/
  block : ∀ x ∈ H, ∀ i B, tr.AcceptAt x i B ∨ tr.OwnBlockAt x i B → 0 ≤ tr.time i →
    ∀ y ∈ H, ∀ j, tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      tr.BlockDeliveredBy y j (tr.time i) (tr.time i) B

end RunTrace

namespace Compose

open Node

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}

/-- A restart of the AC projection is a restart of the run. -/
theorem projAC_restartAt {y : Fin P.n} {k : Nat} : tr.projAC.RestartAt y k ↔ tr.RestartAt y k :=
  ⟨fun ⟨ℓ, hc, hr⟩ => ⟨ℓ, projAC_callAt.1 hc, hr⟩, fun ⟨ℓ, hc, hr⟩ => ⟨ℓ, projAC_callAt.2 hc, hr⟩⟩

/-- The AC projection's latest wakes are the run's. -/
theorem projAC_lastWake (y : Fin P.n) : tr.projAC.lastWake y = tr.lastWake y := by
  funext k
  induction k with
  | zero =>
    simp only [ACTrace.lastWake, RunTrace.lastWake]
    by_cases hr : tr.RestartAt y 0
    · simp only [projAC_restartAt.2 hr, hr, ↓reduceIte]
      rfl
    · simp [hr, mt projAC_restartAt.1 hr]
  | succ k ih =>
    simp only [ACTrace.lastWake, RunTrace.lastWake, ih]
    by_cases hr : tr.RestartAt y (k + 1)
    · simp only [projAC_restartAt.2 hr, hr, ↓reduceIte]
      rfl
    · simp [hr, mt projAC_restartAt.1 hr]

/-- The AC projection's deadlines are the run's with `Δ`. -/
theorem projAC_deadline (y : Fin P.n) (k : Nat) (τ : Time) :
    tr.projAC.deadline y k τ = tr.deadline y k τ P.Δ := by
  simp only [ACTrace.deadline, RunTrace.deadline, projAC_lastWake]

/-- Project the recipient's timely FG acceptance to its same-time AC block call. -/
theorem acRelay_of_acceptNext {y : Fin P.n} {j : Nat} {B : A.Blk} {ℓ : ACLabel A}
    {σ : Time} (hc : tr.projAC.CallAt y j ℓ) (relay : tr.BlockAcceptedBy y j σ B)
    (next : ∀ k ≤ j, tr.AcceptAt y k B → ∃ ℓ', tr.CallAt y (k + 1) (.ac ℓ') ∧
      ℓ'.call = .block B ∧ tr.time (k + 1) = tr.time k) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k σ := by
  obtain ⟨k, hkj, hk, hlt⟩ := relay
  obtain ⟨ℓ', hc', hb', htk⟩ := next k hkj hk
  have hkj' : k + 1 ≤ j := by
    rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
    · omega
    · cases Option.some.inj (hk.2.symm.trans (projAC_callAt.1 hc).2)
  have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
    cases Option.some.inj (hc'.2.symm.trans hcr.2)
    rw [hb'] at hr
    cases hr
  refine ⟨k + 1, hkj', ⟨ℓ', projAC_callAt.2 hc', hb'⟩, ?_⟩
  rw [projAC_deadline, htk]
  simpa only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] using hlt

/-- **`Sync` projects**: a send or admission of the AC projection is the run's, and its
processing is the run's; an `ac_on_block(B)` follows the FG acceptance of `B` at its time, whose
relay is an acceptance of `B`, followed at once by the AC call of `B` (not a restart, so with the
same deadline). -/
theorem sync_projection : SyncProjection := by
  intro P A dg H sg tr proposer ΔF a b ini h hs
  refine ⟨fun x hx i m hsa hai hib y hy j ℓ hc hdl => ?_,
    fun x hx i B hacc hai hib y hy j ℓ hc hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, projAC_callAt.1 hc₀, by
      rw [projAC_state h hx] at hm
      exact hm⟩
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x hx i m hsa' ⟨hai, hib⟩ y hy j
      ⟨_, projAC_callAt.1 hc⟩ (by rw [← projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, by rw [projAC_deadline]; exact hlt⟩
    rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', projAC_callAt.2 hc', Or.inl hm'⟩, ⟨ℓ', projAC_callAt.2 hc', Or.inr hm'⟩]
  · obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev h hx (projAC_callAt.1 hc₀) hb
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(h.cutLaw y hy j _ (projAC_callAt.1 hc)).1]
      rfl
    apply acRelay_of_acceptNext (σ := tr.time (i' + 1)) hc ?_ (fun _ _ => accept_next h hy)
    rw [← hti]
    exact hs.relay x hx i' B hi' ⟨hti ▸ hai, hti ▸ hib⟩ y hy j ⟨_, projAC_callAt.1 hc⟩
      (by rw [hti, ← projAC_deadline]; exact hdl) (hfr ▸ hanc)

section

open AC

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}

private theorem joined_iff {τ t : Time} (hτ : 0 ≤ τ) :
    (0 < sp.toParams.slotOf t ∧ τ ≤ sp.toParams.slotTime (sp.toParams.slotOf t - 1)) ↔
      τ ≤ sp.ts ((sp.slot t : Int) - 1) := by
  have hΔ := sp.toParams.hΔ
  rcases Nat.eq_zero_or_pos (sp.toParams.slotOf t) with h0 | hpos
  · simp only [ACParams.slot, h0, lt_irrefl, false_and, false_iff, not_le, ACParams.ts]
    push_cast
    linarith
  · rw [sp.slotTime_eq]
    simp only [hpos, true_and, ACParams.ts, ACParams.slot]
    push_cast [Nat.one_le_iff_ne_zero.2 hpos.ne']
    rfl

/-- On the AC slot grid, joining is the previous-slot bound on nonnegative restart cuts. -/
theorem joinedAt_iff_restartCuts {A : NodeAC sp.toParams} {tr : RunTrace A}
    (y : Fin sp.n) (t : Time) (htime : ∀ k, tr.RestartAt y k → 0 ≤ tr.time k) :
    tr.JoinedAt y t ↔
      ∀ k, tr.RestartAt y k → tr.time k ≤ t → tr.time k ≤ sp.ts ((sp.slot t : Int) - 1) := by
  unfold RunTrace.JoinedAt
  exact forall_congr' fun k => imp_congr_right fun hk => imp_congr_right fun _ =>
    joined_iff (htime k hk)

/-- **The run's joined test is the AC projection's**, on a trace whose cuts are at times `≥ 0`. -/
theorem projAC_joinedAt_iff {tr : GoldilocksTrace sp ro} (htime : ∀ k, 0 ≤ tr.time k)
    (y : Fin sp.n) (t : Time) : tr.JoinedAt y t ↔ AC.JoinedAt tr.projAC y t := by
  rw [joinedAt_iff_restartCuts y t (fun k _ => htime k)]
  simp only [AC.JoinedAt, projAC_restartAt]
  rfl

/-- The latest restart time before cut `i`. -/
private noncomputable def lastBefore (tr : GoldilocksTrace sp ro) (y : Fin sp.n) :
    Nat → WithBot Time
  | 0 => ⊥
  | i + 1 => tr.lastWake y i

open Classical in
private theorem lastBefore_succ (tr : GoldilocksTrace sp ro) (y : Fin sp.n) (i : Nat) :
    lastBefore tr y (i + 1) =
      if tr.RestartAt y i then (tr.time i : WithBot Time) else lastBefore tr y i := by
  cases i <;> rfl

private theorem lastBefore_le {dg} {H} {tr : GoldilocksTrace sp ro}
    {ini} (h : GoldilocksRun proposer dg H tr ini)
    (y : Fin sp.n) (x : Time) :
    ∀ i, lastBefore tr y i ≤ x ↔ ∀ k < i, tr.RestartAt y k → tr.time k ≤ x := by
  intro i
  induction i with
  | zero => simp [lastBefore]
  | succ i ih =>
    rw [lastBefore_succ]
    split_ifs with hr
    · refine ⟨fun hx k hk hk' => ?_, fun hall => WithBot.coe_le_coe.2 (hall i (by omega) hr)⟩
      exact (h.time_mono (show k ≤ i by omega)).trans (WithBot.coe_le_coe.1 hx)
    · rw [ih]
      refine ⟨fun hall k hk hk' => ?_, fun hall k hk => hall k (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      exacts [hall k hk hk', absurd hk' hr]

private theorem restartTime_eq {dg} {H} {tr : GoldilocksTrace sp ro}
    {ini} (h : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) : ∀ i, (tr.state y i).ac.restartTime = lastBefore tr y i := by
  intro i
  induction i with
  | zero =>
    obtain ⟨m, hm⟩ := AC.voteStart_iff.1 (h.vstart y)
    rw [Trace.state, h.init y hy]
    simp only [Node.initWith, hm]
    rfl
  | succ i ih =>
    rw [lastBefore_succ, ← ih]
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      have hlaw := h.cutLaw y hy i c hc
      rw [tr.state_succ_of_call hc]
      cases c with
      | ac ℓ =>
        have hpost : (tr.post i).ac = ((goldilocksNode sp ro).step y (tr.state y i).ac ℓ.frame
            (tr.time i) ℓ.call).1 := (congrArg Prod.fst hlaw.2.1).symm
        rw [hpost]
        split_ifs with hR
        · obtain ⟨ℓ', hℓ', hr⟩ := hR
          cases Option.some.inj (hc.2.symm.trans hℓ'.2)
          rw [hr]
          have hΦ : FrameOK ℓ.frame := hlaw.1 ▸
            (Store.frame_realization _ _ _ _ (fg_reachable h.toLocalRun hy i)).1
          exact (restart_state sp _ ro y _ ℓ.frame (tr.time i) hΦ
            (h.time_nonneg i)).2.2.2.2.2.2.1
        · exact step_restartTime y _ _ _ _ fun hr => hR ⟨ℓ, hc, hr⟩
      | fg ℓ =>
        split_ifs with hR
        · obtain ⟨ℓ', hℓ', _⟩ := hR
          cases Option.some.inj (hc.2.symm.trans hℓ'.2)
        congr 1
        cases ℓ with
        | block B acc =>
          cases acc
          · rw [hlaw.2]
          · exact hlaw.2.2.1
        | attestation a => exact hlaw.2.1
        | attest C s =>
          cases s
          · rw [hlaw.2]
          · exact hlaw.2.2
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      split_ifs with hR
      · obtain ⟨ℓ, hℓ, _⟩ := hR
        exact absurd ⟨_, hℓ⟩ hc
      · rfl

/-- **Joining and participation project**: a restart of the run is a restart of the AC
projection, and the run's joined test (with `0 < slot(t)`) is the AC's on restart times `≥ 0`;
the AC state's `restart_time` at a call is the time of the latest restart before it (a restart
sets it, every other call keeps it), and the restarts at or before the time of a call other than
a restart are the ones before it (restarts come first at a time). From starts up to the vote
permission. -/
theorem joined_projection_from {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ini} (h : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) (t : Time) :
    (tr.JoinedAt y t ↔ AC.JoinedAt tr.projAC y t) ∧
      (∀ i, tr.IsCall y i → ¬ tr.RestartAt y i → tr.time i = t →
        (tr.JoinedAt y t ↔ AC.joined sp (tr.state y i).ac t)) ∧
      tr.honestAwakeJoined H t = AC.honestAwakeJoined tr.projAC H t := by
  have hpt : ∀ z, (tr.JoinedAt z t ↔ AC.JoinedAt tr.projAC z t) := fun z =>
    projAC_joinedAt_iff h.time_nonneg z t
  refine ⟨hpt y, fun i hi hnr hit => ?_, ?_⟩
  · -- the restarts at or before `t` are the restarts before `i`
    have hset : ∀ k, tr.RestartAt y k → (tr.time k ≤ t ↔ k < i) := by
      intro k hk
      refine ⟨fun hkt => ?_, fun hki => hit ▸ h.time_mono hki.le⟩
      by_contra hik
      rcases Nat.lt_or_eq_of_le (not_lt.1 hik) with hik | rfl
      · obtain ⟨j, e, hj, hg, hp⟩ := group_not_restart h.toLocalRun hy hi hnr
        have htk : tr.time k = t := le_antisymm hkt (hit ▸ h.time_mono hik.le)
        have hgk := restartCall_group h.toLocalRun hy hk
        rw [htk] at hgk
        rw [hit] at hg
        have : e.phase ≤ 0 := h.phase_order y hy y hy j k t e .restart hg hgk (by omega) (.inl rfl)
        omega
      · exact hnr hk
    unfold AC.joined
    rw [joinedAt_iff_restartCuts y t (fun k _ => h.time_nonneg k), restartTime_eq h hy,
      lastBefore_le h]
    exact ⟨fun hj k hki hk => hj k hk ((hset k hk).2 hki),
      fun hj k hk hkt => hj k ((hset k hk).1 hkt) hk⟩
  · unfold RunTrace.honestAwakeJoined AC.honestAwakeJoined
    congr 1
    ext z
    exact Iff.rfl.and (Iff.rfl.and (hpt z))

/-- **Joining and participation project**: `joined_projection_from` at the initial starts. -/
theorem joined_projection : JoinedProjection :=
  fun _ _ _ _ _ _ h _ hy t => joined_projection_from h hy t

end

end Compose

end Consensus.Goldilocks

end
