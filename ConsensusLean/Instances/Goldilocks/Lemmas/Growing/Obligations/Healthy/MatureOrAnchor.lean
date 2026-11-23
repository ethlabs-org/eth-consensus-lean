module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReadContextDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentChecks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Mature record or anchor coverage under growing faults

The mature-or-anchor dichotomy under growing faults: at a read point after the
repair window, the reader's looked-up record is below its anchor or below a mature result of a
node honest at its own cut. The reader is honest at its read time; its earlier updates at labels
past the join, due by its read time and strictly before its read cut, are a premise (`hupd`),
which an engine read discharges from the stored clock. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The reader's frame at a cut `k` whose earlier cuts are by its read time `t` is well formed,
inside the blocks held while honest, and its AC state is its trace AC state. -/
private theorem frame_by_read (D : RepairSchedule tr H proposer dg g b cm βK)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t) :
    FrameOK (Node.frame (tr.state y k)) ∧
      (Node.frame (tr.state y k)).tree ⊆ tr.HonestBlocksAt H ∧
      (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H ∧
      AC.LocksWF sp (tr.state y k).ac.locks := by
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hst : (tr.upTo t).state y k = tr.state y k := Trace.upTo_state tr y hle
  refine ⟨(Store.frame_realization _ _ _ _
      (Healing.Growing.fg_reachable_at hrun ht hle hy)).1,
    fun X hX => ⟨y, k, t, ht, hle, hy, hX.1⟩, fun X hX => ⟨y, k, t, ht, hle, hy, hX⟩, ?_⟩
  have h := Compose.locksWF_state (hrun.upTo ht) (hnc.upTo t) hy k
  rwa [hst] at h

/-- The repair opening of a schedule is after the drain and the join, and before the read time of
a context. -/
private theorem opening_before_read (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t) :
    Healing.drainTime sp D.resetTime ≤ sp.ts O.slot ∧
      AC.gbar g + 4 * sp.Δ ≤ sp.ts O.slot ∧
      sp.ts O.slot + 6 * sp.Δ ≤ t ∧ sp.ts O.slot + 6 * sp.Δ < tr.time n ∧
      sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts O.slot := by
  exact ⟨O.drain, O.late, C.repaired, C.repairedCut, repair_opening_join D O⟩

/-- **Actual anchor coverage or a mature raw witness**, at a read point after the repair window.
Young optimistic writers retain their normalized lock until the next-result deadline; older ones
reach the next result or finalization at the reader's update of the next label. -/
theorem healthy_current_mature_or_anchor_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t)
    (hupd : ∀ u : Nat, sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u →
      sp.ts u + 6 * sp.Δ ≤ t → sp.ts u + 6 * sp.Δ < tr.time n →
      ∃ j ell, AC.UpdateAt tr.projAC y j u ell ∧ j < n)
    {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed =
      some R) :
    (Node.frame (tr.state y n)).Anc R
        (AC.getAnchor sp (tr.state y n).ac (Node.frame (tr.state y n)) t) ∨
      ∃ x r s B CV, x ∈ H (tr.time r) ∧ AC.ResultAt tr.projAC x r s B CV ∧
        Anc (tr.HonestBlocksAt H) R B ∧ tr.time r ≤ b ∧
        Healing.cutZ sp.toParams g ≤ sp.ts s ∧
        D.cleanLabel + 2 * sp.k + 1 ≤ s ∧ s < C.label := by
  let U := tr.HonestBlocksAt H
  let Phi := Node.frame (tr.state y n)
  have hΔ := sp.toParams.hΔ
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have ht0 := C.time_nonneg
  have hnt := C.readPoint.1
  have htb := C.time_bound
  have hy := C.honest
  have hkeys : ∀ {r : Nat}, tr.time r ≤ t → y ∈ H (tr.time r) :=
    fun hr => hrun.antitone hr hy
  obtain ⟨hPhi, hsub, hsubfg, -⟩ := frame_by_read D ht0 hnt hy
  obtain ⟨hdrain, hgu, hTt, hTn, hjoin⟩ := opening_before_read D C
  obtain ⟨hRm, -⟩ := AC.lookup_eq_some hR
  have hchain := healthy_current_live_chain_at D C
  have hfc := (AC.anc_getAnchor hPhi hchain).2 _ (Or.inr rfl)
  have hfinal : Anc U R (tr.state y n).fg.F →
      Phi.Anc R (AC.getAnchor sp (tr.state y n).ac Phi t) := by
    intro hRF
    exact (AC.anc_tree_of_anc_U hU hPhi hsub hRm hRF hPhi.rooted.1).trans
      (hPhi.F_anc_fcRoot.trans hfc)
  by_cases hgen : R.root = sp.genesisRoot
  · left
    apply hfinal
    have htree := Store.accepted_tree _ _ _ _ (Healing.Growing.fg_reachable_at hrun ht0 hnt hy)
    have heq : R = sp.toParams.genesisBlock
        (goldilocksNode sp ro).genesisPayload :=
      htree.2.1.1 hRm.1 htree.2.2.1 hgen
    rw [heq]
    exact (htree.2.2.2 _ hPhi.rooted.1.1).mono hsubfg
  have hTb := hTt.trans htb
  obtain ⟨d, ellD, hup, hdn⟩ := hupd O.slot hjoin hTt hTn
  obtain ⟨q, hqn, ell, hcall, hRq, hrest, hwriter⟩ :=
    last_record_writer_at hrun hnc ht0 hnt hy hR hgen
  have hqt : tr.time q ≤ t := hnt q hqn
  have hqb := hqt.trans htb
  have hyq := hkeys hqt
  have hslotq := retained_writer_slot_after_update_at D.reset O.held rfl O.proposes O.label
    hdrain hgu hTb ht0 hnt hy hup hdn hR hcall hRq hrest
  have hRqfg : R ∈ (tr.state y q).fg.tree :=
    ((Compose.Growing.frame_of_projAC_at hrun hyq hcall ▸ hRq).1)
  have hframe : ∀ e, q ≤ e → e ≤ n → R ∈ (Node.frame (tr.state y e)).tree :=
    fun e hqe hen => writer_mem_frame_between_at hrun hnc ht0 hnt hy hqe hen hRqfg hRm
  have hraw : ∀ (x : Fin sp.n) (r s : Nat) B CV, x ∈ H (tr.time r) →
      AC.ResultAt tr.projAC x r s B CV → Anc U R B →
      tr.time r ≤ t → D.cleanLabel + 2 * sp.k + 1 ≤ s →
      ∃ x r s B CV, x ∈ H (tr.time r) ∧ AC.ResultAt tr.projAC x r s B CV ∧
        Anc (tr.HonestBlocksAt H) R B ∧ tr.time r ≤ b ∧
        Healing.cutZ sp.toParams g ≤ sp.ts s ∧
        D.cleanLabel + 2 * sp.k + 1 ≤ s ∧ s < C.label := by
    intro x r s B CV hx hres hRB hrt hs
    have htime : tr.time r = sp.ts s + 6 * sp.Δ :=
      hres.choose_spec.1.2.2.1
    have hlatest := Obligations.result_label_lt_latest_of_time ht0 (htime ▸ hrt)
      (A := (tr.state y n).ac) (Φ := Phi)
    rw [← C.latest] at hlatest
    have hclean : Healing.cleanLabel sp D.resetTime + sp.k + 2 ≤ s := by
      rw [D.cleanLabel_eq] at hs
      have := sp.two_le_k
      omega
    have hwindow : (s : Int) - sp.k < s :=
      sub_lt_self _ (Int.natCast_pos.mpr (Nat.zero_lt_two.trans_le sp.two_le_k))
    exact ⟨x, r, s, B, CV, hx, hres, hRB, hrt.trans htb,
      D.reset.clean_window_timing_at hclean s hwindow, hs, by exact_mod_cast hlatest⟩
  rcases hwriter with ⟨s, CV, hres⟩ | ⟨⟨CV, hop⟩, hlock⟩
  · right
    have htime : tr.time q = sp.ts s + 6 * sp.Δ :=
      hres.choose_spec.1.2.2.1
    have hslot : sp.slot (tr.time q) = s + 1 := by
      rw [htime]
      apply AC.slot_of_mem sp (s + 1) <;>
        simp only [AC.ACParams.ts] <;> push_cast <;> linarith only [hΔ]
    apply hraw y q s R CV hyq hres .refl hqt
    rw [hslot] at hslotq
    exact Nat.lt_succ_iff.mp (D.old_bound.trans_lt (O.old_lt.trans_le hslotq))
  · let s := sp.slot (tr.time q)
    have hs : D.cleanLabel + 2 * sp.k + 1 ≤ s :=
      D.old_bound.trans (O.old_lt.le.trans hslotq)
    have hsc : Healing.cleanLabel sp D.resetTime + 2 * sp.k + 1 ≤ s := by
      simpa only [D.cleanLabel_eq] using hs
    have hcand : ∀ e, q ≤ e → e ≤ n → (Node.frame (tr.state y e)).AncestorCandidate R :=
      clean_optimistic_writer_candidate_interval_at D.reset ht0 hnt htb hy hop hsc hqn hRm
    by_cases hyoung : t ≤ sp.ts (s + 1 : Nat) + 6 * sp.Δ
    · left
      have hle1 : ∀ k < q + 1, tr.time k ≤ t := fun k hk => hnt k (by omega)
      have hnorm : ell.frame.viableAncestor R = R := by
        rw [Compose.Growing.frame_of_projAC_at hrun hyq hcall]
        exact AC.viableAncestor_self (frame_by_read D ht0 (fun k hk => hnt k (by omega))
          hy).1 (hframe q le_rfl hqn.le) (hcand q le_rfl hqn.le).symm
      rw [hnorm] at hlock
      obtain ⟨e, hlock⟩ := hlock
      have he := (frame_by_read D ht0 hle1 hy).2.2.2.floor hlock
      have hl := young_optimistic_lock_persists_at D.reset hyq hop hsc hqb hqn hnt htb ht0 hy
        hyoung he hlock (fun e hqe hen => ⟨hframe e (Nat.le_of_succ_le hqe) hen.le,
          hcand e (Nat.le_of_succ_le hqe) hen.le⟩)
      apply Obligations.record_below_anchor_of_stored_live_lock hPhi hl hRm rfl ?_ ?_ hchain
      · have hfloor := (AC.ts_le_iff_le_slot sp ht0 (sp.slot t)).2 le_rfl
        simp only [AC.ACParams.ts] at hfloor hyoung
        push_cast at hyoung
        change sp.slot t ≤ e
        change s + 2 ≤ e at he
        by_contra h
        have : (s : Int) + 3 ≤ sp.slot t := by
          exact_mod_cast he.trans_lt (Nat.lt_of_not_le h)
        linarith only [mul_le_mul_of_nonneg_left this
          (by linarith only [hΔ] : (0 : Time) ≤ 4 * sp.Δ), hfloor, hyoung, hΔ]
      · rw [AC.viableAncestor_self hPhi hRm (hcand n hqn.le le_rfl).symm]
        exact .refl
    · have hnext : sp.ts (s + 1 : Nat) + 6 * sp.Δ < t := lt_of_not_ge hyoung
      have hjoinNext : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤
          sp.ts (s + 1 : Nat) :=
        hjoin.trans ((AC.ts_le_iff sp).2 (by exact_mod_cast hslotq.trans (Nat.le_succ _)))
      obtain ⟨j, ellJ, hu, hjn⟩ := hupd (s + 1) hjoinNext hnext.le (hnext.trans_le C.readPoint.2)
      have hjt : tr.time j = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
      have hjb := hjt ▸ hnext.le.trans htb
      have hRnext : Healing.drainTime sp D.resetTime ≤ sp.ts (s + 1 + 1 : Nat) := by
        rw [Healing.drainTime_eq]
        apply (AC.ts_le_iff sp).2
        have hs' := hsc
        rw [Healing.cleanLabel_eq] at hs'
        exact_mod_cast (show sp.slot D.resetTime + 2 * sp.k + 5 ≤
          s + 1 + 1 by omega)
      rcases optimistic_result_or_finalized_at_update_at D.reset hyq (hkeys (hnt j hjn)) hop
          hsc hqb hu hjb hRnext with hRF | ⟨B, DV, hres, hRB⟩
      · left
        apply hfinal
        exact hRF.trans (hrun.toLocalRun.finalized_mono_on_prefix ht0 hy hjn.le hnt)
      · right
        exact hraw y j (s + 1) B DV (hkeys (hnt j hjn)) hres hRB (hjt ▸ hnext.le)
          (hs.trans (Nat.le_succ s))

end Consensus.Goldilocks.Obligations.Growing

end
