module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReadContextDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentChecks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Opening
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

The growing form of `Obligations.healthy_current_mature_or_anchor`: at a read point after the
repair window, the reader's looked-up record is below its anchor or below a mature result of a
node honest at its own cut. The reader is honest at its read time; its earlier updates at labels
past the join are a premise (`hupd`), which an engine read discharges from the stored clock. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The reader's frame at a cut `k` whose earlier cuts are by its read time `t` is well formed,
inside the blocks held while honest, and its AC state is its trace AC state. -/
private theorem frame_by_read (Q : HealthyPreparationQueryAt S A V) {y : Fin Q.params.n}
    {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, Q.trace.time q ≤ t) (hy : y ∈ Q.keys t) :
    FrameOK (Node.frame (Q.trace.state y k)) ∧
      (Node.frame (Q.trace.state y k)).tree ⊆ Q.trace.HonestBlocksAt Q.keys ∧
      (Q.trace.state y k).fg.tree ⊆ Q.trace.HonestBlocksAt Q.keys ∧
      SA.LocksWF Q.params (Q.trace.state y k).ac.locks := by
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hst : (Q.trace.upTo t).state y k = Q.trace.state y k := Trace.upTo_state Q.trace y hle
  refine ⟨(Store.frame_realization _ _ _ _
      (Healing.Growing.fg_reachable_at hrun ht hle hy)).1,
    fun X hX => ⟨y, k, t, ht, hle, hy, hX.1⟩, fun X hX => ⟨y, k, t, ht, hle, hy, hX⟩, ?_⟩
  have h := Compose.locksWF_state (hrun.upTo ht) (hnc.upTo t) hy k
  rwa [hst] at h

/-- The repair opening of a schedule is after the drain and the join, and before the read time of
a context. -/
private theorem opening_before_read (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) (O : HealthyRepairOpeningAt S A V Q D)
    {y : Fin Q.params.n} {n : Nat} {t : Time} (C : HealthyReadContextAt S A V Q D y n t) :
    Healing.drainTime Q.params D.resetTime ≤ Q.params.ts O.slot ∧
      SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts O.slot ∧
      Q.params.ts O.slot + 6 * Q.params.Δ < t ∧
      Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤ Q.params.ts O.slot := by
  have hlow := D.lower
  simp only [max_le_iff] at hlow
  obtain ⟨-, hdr, -, hgr, -⟩ := hlow
  have hT : Q.params.ts O.slot + 6 * Q.params.Δ < t := by
    refine lt_of_le_of_lt ?_ C.repaired
    rw [add_mul, ← add_assoc]
    exact add_le_add O.bounded le_rfl
  have hgu := hgr.trans O.fresh.le
  refine ⟨hdr.trans O.fresh.le, hgu, hT, ?_⟩
  have hbase := (SA.ts_le_iff_le_slot Q.params (SA.gbar_nonneg Q.gst)
    (Q.params.slot (SA.gbar Q.gst))).mpr le_rfl
  simp only [SA.SAParams.ts] at hbase hgu ⊢
  push_cast at hbase hgu ⊢
  linarith only [hbase, hgu]

set_option linter.unusedVariables false in
-- The statement keeps the static `hrepair`; the operational opening gives the writer fact.
/-- **Actual anchor coverage or a mature raw witness**, at a read point after the repair window.
Young optimistic writers retain their normalized lock until the next-result deadline; older ones
reach the next result or finalization at the reader's update of the next label. -/
theorem healthy_current_mature_or_anchor_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (D : HealthyRepairScheduleAt S A V Q) (O : HealthyRepairOpeningAt S A V Q D)
    (hrepair : HealthyReceiverRepairAt S A V Q D O) {y : Fin Q.params.n} {n : Nat} {t : Time}
    (C : HealthyReadContextAt S A V Q D y n t)
    (hupd : ∀ u : Nat, Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤ Q.params.ts u →
      Q.params.ts u + 6 * Q.params.Δ ≤ t → ∃ j ell, SA.UpdateAt Q.trace.projAC y j u ell ∧ j < n)
    {R : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : SA.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed =
      some R) :
    (Node.frame (Q.trace.state y n)).Anc R
        (SA.getAnchor Q.params (Q.trace.state y n).ac (Node.frame (Q.trace.state y n)) t) ∨
      ∃ x r s B CV, x ∈ Q.keys (Q.trace.time r) ∧ SA.ResultAt Q.trace.projAC x r s B CV ∧
        Anc (Q.trace.HonestBlocksAt Q.keys) R B ∧ Q.trace.time r ≤ Q.run.2.horizon ∧
        Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s ∧
        D.cleanLabel + 2 * Q.params.k + 1 ≤ s ∧ s < C.label := by
  let U := Q.trace.HonestBlocksAt Q.keys
  let Phi := Node.frame (Q.trace.state y n)
  have hΔ := Q.params.toParams.hΔ
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hc := healthy_repair_catch_at S A V Q
  have ht0 := C.time_nonneg
  have hnt := C.readPoint.1
  have htb := C.time_bound
  have hy := C.honest
  have hkeys : ∀ {r : Nat}, Q.trace.time r ≤ t → y ∈ Q.keys (Q.trace.time r) :=
    fun hr => honestKeysAt_antitone S Q.run.2 hr hy
  obtain ⟨hPhi, hsub, hsubfg, -⟩ := frame_by_read S A V Q ht0 hnt hy
  obtain ⟨hdrain, hgu, hTt, hjoin⟩ := opening_before_read S A V Q D O C
  obtain ⟨hRm, -⟩ := SA.lookup_eq_some hR
  have hchain := healthy_current_live_chain_at S A V Q D C
  have hfc := (SA.anc_getAnchor hPhi hchain).2 _ (Or.inr rfl)
  have hfinal : Anc U R (Q.trace.state y n).fg.F →
      Phi.Anc R (SA.getAnchor Q.params (Q.trace.state y n).ac Phi t) := by
    intro hRF
    exact (SA.anc_tree_of_anc_U hU hPhi hsub hRm hRF hPhi.rooted.1).trans
      (hPhi.F_anc_fcRoot.trans hfc)
  by_cases hgen : R.root = Q.params.genesisRoot
  · left
    apply hfinal
    have htree := Store.accepted_tree _ _ _ _ (Healing.Growing.fg_reachable_at hrun ht0 hnt hy)
    have heq : R = Q.params.toParams.genesisBlock
        (goldilocksNode Q.params (S.ro _)).genesisPayload :=
      htree.2.1.1 hRm.1 htree.2.2.1 hgen
    rw [heq]
    exact (htree.2.2.2 _ hPhi.rooted.1.1).mono hsubfg
  have hTb := hTt.le.trans htb
  obtain ⟨d, ellD, hup, hdn⟩ := hupd O.slot hjoin hTt.le
  obtain ⟨q, hqn, ell, hcall, hRq, hrest, hwriter⟩ :=
    last_record_writer_at hrun hnc ht0 hnt hy hR hgen
  have hqt : Q.trace.time q ≤ t := hnt q hqn
  have hqb := hqt.trans htb
  have hyq := hkeys hqt
  have hslotq := retained_writer_slot_after_update_at D.reset hc O.held rfl O.proposes O.label
    hdrain hgu hTb ht0 hnt hy hup hdn hR hcall hRq hrest
  have hRqfg : R ∈ (Q.trace.state y q).fg.tree :=
    ((Compose.Growing.frame_of_projAC_at hrun hyq hcall ▸ hRq).1)
  have hframe : ∀ e, q ≤ e → e ≤ n → R ∈ (Node.frame (Q.trace.state y e)).tree :=
    fun e hqe hen => writer_mem_frame_between_at hrun hnc ht0 hnt hy hqe hen hRqfg hRm
  have hraw : ∀ (x : Fin Q.params.n) (r s : Nat) B CV, x ∈ Q.keys (Q.trace.time r) →
      SA.ResultAt Q.trace.projAC x r s B CV → Anc U R B →
      Q.trace.time r ≤ t → D.cleanLabel + 2 * Q.params.k + 1 ≤ s →
      ∃ x r s B CV, x ∈ Q.keys (Q.trace.time r) ∧ SA.ResultAt Q.trace.projAC x r s B CV ∧
        Anc (Q.trace.HonestBlocksAt Q.keys) R B ∧ Q.trace.time r ≤ Q.run.2.horizon ∧
        Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s ∧
        D.cleanLabel + 2 * Q.params.k + 1 ≤ s ∧ s < C.label := by
    intro x r s B CV hx hres hRB hrt hs
    have htime : Q.trace.time r = Q.params.ts s + 6 * Q.params.Δ :=
      hres.choose_spec.1.2.2.1
    have hlatest := Obligations.result_label_lt_latest_of_time ht0 (htime ▸ hrt)
      (A := (Q.trace.state y n).ac) (Φ := Phi)
    rw [← C.latest] at hlatest
    have hclean : Healing.cleanLabel Q.params D.resetTime + Q.params.k + 2 ≤ s := by
      rw [D.cleanLabel_eq] at hs
      have := Q.params.two_le_k
      omega
    have hwindow : (s : Int) - Q.params.k < s :=
      sub_lt_self _ (Int.natCast_pos.mpr (Nat.zero_lt_two.trans_le Q.params.two_le_k))
    exact ⟨x, r, s, B, CV, hx, hres, hRB, hrt.trans htb,
      D.reset.clean_window_timing_at hclean s hwindow, hs, by exact_mod_cast hlatest⟩
  rcases hwriter with ⟨s, CV, hres⟩ | ⟨⟨CV, hop⟩, hlock⟩
  · right
    have htime : Q.trace.time q = Q.params.ts s + 6 * Q.params.Δ :=
      hres.choose_spec.1.2.2.1
    have hslot : Q.params.slot (Q.trace.time q) = s + 1 := by
      rw [htime]
      apply SA.slot_of_mem Q.params (s + 1) <;>
        simp only [SA.SAParams.ts] <;> push_cast <;> linarith only [hΔ]
    apply hraw y q s R CV hyq hres .refl hqt
    rw [hslot] at hslotq
    exact Nat.lt_succ_iff.mp (D.old_bound.trans_lt (O.old_lt.trans_le hslotq))
  · let s := Q.params.slot (Q.trace.time q)
    have hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s :=
      D.old_bound.trans (O.old_lt.le.trans hslotq)
    have hsc : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 1 ≤ s := by
      simpa only [D.cleanLabel_eq] using hs
    have hcand : ∀ e, q ≤ e → e ≤ n → (Node.frame (Q.trace.state y e)).AncestorCandidate R :=
      clean_optimistic_writer_candidate_interval_at D.reset hc ht0 hnt htb hy hop hsc hqn hRm
    by_cases hyoung : t < Q.params.ts (s + 1 : Nat) + 6 * Q.params.Δ
    · left
      have hle1 : ∀ k < q + 1, Q.trace.time k ≤ t := fun k hk => hnt k (by omega)
      have hnorm : ell.frame.viableAncestor R = R := by
        rw [Compose.Growing.frame_of_projAC_at hrun hyq hcall]
        exact SA.viableAncestor_self (frame_by_read S A V Q ht0 (fun k hk => hnt k (by omega))
          hy).1 (hframe q le_rfl hqn.le) (hcand q le_rfl hqn.le).symm
      rw [hnorm] at hlock
      obtain ⟨e, hlock⟩ := hlock
      have he := (frame_by_read S A V Q ht0 hle1 hy).2.2.2.floor hlock
      have hl := young_optimistic_lock_persists_at D.reset hc hyq hop hsc hqb hqn hnt htb ht0 hy
        hyoung he hlock (fun e hqe hen => ⟨hframe e (Nat.le_of_succ_le hqe) hen.le,
          hcand e (Nat.le_of_succ_le hqe) hen.le⟩)
      apply Obligations.record_below_anchor_of_stored_live_lock hPhi hl hRm rfl ?_ ?_ hchain
      · have hfloor := (SA.ts_le_iff_le_slot Q.params ht0 (Q.params.slot t)).2 le_rfl
        simp only [SA.SAParams.ts] at hfloor hyoung
        push_cast at hyoung
        change Q.params.slot t ≤ e
        change s + 2 ≤ e at he
        by_contra h
        have : (s : Int) + 3 ≤ Q.params.slot t := by
          exact_mod_cast he.trans_lt (Nat.lt_of_not_le h)
        linarith only [mul_le_mul_of_nonneg_left this
          (by linarith only [hΔ] : (0 : Time) ≤ 4 * Q.params.Δ), hfloor, hyoung, hΔ]
      · rw [SA.viableAncestor_self hPhi hRm (hcand n hqn.le le_rfl).symm]
        exact .refl
    · have hnext : Q.params.ts (s + 1 : Nat) + 6 * Q.params.Δ ≤ t := le_of_not_gt hyoung
      have hjoinNext : Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤
          Q.params.ts (s + 1 : Nat) :=
        hjoin.trans ((SA.ts_le_iff Q.params).2 (by exact_mod_cast hslotq.trans (Nat.le_succ _)))
      obtain ⟨j, ellJ, hu, hjn⟩ := hupd (s + 1) hjoinNext hnext
      have hjt : Q.trace.time j = Q.params.ts (s + 1 : Nat) + 6 * Q.params.Δ := hu.2.2.1
      have hjb := hjt ▸ hnext.trans htb
      have hRnext : Healing.drainTime Q.params D.resetTime ≤ Q.params.ts (s + 1 + 1 : Nat) := by
        rw [Healing.drainTime_eq]
        apply (SA.ts_le_iff Q.params).2
        have hs' := hsc
        rw [Healing.cleanLabel_eq] at hs'
        exact_mod_cast (show Q.params.slot D.resetTime + 2 * Q.params.k + 5 ≤
          s + 1 + 1 by omega)
      rcases optimistic_result_or_finalized_at_update_at D.reset hc hyq (hkeys (hnt j hjn)) hop
          hsc hqb hu hjb hRnext with hRF | ⟨B, DV, hres, hRB⟩
      · left
        apply hfinal
        have hFN := Healing.run_F_mono (hrun.upTo ht0).toLocalRun hy hjn.le
        rw [Trace.upTo_state Q.trace y (fun k hk => hnt k (by omega)),
          Trace.upTo_state Q.trace y hnt] at hFN
        exact hRF.trans (hFN.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono ht0))
      · right
        exact hraw y j (s + 1) B DV (hkeys (hnt j hjn)) hres hRB (hjt ▸ hnext)
          (hs.trans (Nat.le_succ s))

end Consensus.Goldilocks.Obligations.Growing

end
