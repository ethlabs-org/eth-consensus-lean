module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReadContextDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedRead
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.StoredLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SourceOrigin
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.StoredSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResultLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.ResultDomain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FloorSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.SeedCandidate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor

public section

/-! # The current-read checks of healed safety under growing faults

The healed-safety checks on a reader's current state at a read point after the
repair window (`RepairReadContext`), with the reader honest at its read time and every source
writer honest at its own cut:

* `healthy_current_live_candidates_at`: the reader's live lock blocks and fork-choice root are
  compatible with its looked-up record;
* `healthy_current_record_viable_at`: a looked-up record not below the fork-choice root is
  viable;
* `healthy_current_vote_domain_of_quarantine_at`, `healthy_current_stored_locks_at`: the
  vote-domain and stored-lock arms of a recent actual result;
* `healthy_current_live_chain_at`: the reader's live lock blocks are pairwise compatible.

The record's clean source comes from the receiver repair
(`record_sources_before_now_at`) and the reset seed from
`reset_seed_held_at_read_at`. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

section Repair

variable {sp : AC.ACParams}
  {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The reader's frame at a read point of its context is well formed, inside the blocks held while
honest, and its AC state is its trace AC state. -/
private theorem read_frame (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t) :
    FrameOK (Node.frame (tr.state y n)) ∧
      (Node.frame (tr.state y n)).tree ⊆ tr.HonestBlocksAt H ∧
      tr.projAC.state y n = (tr.state y n).ac ∧
      AC.LocksWF sp (tr.state y n).ac.locks := by
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have ht := C.time_nonneg
  have hle := C.readPoint.1
  have hst : (tr.upTo t).state y n = tr.state y n := Trace.upTo_state tr y hle
  refine ⟨(Store.frame_realization _ _ _ _
      (Healing.Growing.fg_reachable_at hrun ht hle C.honest)).1,
    fun X hX => ⟨y, n, t, ht, hle, C.honest, hX.1⟩, ?_, ?_⟩
  · have h := Compose.projAC_state (hrun.upTo ht).toLocalRun C.honest n
    rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y hle, hst] at h
  · have h := Compose.locksWF_state (hrun.upTo ht) (hnc.upTo t) C.honest n
    rwa [hst] at h

/-- The repair opening of a schedule is before the read time of a context, after the drain. -/
private theorem read_opening (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t) :
    Healing.drainTime sp D.resetTime ≤ sp.ts O.slot ∧
      AC.gbar g + 4 * sp.Δ ≤ sp.ts O.slot ∧
      sp.ts O.slot + 6 * sp.Δ ≤ t ∧ sp.ts O.slot + 6 * sp.Δ < tr.time n ∧
      Healing.drainTime sp D.resetTime ≤ t := by
  have hΔ := sp.toParams.hΔ
  have hT := C.repaired
  refine ⟨O.drain, O.late, hT, C.repairedCut, ?_⟩
  linarith only [O.drain, hT, hΔ]

/-- **Current anchor candidates are compatible with the current looked-up record**: the reader's
live lock blocks and its fork-choice root, at a read point after the repair window. -/
theorem healthy_current_live_candidates_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t)
    {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed =
      some R) :
    ∀ X ∈ AC.liveLockBlocks sp (tr.state y n).ac.locks (Node.frame (tr.state y n))
        t ∪ {(Node.frame (tr.state y n)).fcRoot},
      Goldilocks.Compatible (Node.frame (tr.state y n)).tree X R := by
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨hPhi, hsub, hst, hwf⟩ := read_frame D C
  obtain ⟨hdrain, hgu, hbefore, hcut, hdrainNow⟩ := read_opening D C
  have hRm := (AC.lookup_eq_some hR).1
  have hcover := record_sources_before_now_at D O C.readPoint C.honest C.repaired
    C.repairedCut
  rw [hR, Option.getD_some, recordCover_iff] at hcover
  rcases hcover with hF | ⟨x, q, s, B, CV, hx, -, hqt, hs, hsrc, hRB⟩
  · -- the record is the finalized block, below every block of the frame
    intro X hX
    have hFX : (Node.frame (tr.state y n)).Anc R X := by
      rw [hF]
      rcases hX with hX | hX
      · exact hPhi.rooted.2 X hX.1
      · rw [Set.mem_singleton_iff.mp hX]
        exact hPhi.F_anc_fcRoot
    exact Or.inr hFX
  have hqb := hqt.trans C.time_bound
  have hs' : Healing.cleanLabel sp D.resetTime + 2 * sp.k + 1 ≤ s := by
    rw [← D.cleanLabel_eq]; exact hs
  intro X hX
  rcases hX with hX | hX
  · obtain ⟨l, hl, E, hE, hEr, hlive, rfl⟩ := AC.mem_liveLockBlocks_of_wf hPhi hwf hX
    rw [← hst] at hl
    have hBE := D.reset.clean_source_stored_lock_compatible_at hx C.time_nonneg
      C.readPoint.1 C.honest C.time_bound hsrc hs' hqb hl
      (Healing.drain_stored_lock_label hdrainNow hlive) (hsub hE) hEr
    have hXE := (AC.viableAncestor_anc hPhi hE).2.mono hsub
    have hXR := tips_comparable_of_origin_witnesses_at hU hXE hRB hBE.symm
    rcases hXR with h | h
    · exact Or.inl (AC.anc_tree_of_anc_U hU hPhi hsub hX.1 h hRm)
    · exact Or.inr (AC.anc_tree_of_anc_U hU hPhi hsub hRm h hX.1)
  · obtain rfl := Set.mem_singleton_iff.mp hX
    obtain ⟨z, r, l, S₀, hseed, hrb, -, -, hhold⟩ :=
      D.reset.reset_seed_held_at_read_at C.readPoint C.time_bound C.honest hdrain hgu hbefore hcut
    have hcmp : ∀ z r l B₀, tr.time r ≤ b →
        Healing.Growing.HighOrigin tr H g z r l B₀ →
        Goldilocks.Compatible (tr.HonestBlocksAt H) R B₀ := fun z r l B₀ hrb' ho =>
      tips_comparable_of_origin_witnesses_at hU hRB .refl
        (D.reset.clean_source_compatible_high_origin_at hx hsrc hs' hqb ho hrb')
    have hcandidate := D.reset.guarded_seed_ancestor_candidate_at_state_covered_at C.time_nonneg
      C.readPoint.1 C.honest C.time_bound hRm hseed hrb hhold (hcmp z r l S₀ hrb hseed)
      (Healing.Growing.ResetPremisesUpTo.compatibleWithOrigins_iff.2 ⟨fun z r l B₀ hrn ho =>
        hcmp z r l B₀ ((C.readPoint.1 r hrn).trans C.time_bound) ho,
        fun hc _ _ hD _ => D.reset.clean_source_compatible_healed_at hx hsrc hs' hqb hRB hc
          hD.healedOrigin⟩)
    exact hcandidate.elim Or.inr (fun h => Or.inl h.2.1)

set_option linter.unusedVariables false in
/-- **A looked-up record not below the fork-choice root is viable**, at a read point after the
repair window: the record's clean source and the guarded reset seed make it an ancestor
candidate. The supplied recent result is not needed. -/
theorem healthy_current_record_viable_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t)
    {R B : AC.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} {r s : Nat}
    {CV : Set (AC.Vote sp.n)}
    (hx : x ∈ H (tr.time r)) (hr : AC.ResultAt tr.projAC x r s B CV)
    (hRB : Anc (tr.HonestBlocksAt H) R B) (hrb : tr.time r ≤ b)
    (hs : Healing.cutZ sp.toParams g ≤ sp.ts s) (hL : s < C.label)
    (hfc : ¬ (Node.frame (tr.state y n)).Anc R (Node.frame (tr.state y n)).fcRoot)
    (hR : AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed =
      some R) :
    R ∈ (Node.frame (tr.state y n)).viableTree (Node.frame (tr.state y n)).tree := by
  have hU := Compose.Growing.honest_blocks_coherent D.reset.run D.reset.noColl
  obtain ⟨hPhi, -, -, -⟩ := read_frame D C
  obtain ⟨hdrain, hgu, hbefore, hcut, -⟩ := read_opening D C
  have hRm := (AC.lookup_eq_some hR).1
  have hcover := record_sources_before_now_at D O C.readPoint C.honest C.repaired
    C.repairedCut
  rw [hR, Option.getD_some, recordCover_iff] at hcover
  rcases hcover with hF | ⟨z, q, l, E, DV, hz, -, hqt, hl, hsrc, hRE⟩
  · exact absurd (hF ▸ hPhi.F_anc_fcRoot) hfc
  have hqb := hqt.trans C.time_bound
  have hl' : Healing.cleanLabel sp D.resetTime + 2 * sp.k + 1 ≤ l := by
    rw [← D.cleanLabel_eq]; exact hl
  obtain ⟨zS, qS, lS, S₀, hseed, hqSb, -, -, hhold⟩ :=
    D.reset.reset_seed_held_at_read_at C.readPoint C.time_bound C.honest hdrain hgu hbefore hcut
  have hcmp : ∀ z r l B₀, tr.time r ≤ b →
      Healing.Growing.HighOrigin tr H g z r l B₀ →
      Goldilocks.Compatible (tr.HonestBlocksAt H) R B₀ := fun z r l B₀ hrb' ho =>
    tips_comparable_of_origin_witnesses_at hU hRE .refl
      (D.reset.clean_source_compatible_high_origin_at hz hsrc hl' hqb ho hrb')
  rcases D.reset.guarded_seed_ancestor_candidate_at_state_covered_at C.time_nonneg
    C.readPoint.1 C.honest C.time_bound hRm hseed hqSb hhold (hcmp zS qS lS S₀ hqSb hseed)
    (Healing.Growing.ResetPremisesUpTo.compatibleWithOrigins_iff.2 ⟨fun z r l B₀ hrn ho =>
      hcmp z r l B₀ ((C.readPoint.1 r hrn).trans C.time_bound) ho,
      fun hc _ _ hD _ => D.reset.clean_source_compatible_healed_at hz hsrc hl' hqb hRE hc
        hD.healedOrigin⟩)
    with hroot | hviable
  · exact absurd hroot hfc
  · exact hviable

/-- **The vote-domain arm of a recent actual result**: the result's prefix is below the
fork-choice root or in the viable voter tree of every later cast of a node honest at it, given the
earlier later-label votes extend it; inside the deep quarantine (`hpre`). -/
theorem healthy_current_vote_domain_of_quarantine_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {R B : AC.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} {r s : Nat}
    {CV : Set (AC.Vote sp.n)}
    (hx : x ∈ H (tr.time r)) (hr : AC.ResultAt tr.projAC x r s B CV)
    (hRB : Anc (tr.HonestBlocksAt H) R B) (hrb : tr.time r ≤ b)
    (hs : D.cleanLabel + sp.k + 2 ≤ s)
    (hpre : ∀ Dd, sp.deepDepth = some Dd → b ≤ Healing.cutZ sp.toParams g + 4 * Dd * sp.Δ) :
    ∀ z q ell e, z ∈ H (tr.time q) → AC.CastAt tr.projAC z q ell e →
      tr.time q ≤ b → s < e.msg.slot →
      (∀ w p e', p < q → Compose.Growing.HVoteAt tr H w p e' → s < e'.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e'.msg R) →
      Anc (tr.HonestBlocksAt H) R ell.frame.fcRoot ∨
        R ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  intro z q ell e hz he hqb hse hprior
  exact Healing.Growing.ProposalImpl.result_prefix_vote_domain_before_of_quarantine_at D.reset
    hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb he hse hqb
    (fun w p hw hpq e' hv hs' => hprior w p e' hpq
      (Compose.Growing.hVoteAt_iff.mpr ⟨hw, hv⟩) hs') hpre

/-- **The stored-lock arm of a recent actual result**: the time-live stored locks at a cast of the
successor label, of a node honest at it, compare with the result's prefix. -/
theorem healthy_current_stored_locks_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {R B : AC.Blk sp.n (List (FG.Att sp.n))} {x : Fin sp.n} {r s : Nat}
    {CV : Set (AC.Vote sp.n)}
    (hx : x ∈ H (tr.time r)) (hr : AC.ResultAt tr.projAC x r s B CV)
    (hRB : Anc (tr.HonestBlocksAt H) R B) (hrb : tr.time r ≤ b)
    (hs : D.cleanLabel + 2 * sp.k + 1 ≤ s) :
    ∀ z q ell e, z ∈ H (tr.time q) → AC.CastAt tr.projAC z q ell e →
      tr.time q ≤ b → e.msg.slot = s + 1 →
      ∀ l ∈ (tr.projAC.state z q).locks, sp.slot (tr.time q) ≤ l.slot + sp.k →
        l.slot ≤ s → ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block →
          Goldilocks.Compatible (tr.HonestBlocksAt H) Y R := by
  intro z q ell e hz he hqb hes
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hd := hrun.time_nonneg q
  have hac := (Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hnc.upTo _)).localRun
  rw [RunTrace.upTo_projAC] at hac
  have he' : AC.CastAt (tr.projAC.upTo (tr.time q)) z q ell e :=
    AC.upTo_castAt.mpr ⟨le_rfl, he⟩
  have hslot := (AC.castAt_specU hac.toU hz he').2.1
  exact D.reset.result_prefix_stored_locks_at hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb hqb (by
      change e.msg.slot = sp.slot (tr.time q) at hslot
      exact (hes.symm.trans hslot).le)

/-- **The reader's normalized live locks are pairwise compatible**, at a read point after the
repair window, through their clean stored provenance. -/
theorem healthy_current_live_chain_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t) :
    ∀ X ∈ AC.liveLockBlocks sp (tr.state y n).ac.locks
        (Node.frame (tr.state y n)) t,
      ∀ Y ∈ AC.liveLockBlocks sp (tr.state y n).ac.locks
        (Node.frame (tr.state y n)) t,
      Goldilocks.Compatible (Node.frame (tr.state y n)).tree X Y := by
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨hPhi, hsub, hst, hwf⟩ := read_frame D C
  have hdrain : Healing.drainTime sp D.resetTime ≤ t := by
    have h6 : (0 : Time) ≤ 6 * sp.Δ := mul_nonneg (by norm_num) sp.toParams.hΔ.le
    linarith only [O.drain, C.repaired, h6]
  intro X hX Y hY
  obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := AC.mem_liveLockBlocks_of_wf hPhi hwf hX
  obtain ⟨m, hm, E, hE, hEr, hmive, rfl⟩ := AC.mem_liveLockBlocks_of_wf hPhi hwf hY
  rw [← hst] at hl hm
  have hBE := D.reset.clean_stored_locks_compatible_at
    C.time_nonneg C.readPoint.1 C.honest C.time_bound hl hm
    (Healing.drain_stored_lock_label hdrain hlive) (Healing.drain_stored_lock_label hdrain hmive)
    (hsub hB) hBr (hsub hE) hEr
  have hXB := (AC.viableAncestor_anc hPhi hB).2.mono hsub
  have hYE := (AC.viableAncestor_anc hPhi hE).2.mono hsub
  have hXY := tips_comparable_of_origin_witnesses_at hU hXB hYE hBE
  rcases hXY with h | h
  · exact Or.inl (AC.anc_tree_of_anc_U hU hPhi hsub hX.1 h hY.1)
  · exact Or.inr (AC.anc_tree_of_anc_U hU hPhi hsub hY.1 h hX.1)

end Repair

end Consensus.Goldilocks.Obligations.Growing

end
