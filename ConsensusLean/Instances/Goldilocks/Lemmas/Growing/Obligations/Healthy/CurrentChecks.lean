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
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Opening
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

The checks of `Obligations/HealedSafety` on a reader's current state at a read point after the
repair window (`HealthyReadContextAt`), with the reader honest at its read time and every source
writer honest at its own cut:

* `guarded_seed_ancestor_candidate_at_state_at`: a target compatible with a bounded high seed,
  held whenever it is above finalization, and with every earlier high origin, is an ancestor
  candidate of the reader's frame (the growing form of
  `UpTo.guarded_seed_ancestor_candidate_at_state`; the argument is
  `ResetPremisesUpTo.guarded_seed_ancestor_candidate_at_state_at`);
* `healthy_current_live_candidates_at`: the reader's live lock blocks and fork-choice root are
  compatible with its looked-up record;
* `healthy_current_record_viable_at`: a looked-up record not below the fork-choice root is
  viable;
* `healthy_current_vote_domain_at`, `healthy_current_stored_locks_at`: the vote-domain and
  stored-lock arms of a recent actual result;
* `healthy_current_live_chain_at`: the reader's live lock blocks are pairwise compatible.

The record's clean source comes from the receiver repair
(`healthy_current_record_sources_before_now_at`) and the reset seed from
`reset_seed_held_at_read_at`. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

section Guarded

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a b : Time}

/-- **A comparable bounded high seed, held whenever it is above finalization, supplies current
candidacy**, at a state of a reader honest at a read time `t ≤ b`, every earlier cut at a time
`≤ t`. A local signed entry witnesses any higher floor. -/
theorem guarded_seed_ancestor_candidate_at_state_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} {i q m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ r < i, tr.time r ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {P S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree)
    (hseed : Healing.Growing.HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    (hhold : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F S →
      S ∈ (tr.state y i).fg.tree)
    (hPS : Compatible (tr.HonestBlocksAt H) P S)
    (hcompare : ∀ x r l B, r < i → Healing.Growing.HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocksAt H) P B) :
    (Node.frame (tr.state y i)).AncestorCandidate P :=
  hp.guarded_seed_ancestor_candidate_at_state_at ht hle hy htb hPt hseed hqb hhold hPS hcompare

end Guarded

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The reader's frame at a read point of its context is well formed, inside the blocks held while
honest, and its AC state is its trace AC state. -/
private theorem read_frame (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) {y : Fin Q.params.n} {n : Nat} {t : Time}
    (C : HealthyReadContextAt S A V Q D y n t) :
    FrameOK (Node.frame (Q.trace.state y n)) ∧
      (Node.frame (Q.trace.state y n)).tree ⊆ Q.trace.HonestBlocksAt Q.keys ∧
      Q.trace.projAC.state y n = (Q.trace.state y n).ac ∧
      SA.LocksWF Q.params (Q.trace.state y n).ac.locks := by
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision
  have ht := C.time_nonneg
  have hle := C.readPoint.1
  have hst : (Q.trace.upTo t).state y n = Q.trace.state y n := Trace.upTo_state Q.trace y hle
  refine ⟨(Store.frame_realization _ _ _ _
      (Healing.Growing.fg_reachable_at hrun ht hle C.honest)).1,
    fun X hX => ⟨y, n, t, ht, hle, C.honest, hX.1⟩, ?_, ?_⟩
  · have h := Compose.projAC_state (hrun.upTo ht).toLocalRun C.honest n
    rwa [RunTrace.upTo_projAC, Trace.upTo_state Q.trace.projAC y hle, hst] at h
  · have h := Compose.locksWF_state (hrun.upTo ht) (hnc.upTo t) C.honest n
    rwa [hst] at h

/-- The repair opening of a schedule is before the read time of a context, after the drain. -/
private theorem read_opening (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) (O : HealthyRepairOpeningAt S A V Q D)
    {y : Fin Q.params.n} {n : Nat} {t : Time} (C : HealthyReadContextAt S A V Q D y n t) :
    Healing.drainTime Q.params D.resetTime ≤ Q.params.ts O.slot ∧
      SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts O.slot ∧
      Q.params.ts O.slot + 6 * Q.params.Δ < t ∧
      Healing.drainTime Q.params D.resetTime ≤ t := by
  have hlow := D.lower
  simp only [max_le_iff] at hlow
  obtain ⟨-, hdr, -, hgr, -⟩ := hlow
  have hΔ := Q.params.toParams.hΔ
  have hT : Q.params.ts O.slot + 6 * Q.params.Δ < t := by
    refine lt_of_le_of_lt ?_ C.repaired
    rw [add_mul, ← add_assoc]
    exact add_le_add O.bounded le_rfl
  refine ⟨hdr.trans O.fresh.le, hgr.trans O.fresh.le, hT, ?_⟩
  linarith only [hdr.trans O.fresh.le, hT, hΔ]

/-- **Current anchor candidates are compatible with the current looked-up record**: the reader's
live lock blocks and its fork-choice root, at a read point after the repair window. -/
theorem healthy_current_live_candidates_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (D : HealthyRepairScheduleAt S A V Q) {y : Fin Q.params.n} {n : Nat} {t : Time}
    (C : HealthyReadContextAt S A V Q D y n t)
    {R : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : SA.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed =
      some R) :
    ∀ X ∈ SA.liveLockBlocks Q.params (Q.trace.state y n).ac.locks (Node.frame (Q.trace.state y n))
        t ∪ {(Node.frame (Q.trace.state y n)).fcRoot},
      Goldilocks.Compatible (Node.frame (Q.trace.state y n)).tree X R := by
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hc := healthy_schedule_catch_at S A V Q D
  obtain ⟨hPhi, hsub, hst, hwf⟩ := read_frame S A V Q D C
  obtain ⟨O, hrepair⟩ := healthy_bounded_repairing_opening_at S A V Q hb hp D
  obtain ⟨hdrain, hgu, hbefore, hdrainNow⟩ := read_opening S A V Q D O C
  have hRm := (SA.lookup_eq_some hR).1
  have hcover := healthy_current_record_sources_before_now_at S A V Q D O hrepair C.readPoint
    C.time_bound C.honest C.repaired
  rw [hR, Option.getD_some, healthyRecordCoverAt_iff] at hcover
  rcases hcover with hF | ⟨x, q, s, B, CV, hx, -, hqt, hs, hsrc, hRB⟩
  · -- the record is the finalized block, below every block of the frame
    intro X hX
    have hFX : (Node.frame (Q.trace.state y n)).Anc R X := by
      rw [hF]
      rcases hX with hX | hX
      · exact hPhi.rooted.2 X hX.1
      · rw [Set.mem_singleton_iff.mp hX]
        exact hPhi.F_anc_fcRoot
    exact Or.inr hFX
  have hqb := hqt.trans C.time_bound
  have hs' : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 1 ≤ s := by
    rw [← D.cleanLabel_eq]; exact hs
  intro X hX
  rcases hX with hX | hX
  · obtain ⟨l, hl, E, hE, hEr, hlive, rfl⟩ := SA.mem_liveLockBlocks_of_wf hPhi hwf hX
    rw [← hst] at hl
    have hBE := D.reset.clean_source_stored_lock_compatible_at hc hx C.time_nonneg
      C.readPoint.1 C.honest C.time_bound hsrc hs' hqb hl
      (Healing.drain_stored_lock_label hdrainNow hlive) (hsub hE) hEr
    have hXE := (SA.viableAncestor_anc hPhi hE).2.mono hsub
    have hXR := tips_comparable_of_origin_witnesses_at S A V Q hXE hRB hBE.symm
    rcases hXR with h | h
    · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi hsub hX.1 h hRm)
    · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi hsub hRm h hX.1)
  · obtain rfl := Set.mem_singleton_iff.mp hX
    obtain ⟨z, r, l, S₀, hseed, hrb, -, -, hhold⟩ :=
      D.reset.reset_seed_held_at_read_at hc C.readPoint C.time_bound C.honest hdrain hgu hbefore
    have hcmp : ∀ z r l B₀, Q.trace.time r ≤ Q.bound →
        Healing.Growing.HighOrigin Q.trace Q.keys Q.gst z r l B₀ →
        Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys) R B₀ := fun z r l B₀ hrb' ho =>
      tips_comparable_of_origin_witnesses_at S A V Q hRB .refl
        (D.reset.clean_source_compatible_high_origin_at hc hx hsrc hs' hqb ho hrb')
    have hcandidate := guarded_seed_ancestor_candidate_at_state_at D.reset C.time_nonneg
      C.readPoint.1 C.honest C.time_bound hRm hseed hrb hhold (hcmp z r l S₀ hrb hseed)
      (fun z r l B₀ hrn ho => hcmp z r l B₀ ((C.readPoint.1 r hrn).trans C.time_bound) ho)
    exact hcandidate.elim Or.inr (fun h => Or.inl h.2.1)

set_option linter.unusedVariables false in
/-- **A looked-up record not below the fork-choice root is viable**, at a read point after the
repair window: the record's clean source and the guarded reset seed make it an ancestor
candidate. The supplied recent result is not needed. -/
theorem healthy_current_record_viable_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (D : HealthyRepairScheduleAt S A V Q) {y : Fin Q.params.n} {n : Nat} {t : Time}
    (C : HealthyReadContextAt S A V Q D y n t)
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x : Fin Q.params.n} {r s : Nat}
    {CV : Set (SA.Vote Q.params.n)}
    (hx : x ∈ Q.keys (Q.trace.time r)) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocksAt Q.keys) R B) (hrb : Q.trace.time r ≤ Q.bound)
    (hs : Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s) (hL : s < C.label)
    (hfc : ¬ (Node.frame (Q.trace.state y n)).Anc R (Node.frame (Q.trace.state y n)).fcRoot)
    (hR : SA.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed =
      some R) :
    R ∈ (Node.frame (Q.trace.state y n)).viableTree (Node.frame (Q.trace.state y n)).tree := by
  have hc := healthy_schedule_catch_at S A V Q D
  obtain ⟨hPhi, -, -, -⟩ := read_frame S A V Q D C
  obtain ⟨O, hrepair⟩ := healthy_bounded_repairing_opening_at S A V Q hb hp D
  obtain ⟨hdrain, hgu, hbefore, -⟩ := read_opening S A V Q D O C
  have hRm := (SA.lookup_eq_some hR).1
  have hcover := healthy_current_record_sources_before_now_at S A V Q D O hrepair C.readPoint
    C.time_bound C.honest C.repaired
  rw [hR, Option.getD_some, healthyRecordCoverAt_iff] at hcover
  rcases hcover with hF | ⟨z, q, l, E, DV, hz, -, hqt, hl, hsrc, hRE⟩
  · exact absurd (hF ▸ hPhi.F_anc_fcRoot) hfc
  have hqb := hqt.trans C.time_bound
  have hl' : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 1 ≤ l := by
    rw [← D.cleanLabel_eq]; exact hl
  obtain ⟨zS, qS, lS, S₀, hseed, hqSb, -, -, hhold⟩ :=
    D.reset.reset_seed_held_at_read_at hc C.readPoint C.time_bound C.honest hdrain hgu hbefore
  have hcmp : ∀ z r l B₀, Q.trace.time r ≤ Q.bound →
      Healing.Growing.HighOrigin Q.trace Q.keys Q.gst z r l B₀ →
      Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys) R B₀ := fun z r l B₀ hrb' ho =>
    tips_comparable_of_origin_witnesses_at S A V Q hRE .refl
      (D.reset.clean_source_compatible_high_origin_at hc hz hsrc hl' hqb ho hrb')
  rcases guarded_seed_ancestor_candidate_at_state_at D.reset C.time_nonneg C.readPoint.1
    C.honest C.time_bound hRm hseed hqSb hhold (hcmp zS qS lS S₀ hqSb hseed)
    (fun z r l B₀ hrn ho => hcmp z r l B₀ ((C.readPoint.1 r hrn).trans C.time_bound) ho) with
    hroot | hviable
  · exact absurd hroot hfc
  · exact hviable

/-- **The vote-domain arm of a recent actual result**: the result's prefix is below the
fork-choice root or in the viable voter tree of every later cast of a node honest at it, given the
earlier later-label votes extend it. -/
theorem healthy_current_vote_domain_at (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q)
    (hc : Healing.Growing.CatchRun Q.trace Q.keys Q.gst (2 * Q.params.Δ))
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x : Fin Q.params.n} {r s : Nat}
    {CV : Set (SA.Vote Q.params.n)}
    (hx : x ∈ Q.keys (Q.trace.time r)) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocksAt Q.keys) R B) (hrb : Q.trace.time r ≤ Q.bound)
    (hs : D.cleanLabel + Q.params.k + 2 ≤ s) :
    ∀ z q ell e, z ∈ Q.keys (Q.trace.time q) → SA.CastAt Q.trace.projAC z q ell e →
      Q.trace.time q ≤ Q.bound → s < e.msg.slot →
      (∀ w p e', p < q → Compose.Growing.HVoteAt Q.trace Q.keys w p e' → s < e'.msg.slot →
        SA.VoteExtends (Q.trace.HonestBlocksAt Q.keys) e'.msg R) →
      Anc (Q.trace.HonestBlocksAt Q.keys) R ell.frame.fcRoot ∨
        R ∈ ell.frame.viableTree (SA.voterBlockTree Q.params e.readPoint ell.frame e.msg.slot) := by
  intro z q ell e hz he hqb hse hprior
  exact Healing.Growing.ProposalImpl.result_prefix_vote_domain_before_at D.reset hc hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb he hse hqb
    (fun w p hw hpq e' hv hs' => hprior w p e' hpq
      (Compose.Growing.hVoteAt_iff.mpr ⟨hw, hv⟩) hs')

/-- **The stored-lock arm of a recent actual result**: the time-live stored locks at a cast of the
successor label, of a node honest at it, compare with the result's prefix. -/
theorem healthy_current_stored_locks_at (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q)
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x : Fin Q.params.n} {r s : Nat}
    {CV : Set (SA.Vote Q.params.n)}
    (hx : x ∈ Q.keys (Q.trace.time r)) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocksAt Q.keys) R B) (hrb : Q.trace.time r ≤ Q.bound)
    (hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s) :
    ∀ z q ell e, z ∈ Q.keys (Q.trace.time q) → SA.CastAt Q.trace.projAC z q ell e →
      Q.trace.time q ≤ Q.bound → e.msg.slot = s + 1 →
      ∀ l ∈ (Q.trace.projAC.state z q).locks, Q.params.slot (Q.trace.time q) ≤ l.slot + Q.params.k →
        l.slot ≤ s → ∀ Y ∈ Q.trace.HonestBlocksAt Q.keys, Y.root = l.block →
          Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys) Y R := by
  intro z q ell e hz he hqb hes
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision
  have hd := hrun.time_nonneg q
  have hac := (Compose.goldilocks_ac_projection _ _ _ (Q.keys (Q.trace.time q))
    (Q.trace.upTo (Q.trace.time q)) _ (hrun.upTo hd) (hnc.upTo _)).localRun
  rw [RunTrace.upTo_projAC] at hac
  have he' : SA.CastAt (Q.trace.projAC.upTo (Q.trace.time q)) z q ell e :=
    SA.upTo_castAt.mpr ⟨le_rfl, he⟩
  have hslot := (SA.castAt_spec hac hz he').2.1
  exact D.reset.result_prefix_stored_locks_at (healthy_schedule_catch_at S A V Q D) hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb hqb (by
      change e.msg.slot = Q.params.slot (Q.trace.time q) at hslot
      exact (hes.symm.trans hslot).le)

/-- **The reader's normalized live locks are pairwise compatible**, at a read point after the
repair window, through their clean stored provenance. -/
theorem healthy_current_live_chain_at (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) {y : Fin Q.params.n} {n : Nat} {t : Time}
    (C : HealthyReadContextAt S A V Q D y n t) :
    ∀ X ∈ SA.liveLockBlocks Q.params (Q.trace.state y n).ac.locks
        (Node.frame (Q.trace.state y n)) t,
      ∀ Y ∈ SA.liveLockBlocks Q.params (Q.trace.state y n).ac.locks
        (Node.frame (Q.trace.state y n)) t,
      Goldilocks.Compatible (Node.frame (Q.trace.state y n)).tree X Y := by
  have hrun := simTraceAt_goldilocksRun ⟨S, stock⟩ Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn Q.valid Q.noCollision
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨hPhi, hsub, hst, hwf⟩ := read_frame S A V Q D C
  have hlow := D.lower
  simp only [max_le_iff] at hlow
  obtain ⟨-, hdr, -⟩ := hlow
  have hq0 : D.query ≤ t := by
    have : (0 : Time) ≤ (4 * (Q.index : Time) + 6) * Q.params.Δ :=
      mul_nonneg (by positivity) Q.params.toParams.hΔ.le
    linarith only [C.repaired, this]
  have hdrain := hdr.trans hq0
  intro X hX Y hY
  obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := SA.mem_liveLockBlocks_of_wf hPhi hwf hX
  obtain ⟨m, hm, E, hE, hEr, hmive, rfl⟩ := SA.mem_liveLockBlocks_of_wf hPhi hwf hY
  rw [← hst] at hl hm
  have hBE := D.reset.clean_stored_locks_compatible_at (healthy_schedule_catch_at S A V Q D)
    C.time_nonneg C.readPoint.1 C.honest C.time_bound hl hm
    (Healing.drain_stored_lock_label hdrain hlive) (Healing.drain_stored_lock_label hdrain hmive)
    (hsub hB) hBr (hsub hE) hEr
  have hXB := (SA.viableAncestor_anc hPhi hB).2.mono hsub
  have hYE := (SA.viableAncestor_anc hPhi hE).2.mono hsub
  have hXY := tips_comparable_of_origin_witnesses_at S A V Q hXB hYE hBE
  rcases hXY with h | h
  · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi hsub hX.1 h hY.1)
  · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi hsub hY.1 h hX.1)

end Consensus.Goldilocks.Obligations.Growing

end
