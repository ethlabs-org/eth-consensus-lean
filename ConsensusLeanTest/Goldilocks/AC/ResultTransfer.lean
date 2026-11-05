module
public import ConsensusLeanTest.Goldilocks.AC.FastUpdate
public import ConsensusLean.Instances.Goldilocks.Proofs.ACSteps.Main
@[expose] public section

/-! # Witness for the premises of the Goldilocks ACSteps statement A1.8 `ResultTransfer`

Kind (a), joint satisfiability (CONTRIBUTING "Statements"): the hypotheses of A1.8
`ResultTransfer` (`Statements/AC/Steps.lean`) hold together on the AC projection of the
one-validator tick run of `Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`, `t_s = 4s`,
`k = c = 2`, a tick at every time, no restart), so the proved milestone is not vacuous. For every
slot `s ≥ 1`:

* the result: the update of slot `s` at cut `8 · (4s + 6)` (time `t_s + 6Δ`) gets the result
  `blk s` with counted votes `{cv s}` (`ResultAt`, from `Goldilocks/AC/FastUpdate`);
* the vote: `v0`'s slot-`(s + 1)` vote at cut `8 · t_{s+1} + 3` (`ac_on_block` of its own block
  `blk (s + 1)`), with `CarryAt`, `blk s` in the viable voter block tree;
* `liveLocks_compatible`: every live lock block of the vote's frame is a chain block, so it is
  compatible with `blk s`;
* `mergedView_slot_cv`: every slot-`s` vote of the merged view of the vote is `cv s`, the only
  vote of the update's pool `s` (`[cv s]`).

`resultTransfer_premises_update` bundles these for every `s ≥ 1`;
`resultTransfer_premises_satisfiable` states, at `sp1`, `FGP := List (FG.Att sp1.n)`, `ro1`,
that there are values of all the statement's universally bound variables satisfying `ACRun` and
every hypothesis (copied from the statement), at `s = 1` (update cut `80`, vote cut `67`);
`resultTransfer_on_witness` applies the proved milestone (`acStepsAt`). The vote (time
`t_{s+1} = 4s + 4`) precedes the update (time `4s + 6`): the statement does not order `i₀` and
`i`, and the claims allow a result that is later than the vote.

Limitations: `n = 1` and `f = 0`, so the equivocation alternative of the merged-view premise is
not used (the pool has no equivocator). The run is one chain, so every live lock block is
compatible with every chain block and the lock premise holds without a vetoed lock. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node ChainFrame

/-- (a) **Every slot-`s` vote of the merged view at the vote of slot `s + 1` is `cv s`**: the
read point's pool holds chain votes only, and the only slot-`(s + 1)` block of the frame is
`blk (s + 1)`, whose votes are `[cv s]`. -/
theorem mergedView_slot_cv {s : Nat} {fg' : Store sp1.toParams N1.Payload} {e : N1.Em}
    (hfg : FGGood fg' (s + 1))
    (hp : e.readPoint.pool = (tickState N1 dg1 (4 * (s + 1))).ac.pool) :
    ∀ v ∈ (mergedVoteView sp1 e.readPoint fg'.toFrame (s + 1)).votes, v.slot = s → v = cv s := by
  intro v hv hvs
  rcases hv with hv | ⟨B, hB, hBs, hv⟩
  · simp only [voteView, voteViewList, View.ofLists, Set.mem_ofPred_eq, List.mem_filter] at hv
    have hv' := hv.1
    unfold SAState.poolAt at hv'
    split_ifs at hv'
    · simp at hv'
    · rw [hp] at hv'
      rw [tickState_pool_cv _ _ v hv'] at hvs ⊢
      exact congrArg cv hvs
  · obtain ⟨f, hf⟩ := fgGood_frame hfg
    obtain ⟨m, -, -, rfl⟩ := hf.eq_of_mem hB
    rw [blk_slot] at hBs
    subst hBs
    exact List.mem_singleton.1 hv

/-- (a) **Every live lock block of a frame of the run is compatible with every chain block**:
it is a block of the frame, which is a chain. -/
theorem liveLocks_compatible {τ : Nat} {fg' : Store sp1.toParams N1.Payload}
    (hfg : FGGood fg' τ) (L : Set Lock) (t : Time) (s : Nat) :
    ∀ B ∈ liveLockBlocks sp1 L fg'.toFrame t,
      Compatible ((tickRun N1 dg1).HonestBlocks Set.univ) B (blk s) := by
  rintro B ⟨hB, -⟩
  obtain ⟨f, hf⟩ := fgGood_frame hfg
  obtain ⟨m, -, -, rfl⟩ := hf.eq_of_mem hB
  exact compatible_blk m s

/-- (a) **The premises of A1.8 (`ResultTransfer`) at the update of slot `s ≥ 1`**: the result
`blk s` of the update at cut `8 · (4s + 6)`, counting `{cv s}`, and the slot-`(s + 1)` vote at
cut `8 · t_{s+1} + 3`: `CarryAt`, `blk s` viable at the vote, every live lock block compatible
with `blk s`, and every slot-`s` vote of the merged view in the update's pool `s`. -/
theorem resultTransfer_premises_update {s : Nat} (hs : 1 ≤ s) :
    ∃ (ℓ : ACLabel N1) (e : N1.Em),
      ResultAt (tickRun N1 dg1).projAC v0 (8 * (4 * s + 6)) s (blk s) {cv s} ∧
      CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (s + 1)) + 3) ℓ e ∧ e.msg.slot = s + 1 ∧
      CarryAt (tickRun N1 dg1).projAC ((tickRun N1 dg1).HonestBlocks Set.univ) v0
        (8 * (4 * (s + 1)) + 3) e s {cv s} ∧
      ViableAtVote ℓ e (s + 1) (blk s) ∧
      (∀ L ∈ liveLockBlocks sp1 e.readPoint.locks ℓ.frame
          ((tickRun N1 dg1).projAC.time (8 * (4 * (s + 1)) + 3)),
        Compatible ((tickRun N1 dg1).HonestBlocks Set.univ) L (blk s)) ∧
      (∀ v ∈ (mergedVoteView sp1 e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
        v ∈ ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).pool s ∨
        v.val ∈ equivocators
          {w | w ∈ ((tickRun N1 dg1).projAC.state v0 (8 * (4 * s + 6))).pool s}) := by
  obtain ⟨fg', e, hl, hfg', hm, hp⟩ := vote_label s
  obtain ⟨f, hf⟩ := fgGood_frame hfg'
  have hfs : f ≤ s := le_trans hf.fj (jexp_succ_le s)
  have hcast : CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (s + 1)) + 3)
      ⟨.block (blk (s + 1)), fg'.toFrame, [e]⟩ e :=
    ⟨Compose.projAC_callAt.2 ⟨rfl, hl⟩, List.mem_singleton_self _⟩
  have hslot : e.msg.slot = s + 1 := by rw [hm]; rfl
  refine ⟨_, e, ⟨_, updateAt_tickRun s, getConfirmation_update hs,
    (fastCounted_update hs).symm⟩, hcast, hslot,
    carry_cv s (fun v hv => hv) v0 (Set.mem_univ _) _ e ⟨_, hcast⟩ hslot,
    Or.inl (hf.mem_viableTree (mem_voterBlockTree hf _ (by omega) le_rfl)
      (jexp_succ_le s) (by omega) (mem_voterBlockTree hf _ hfs (by omega))),
    liveLocks_compatible hfg' _ _ s, fun v hv hvs => Or.inl ?_⟩
  rw [mergedView_slot_cv hfg' hp v hv hvs, update_pool_eq]
  exact List.mem_singleton_self _

/-- (a) **A1.8, `ResultTransfer`: the premises are satisfiable.** Every hypothesis of the
statement holds of the AC projection of the tick run at `s = 1`: the result `blk 1` of the
update of slot `1` at cut `80` (time `10`), counting `{cv 1}`, and the slot-`2` vote at cut `67`
(time `8`). -/
theorem resultTransfer_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n (List (FG.Att sp1.n))))
      (tr : SATrace sp1 (List (FG.Att sp1.n)) ro1) (proposer : Nat → Fin sp1.n) (s : Nat)
      (X y : Fin sp1.n) (i₀ i : Nat) (C : Blk sp1.n (List (FG.Att sp1.n)))
      (CV : Set (Vote sp1.n)) (ℓ : ACLabel (goldilocksSA sp1 (List (FG.Att sp1.n)) ro1))
      (e : Em sp1 (List (FG.Att sp1.n))),
    ACRun proposer tr H U ∧
    X ∈ H ∧ ResultAt tr X i₀ s C CV ∧
    y ∈ H ∧ CastAt tr y i ℓ e ∧ e.msg.slot = s + 1 ∧
    CarryAt tr U y i e s CV ∧ ViableAtVote ℓ e (s + 1) C ∧
    (∀ L ∈ liveLockBlocks sp1 e.readPoint.locks ℓ.frame (tr.time i), Compatible U L C) ∧
    (∀ v ∈ (mergedVoteView sp1 e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) := by
  obtain ⟨ℓ, e, hr, hc, hsl, hca, hv, hl, hm⟩ := resultTransfer_premises_update le_rfl
  exact ⟨Set.univ, _, _, fun _ => v0, 1, v0, v0, _, _, blk 1, {cv 1}, ℓ, e, acRun,
    Set.mem_univ _, hr, Set.mem_univ _, hc, hsl, hca, hv, hl, hm⟩

/-- (a) A1.8 on the run: for every slot `s ≥ 1`, the slot-`(s + 1)` vote at cut
`8 · t_{s+1} + 3` extends the result `blk s` of the update of slot `s`. -/
theorem resultTransfer_on_witness {s : Nat} (hs : 1 ≤ s) :
    ∃ (ℓ : ACLabel N1) (e : N1.Em),
      CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (s + 1)) + 3) ℓ e ∧
      VoteExtends ((tickRun N1 dg1).HonestBlocks Set.univ) e.msg (blk s) := by
  obtain ⟨ℓ, e, hr, hc, hsl, hca, hv, hl, hm⟩ := resultTransfer_premises_update hs
  exact ⟨ℓ, e, hc, (acStepsAt sp1).resultTransfer _ ro1 Set.univ _ _ (fun _ => v0) acRun s v0
    v0 _ _ (blk s) {cv s} ℓ e (Set.mem_univ _) hr (Set.mem_univ _) hc hsl hca hv hl hm⟩

end Consensus.Goldilocks.Witness.One

end
