module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockKeepInterval
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.OpponentsHonest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks: a lock kept over an interval of cuts against honest votes

`heldVotes_honest_unique`: at an AC cut `j` of an honest node `y`,
two votes held across the cut (`AC.heldVotes`) of one honest validator and one slot are equal
(each was emitted by its validator, `one_vote_per_slot`; a declared head vote counts only when its
validator has two distinct pooled votes of its slot, impossible for an honest validator). With
the fault bound `2 · |Hᶜ| < n` this keeps the unlock target
(`AC.unlockTarget_unlockView_held_of_honest_slot`). It assumes `NoCollRun`, for the AC projection
of the run (`goldilocks_ac_projection`). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **Honest held votes do not equivocate per slot.** At an AC cut `j` of an honest node `y`, two
votes of the same honest validator and the same slot among the votes held across the cut are
equal. -/
theorem heldVotes_honest_unique {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {x x' : Vote sp.n}
    (hx : x ∈ AC.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)))
    (hx' : x' ∈
      AC.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac (Node.frame (tr.state y j)))
    (hxH : x.val ∈ H) (hval : x'.val = x.val) (hs : x.slot = x'.slot) : x = x' := by
  have hrun' := goldilocks_ac_projection_from hrun hnc
  have hr := hrun'.localRun
  have hem : ∀ v ∈ AC.heldVotes (tr.state y j).ac (tr.state y (j + 1)).ac
      (Node.frame (tr.state y j)), v.val ∈ H →
      ∃ k e, AC.VoteAt tr.projAC v.val k e ∧ e.msg = v := by
    intro v hv hvH
    rcases AC.mem_heldVotes.1 hv with ⟨τ, hv⟩ | ⟨τ, hv⟩ | ⟨-, hv⟩
    · rw [← projAC_state hrun.toLocalRun hy] at hv
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy j τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · rw [← projAC_state hrun.toLocalRun hy] at hv
      obtain ⟨k, -, e, he, hm⟩ := hrun'.honest.pool_vote y hy (j + 1) τ v hv hvH
      exact ⟨k, e, he, hm⟩
    · -- a declaration counts only when its validator equivocates in the post-cut pool; two
      -- distinct pooled votes of an honest validator in one slot contradict one vote per slot
      exfalso
      obtain ⟨w₁, hw₁, w₂, hw₂, hne, hw₁v, hw₂v⟩ := hv
      simp only [Set.mem_ofPred_eq] at hw₁ hw₂
      rw [← projAC_state hrun.toLocalRun hy] at hw₁ hw₂
      have hs₁ := (state_pool_cap hrun hy (j + 1) v.slot).1 w₁ hw₁
      have hs₂ := (state_pool_cap hrun hy (j + 1) v.slot).1 w₂ hw₂
      obtain ⟨k₁, -, e₁, he₁, hm₁⟩ := hrun'.honest.pool_vote y hy (j + 1) _ w₁ hw₁ (hw₁v ▸ hvH)
      obtain ⟨k₂, -, e₂, he₂, hm₂⟩ := hrun'.honest.pool_vote y hy (j + 1) _ w₂ hw₂ (hw₂v ▸ hvH)
      rw [hw₁v] at he₁
      rw [hw₂v] at he₂
      have := (AC.one_vote_per_slotU sp _ ro H _ _ hr.toU _ hvH k₁ k₂ e₁ e₂ he₁ he₂
        (by rw [hm₁, hm₂, hs₁, hs₂])).2
      exact hne (hm₁.symm.trans
        ((congrArg (fun e : AC.Em sp (List (FG.Att sp.n)) => e.msg) this).trans hm₂))
  obtain ⟨k, e, he, rfl⟩ := hem x hx hxH
  obtain ⟨k', e', he', rfl⟩ := hem x' hx' (hval ▸ hxH)
  rw [hval] at he'
  exact congrArg (fun e : AC.Em sp (List (FG.Att sp.n)) => e.msg)
    (AC.one_vote_per_slotU sp _ ro H _ _ hr.toU _ hxH k k' e e' he he' hs).2

end Consensus.Goldilocks.Compose

end
