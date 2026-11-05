module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockTargetSelf
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks SA: the opponents of the view that `unlock` reads

The O-form of the unlock premise of `mem_step_locks_of_keep_view`.
The view `unlockView A Φ t c` of an AC call `c` is built from votes of pools and
from the votes and support entries of the blocks of `Φ.tree`. So, for a vote set `S` that holds
these votes, its votes and its support lie in `S`, and its opponents lie in the opponents of the
view `⟨S, S⟩` (`opponents` grows with the view).
`unlockView_subset_post`: `S` holds the pools of `A` and of the state after the call, and the
votes and support entries of the blocks of `Φ.tree`; `heldVotes A A' Φ` is such an `S`.

Then `2 · |O| < n` and `opponents(Φ, ⟨S, S⟩, s, B) ⊆ O` give `unlockTarget = B` (for honest
voters, `unlockTarget_unlockView_held_of_honest_slot` in `OpponentsHonest`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {Φ : Frm sp.n FGP} {t : Time}

/-- The opponents grow with the votes and the support of the view. -/
theorem opponents_mono_view {V W : View sp.n} (hv : V.votes ⊆ W.votes)
    (hs : V.support ⊆ W.support) (s : Int) (B : Blk sp.n FGP) :
    opponents sp Φ V s B ⊆ opponents sp Φ W s B := by
  rintro i (hi | ⟨x, hx, h⟩)
  · exact Or.inl (equivocators_mono (sp := sp) hv hi)
  · exact Or.inr ⟨x, hs hx, h⟩

/-- The votes and the support of a pool view lie in a set that holds the pools. -/
theorem voteViewList_subset {A : SAState sp.n} {σ : Int} {cutoff : ETime}
    {S : Set (Vote sp.n)} (hpool : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S) :
    (View.ofLists (voteViewList A Φ σ cutoff)).votes ⊆ S ∧
      (View.ofLists (voteViewList A Φ σ cutoff)).support ⊆ S := by
  have hp : ∀ v ∈ A.poolAt σ, v ∈ S := by
    intro v hv
    unfold SAState.poolAt at hv
    split_ifs at hv
    · exact absurd hv List.not_mem_nil
    · exact hpool _ v hv
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · simp only [voteViewList, View.ofLists, Set.mem_ofPred_eq, List.mem_filter,
      decide_eq_true_eq] at hv
    exact hp v hv.1
  · simp only [voteViewList, View.ofLists, Set.mem_ofPred_eq, List.mem_filter,
      decide_eq_true_eq] at hv
    exact hp v hv.1.1

/-- The votes and the support of the merged vote view lie in a set that holds the pools of `A`
and the votes and support entries of the blocks of `Φ.tree`. -/
theorem mergedVoteView_subset {A : SAState sp.n} {s : Nat} {S : Set (Vote sp.n)}
    (hpool : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S)
    (htree : ∀ C ∈ Φ.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S) :
    (mergedVoteView sp A Φ s).votes ⊆ S ∧ (mergedVoteView sp A Φ s).support ⊆ S := by
  have hb := voteViewList_subset (Φ := Φ) (σ := (s : Int) - 1)
    (cutoff := ETime.of (freeze sp s)) hpool
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rcases hv with hv | ⟨C, hC, -, hv⟩
    · exact hb.1 hv
    · exact htree C hC v (Or.inl hv)
  · rcases hv with hv | ⟨C, hC, -, hv, -⟩
    · exact hb.2 hv
    · exact htree C hC v (Or.inr hv)

/-- **The view of a call lies in the votes held before and after it.** The votes and the support
of `unlockView A Φ t c` lie in a set `S` that holds the pools of `A`, the pools of the state
after the call, and the votes and support entries of the blocks of `Φ.tree`. -/
theorem unlockView_subset_post {ro : ReplayOrder sp FGP} (self : Fin sp.n) {A : SAState sp.n}
    (c : (goldilocksSA sp FGP ro).Call) {S : Set (Vote sp.n)}
    (hpre : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S)
    (hpost : ∀ τ, ∀ v ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).1.pool τ, v ∈ S)
    (htree : ∀ C ∈ Φ.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S) :
    (unlockView A Φ t c).votes ⊆ S ∧ (unlockView A Φ t c).support ⊆ S := by
  cases c with
  | tick => rw [unlockView_tick]; exact mergedVoteView_subset hpre htree
  | proposal => rw [unlockView_proposal]; exact voteViewList_subset hpre
  | toFG => rw [unlockView_toFG]; exact mergedVoteView_subset hpre htree
  | restart => rw [unlockView_restart]; exact mergedVoteView_subset hpre htree
  | message v =>
    rw [unlockView_message]
    exact mergedVoteView_subset
      (fun τ x hx => hpost τ x ((grows_tryVote (sp := sp) self _ Φ t).mem hx)) htree
  | block C =>
    rw [unlockView_block]
    exact mergedVoteView_subset
      (fun τ x hx => hpost τ x ((grows_tryVote (sp := sp) self _ Φ t).mem hx)) htree

/-- The votes held across a call from `A` to `A'` with frame `Φ`: the votes of the pools of `A`
and of `A'`, and the votes and support entries of the blocks of `Φ.tree`. -/
def heldVotes (A A' : SAState sp.n) (Φ : Frm sp.n FGP) : Set (Vote sp.n) :=
  {v | (∃ τ, v ∈ A.pool τ) ∨ (∃ τ, v ∈ A'.pool τ) ∨
    ∃ C ∈ Φ.tree, v ∈ blockVotes C ∨ v ∈ blockSupport C}

theorem mem_heldVotes {A A' : SAState sp.n} {v : Vote sp.n} : v ∈ heldVotes A A' Φ ↔
    (∃ τ, v ∈ A.pool τ) ∨ (∃ τ, v ∈ A'.pool τ) ∨
      ∃ C ∈ Φ.tree, v ∈ blockVotes C ∨ v ∈ blockSupport C :=
  Iff.rfl

end Consensus.Goldilocks.SA

end
