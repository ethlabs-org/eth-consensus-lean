module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockTargetSelf
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks SA: the opponents of the view that `unlock` reads

The O-form of the unlock premise of `mem_step_locks_of_keep_view` (consensus-lean#135,
WI-15/16). The view `unlockView A Φ t c` of an AC call `c` is built from votes of pools and
from the votes and support entries of the blocks of `Φ.tree`. So, for a vote set `S` that holds
these votes, its votes and its support lie in `S`, and its opponents lie in the opponents of the
view `⟨S, S⟩` (`opponents` grows with the view). Two forms of `S`:

* `unlockView_subset_post`: `S` holds the pools of `A` and of the state after the call, and the
  votes and support entries of the blocks of `Φ.tree`;
* `unlockView_subset_pre`: `S` holds the pools of `A`, the votes and support entries of the
  blocks of `Φ.tree`, and the votes that the call admits (the vote `v` of `.message v`, the
  votes of the block `C` of `.block C`).

Then `2 · |O| < n` and `opponents(Φ, ⟨S, S⟩, s, B) ⊆ O` give `unlockTarget = B`
(`unlockTarget_unlockView_post`, `unlockTarget_unlockView_pre`; with `S = heldVotes A A' Φ`,
`unlockTarget_unlockView_held`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {Φ : Frm sp.n FGP} {t : Time}

/-- The opponents grow with the votes and the support of the view. -/
theorem opponents_mono_view {V W : View sp.n} (hv : V.votes ⊆ W.votes)
    (hs : V.support ⊆ W.support) (s : Int) (B : Blk sp.n FGP) :
    opponents sp Φ V s B ⊆ opponents sp Φ W s B := by
  rintro i (hi | ⟨x, hx, h⟩)
  · exact Or.inl (equivocators_mono (sp := sp) hv hi)
  · exact Or.inr ⟨x, hs hx, h⟩

/-- A vote of the pool of the admission is in the pool before it or is the admitted vote. -/
theorem mem_admitVote_pool_sub {A : SAState sp.n} {v x : Vote sp.n} {σ : Nat}
    (hx : x ∈ (admitVote sp A t v).pool σ) : x ∈ A.pool σ ∨ x = v := by
  unfold admitVote at hx
  split_ifs at hx
  · exact Or.inl hx
  · exact Or.inl hx
  · simp only [Function.update_apply] at hx
    split_ifs at hx with h
    · subst h
      rcases List.mem_append.1 hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)
    · exact Or.inl hx

/-- A vote of a pool after admitting the votes of a list in order is in the pool before or in
the list. -/
theorem mem_foldl_admit_pool_sub (l : List (Vote sp.n)) : ∀ (A : SAState sp.n) {x : Vote sp.n}
    {σ : Nat}, x ∈ (l.foldl (fun A v => admitVote sp A t v) A).pool σ → x ∈ A.pool σ ∨ x ∈ l := by
  induction l with
  | nil => intro A x σ hx; exact Or.inl hx
  | cons v l ih =>
    intro A x σ hx
    rcases ih _ hx with h | h
    · rcases mem_admitVote_pool_sub h with h | h
      · exact Or.inl h
      · exact Or.inr (h ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A vote of a pool after the block receipt of `C` is in the pool before or is a vote of
`C`. -/
theorem mem_blockReceipt_pool_sub {A : SAState sp.n} {C : Blk sp.n FGP} {x : Vote sp.n}
    {σ : Nat} (hx : x ∈ (blockReceipt sp A t C).pool σ) : x ∈ A.pool σ ∨ x ∈ blockVotes C :=
  mem_foldl_admit_pool_sub (t := t) (blockVotes C)
    { A with blockStamp := Function.update A.blockStamp C.root (ETime.of t) } hx

/-- The optimistic confirmation keeps the pools. -/
theorem optimisticConfirmation_pool (A : SAState sp.n) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation
  split
  · rfl
  · unfold updateLatestConfirmed
    split_ifs <;> rfl

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

/-- **The view of a call lies in the votes held before it and the votes it admits.** The votes
and the support of `unlockView A Φ t c` lie in a set `S` that holds the pools of `A`, the votes
and support entries of the blocks of `Φ.tree`, the vote `v` of a call `.message v` and the
votes of the block `C` of a call `.block C`. -/
theorem unlockView_subset_pre {ro : ReplayOrder sp FGP} {A : SAState sp.n}
    (c : (goldilocksSA sp FGP ro).Call) {S : Set (Vote sp.n)}
    (hpre : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S)
    (htree : ∀ C ∈ Φ.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S)
    (hmsg : ∀ v, c = .message v → v ∈ S)
    (hblk : ∀ C, c = .block C → ∀ v ∈ blockVotes C, v ∈ S) :
    (unlockView A Φ t c).votes ⊆ S ∧ (unlockView A Φ t c).support ⊆ S := by
  cases c with
  | tick => rw [unlockView_tick]; exact mergedVoteView_subset hpre htree
  | proposal => rw [unlockView_proposal]; exact voteViewList_subset hpre
  | toFG => rw [unlockView_toFG]; exact mergedVoteView_subset hpre htree
  | restart => rw [unlockView_restart]; exact mergedVoteView_subset hpre htree
  | message v =>
    rw [unlockView_message]
    refine mergedVoteView_subset (fun τ x hx => ?_) htree
    rw [optimisticConfirmation_pool] at hx
    rcases mem_admitVote_pool_sub hx with h | h
    · exact hpre τ x h
    · exact h ▸ hmsg v rfl
  | block C =>
    rw [unlockView_block]
    refine mergedVoteView_subset (fun τ x hx => ?_) htree
    rw [optimisticConfirmation_pool] at hx
    rcases mem_blockReceipt_pool_sub hx with h | h
    · exact hpre τ x h
    · exact hblk C rfl x h

/-- **The O-form, votes held before and after the call.** If `B` is in the tree of a
well-formed frame, `S` is as in `unlockView_subset_post`, and the opponents of `B` in the view
`⟨S, S⟩` lie in a set `O` with `2 · |O| < n`, then `unlock` keeps `B` against the view of the
call. -/
theorem unlockTarget_unlockView_post {ro : ReplayOrder sp FGP} (self : Fin sp.n)
    {A : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) {S : Set (Vote sp.n)}
    (hpre : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S)
    (hpost : ∀ τ, ∀ v ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).1.pool τ, v ∈ S)
    (htree : ∀ C ∈ Φ.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S)
    (s : Int) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {O : Set (Fin sp.n)}
    (hO : opponents sp Φ ⟨S, S⟩ s B ⊆ O) (hOn : 2 * O.ncard < sp.n) :
    unlockTarget sp Φ (unlockView A Φ t c) s B = B := by
  have h := unlockView_subset_post self c hpre hpost htree
  exact unlockTarget_eq_self_of_subset hΦ _ s hB ((opponents_mono_view h.1 h.2 s B).trans hO)
    hOn

/-- **The O-form, votes held before the call and admitted by it.** `unlockTarget_unlockView_post`
with `S` as in `unlockView_subset_pre`. -/
theorem unlockTarget_unlockView_pre {ro : ReplayOrder sp FGP} {A : SAState sp.n}
    (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) {S : Set (Vote sp.n)}
    (hpre : ∀ τ, ∀ v ∈ A.pool τ, v ∈ S)
    (htree : ∀ C ∈ Φ.tree, ∀ v, v ∈ blockVotes C ∨ v ∈ blockSupport C → v ∈ S)
    (hmsg : ∀ v, c = .message v → v ∈ S)
    (hblk : ∀ C, c = .block C → ∀ v ∈ blockVotes C, v ∈ S)
    (s : Int) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {O : Set (Fin sp.n)}
    (hO : opponents sp Φ ⟨S, S⟩ s B ⊆ O) (hOn : 2 * O.ncard < sp.n) :
    unlockTarget sp Φ (unlockView A Φ t c) s B = B := by
  have h := unlockView_subset_pre (t := t) c hpre htree hmsg hblk
  exact unlockTarget_eq_self_of_subset hΦ _ s hB ((opponents_mono_view h.1 h.2 s B).trans hO)
    hOn

/-- The votes held across a call from `A` to `A'` with frame `Φ`: the votes of the pools of `A`
and of `A'`, and the votes and support entries of the blocks of `Φ.tree`. -/
def heldVotes (A A' : SAState sp.n) (Φ : Frm sp.n FGP) : Set (Vote sp.n) :=
  {v | (∃ τ, v ∈ A.pool τ) ∨ (∃ τ, v ∈ A'.pool τ) ∨
    ∃ C ∈ Φ.tree, v ∈ blockVotes C ∨ v ∈ blockSupport C}

theorem mem_heldVotes {A A' : SAState sp.n} {v : Vote sp.n} : v ∈ heldVotes A A' Φ ↔
    (∃ τ, v ∈ A.pool τ) ∨ (∃ τ, v ∈ A'.pool τ) ∨
      ∃ C ∈ Φ.tree, v ∈ blockVotes C ∨ v ∈ blockSupport C :=
  Iff.rfl

/-- **The O-form with the held votes.** For a call `c` from `A` whose state after the call is
`A'`, if the opponents of `B` among the votes held across the call (`heldVotes A A' Φ`, as votes
and as support) lie in a set `O` with `2 · |O| < n`, then `unlock` keeps `B` against the view
of the call. -/
theorem unlockTarget_unlockView_held {ro : ReplayOrder sp FGP} (self : Fin sp.n)
    {A A' : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call)
    (hA' : ((goldilocksSA sp FGP ro).step self A Φ t c).1 = A') (hΦ : FrameOK Φ) (s : Int)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {O : Set (Fin sp.n)}
    (hO : opponents sp Φ ⟨heldVotes A A' Φ, heldVotes A A' Φ⟩ s B ⊆ O)
    (hOn : 2 * O.ncard < sp.n) :
    unlockTarget sp Φ (unlockView A Φ t c) s B = B :=
  unlockTarget_unlockView_post self c hΦ (fun τ _ hv => Or.inl ⟨τ, hv⟩)
    (fun τ _ hv => Or.inr (Or.inl ⟨τ, hA' ▸ hv⟩))
    (fun C hC _ hv => Or.inr (Or.inr ⟨C, hC, hv⟩)) s hB hO hOn

end Consensus.Goldilocks.SA

end
