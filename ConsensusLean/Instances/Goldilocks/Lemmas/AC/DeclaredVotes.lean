module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Actions

public section

/-! # Goldilocks SA: declared head votes at the vote

Facts about the declared head votes of a proposal at a voter, read off the handlers: which
declared votes the merged view counts, that counting survives pool growth, and that an early
vote counts every declared vote of the slot's proposals.

* `shouldCountDeclaredVote_of_mem`, `shouldCountDeclaredVote_mono`: a pool vote should be
  counted, and pool growth keeps a declared vote counted;
* `mem_mergedVoteView_votes_of_declared`, `mem_mergedVoteView_support_of_declared`: a counted
  declared vote (support entry) of a slot-`s` proposal of the tree is in the merged view;
* `allDeclaredVotesCounted_of_tryVote_early`: a vote emitted before `t_s + Δ` counts every declared
  vote of every slot-`s` proposal of the frame, at the state the handler received;
* `tryVote_readPoint_pool`: the read point of an emitted vote has the received state's pool. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- A vote of the pool of its slot should be counted. -/
theorem shouldCountDeclaredVote_of_mem {A : SAState sp.n} {x : Vote sp.n}
    (h : x ∈ A.poolAt x.slot) : ShouldCountDeclaredVote sp A x :=
  Or.inl h

/-- **Pool growth keeps a declared vote counted**: the exact vote stays, and a pair of its
validator stays a pair. -/
theorem shouldCountDeclaredVote_mono {A A' : SAState sp.n} {x : Vote sp.n}
    (hg : ∀ s, A.pool s ⊆ A'.pool s) (h : ShouldCountDeclaredVote sp A x) :
    ShouldCountDeclaredVote sp A' x := by
  have hp : ∀ y, y ∈ A.poolAt x.slot → y ∈ A'.poolAt x.slot := fun y hy => by
    simp only [SAState.poolAt] at hy ⊢
    split_ifs at hy ⊢ with h0
    · exact hy
    · exact hg _ hy
  rcases h with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · exact Or.inl (hp x h)
  · exact Or.inr ⟨a, hp a ha, b, hp b hb, hab, hav, hbv⟩

/-- A counted declared vote of a slot-`s` proposal of the tree is a merged-view vote. -/
theorem mem_mergedVoteView_votes_of_declared {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBs : B.slot = s) {x : Vote sp.n}
    (hx : x ∈ blockVotes B) (hc : ShouldCountDeclaredVote sp A x) :
    x ∈ (mergedVoteView sp A Φ s).votes :=
  Or.inr ⟨B, hB, hBs, hx, by simp [SAParams.committee], hc⟩

/-- A counted support entry `(v, s−1, H)` of a slot-`s` proposal of the tree, with `H` in the tree
and of a slot at most `s − 1`, is a merged-view support vote. -/
theorem mem_mergedVoteView_support_of_declared {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBs : B.slot = s) {x : Vote sp.n}
    (hx : x ∈ blockSupport B) (hc : ShouldCountDeclaredVote sp A x) (hxs : x.slot + 1 = s)
    {H : Blk sp.n FGP} (hH : H ∈ Φ.tree) (hHr : H.root = x.head) (hHs : H.slot + 1 ≤ s) :
    x ∈ (mergedVoteView sp A Φ s).support :=
  Or.inr ⟨B, hB, hBs, hx, by simp [SAParams.committee], hc, hxs, H, hH, hHr, hHs⟩

/-- **An early vote counts every declared vote**: when `try_vote` emits before `t_s + Δ`, every
declared vote and support entry of every slot-`s` proposal of the frame should be counted at the
state the handler received. -/
theorem allDeclaredVotesCounted_of_tryVote_early {self : Fin sp.n} {A : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} (hlt : t < sp.ts (sp.slot t) + sp.Δ)
    (hem : (tryVote sp self A Φ t).2 ≠ []) :
    AllDeclaredVotesCounted sp A Φ (sp.slot t) := by
  by_contra hc
  apply hem
  simp only [tryVote]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; exact h2 ⟨hlt, Or.inr fun h => hc h.2⟩)

/-- **The read point of an emitted vote has the received state's pool** (the unlock and
`voted_slot ← s` change neither the pool nor the vote stamps). -/
theorem tryVote_readPoint_pool {self : Fin sp.n} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {e : Em sp FGP} (he : e ∈ (tryVote sp self A Φ t).2) :
    e.readPoint.pool = A.pool := by
  simp only [tryVote] at he
  split_ifs at he with h1 h2 h3 h4 <;>
    simp_all [List.mem_cons, List.not_mem_nil]

end Consensus.Goldilocks.SA

end
