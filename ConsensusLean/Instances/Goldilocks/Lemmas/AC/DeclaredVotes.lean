module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions

public section

/-! # Goldilocks AC: declared head votes at the vote

Facts about the declared head votes of a proposal at a voter, read off the handlers: which
declared votes the merged view counts, that counting survives pool growth, and that an early
vote counts every declared vote of the slot's proposals.

* `shouldCountDeclaredVote_of_mem`, `shouldCountDeclaredVote_mono`: a pool vote should be
  counted, and pool growth keeps a declared vote counted;
* `mem_mergedVoteView_votes_of_declared`, `mem_mergedVoteView_support_of_declared`: a counted
  declared vote (support entry) of a slot-`s` proposal of the tree is in the merged view;
* `allDeclaredVotesCounted_of_tryVote_early`: a vote emitted before `t_s + Δ` counts every declared
  vote of every slot-`s` proposal of the frame, at the state the handler received;
* `tryVote_readPoint_pool`: the read point of an emitted vote has the received state's pool;
* backing, the relation `ShouldCountDeclaredVote` reads on a pool: `x` is backed in a vote set
  `P` when `P` holds `x` or two distinct votes of its validator (`shouldCountDeclaredVote_iff`).
  `backed_mono` (a larger set), `equivocators_subset_of_backed` and `backed_trans` (every vote of
  `P` backed in `Q`). -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams}

section Backing

variable {n : Nat}

/-- **Backing grows with the vote set.** -/
theorem backed_mono {P Q : Set (Vote n)} (hPQ : P ⊆ Q) {x : Vote n}
    (h : x ∈ P ∨ x.val ∈ equivocators P) : x ∈ Q ∨ x.val ∈ equivocators Q := by
  rcases h with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
  · exact Or.inl (hPQ h)
  · exact Or.inr ⟨a, hPQ ha, b, hPQ hb, hab, hav, hbv⟩

/-- **An equivocator of `P` is one of `Q`** when every vote of `P` is backed in `Q`. -/
theorem equivocators_subset_of_backed {P Q : Set (Vote n)}
    (hrel : ∀ v ∈ P, v ∈ Q ∨ v.val ∈ equivocators Q) : equivocators P ⊆ equivocators Q := by
  rintro _ ⟨a, ha, b, hb, hab, rfl, hbv⟩
  rcases hrel a ha with ha' | ha'
  · rcases hrel b hb with hb' | hb'
    · exact ⟨a, ha', b, hb', hab, rfl, hbv⟩
    · exact hbv ▸ hb'
  · exact ha'

/-- **Backing is transitive**: a vote backed in `P` is backed in `Q` when every vote of `P` is. -/
theorem backed_trans {P Q : Set (Vote n)} (hrel : ∀ v ∈ P, v ∈ Q ∨ v.val ∈ equivocators Q)
    {x : Vote n} (h : x ∈ P ∨ x.val ∈ equivocators P) : x ∈ Q ∨ x.val ∈ equivocators Q :=
  h.elim (hrel x) fun h => Or.inr (equivocators_subset_of_backed hrel h)

end Backing

/-- `ShouldCountDeclaredVote` is backing in the pool of the vote's slot. -/
theorem shouldCountDeclaredVote_iff {A : ACState sp.n} {x : Vote sp.n} :
    ShouldCountDeclaredVote sp A x ↔
      x ∈ {w | w ∈ A.poolAt x.slot} ∨ x.val ∈ equivocators {w | w ∈ A.poolAt x.slot} :=
  Iff.rfl

/-- A vote of the pool of its slot should be counted. -/
theorem shouldCountDeclaredVote_of_mem {A : ACState sp.n} {x : Vote sp.n}
    (h : x ∈ A.poolAt x.slot) : ShouldCountDeclaredVote sp A x :=
  Or.inl h

/-- **Pool growth keeps a declared vote counted**: the exact vote stays, and a pair of its
validator stays a pair. -/
theorem shouldCountDeclaredVote_mono {A A' : ACState sp.n} {x : Vote sp.n}
    (hg : ∀ s, A.pool s ⊆ A'.pool s) (h : ShouldCountDeclaredVote sp A x) :
    ShouldCountDeclaredVote sp A' x := by
  refine backed_mono (P := {y | y ∈ A.poolAt x.slot}) (Q := {y | y ∈ A'.poolAt x.slot})
    (fun y (hy : y ∈ A.poolAt x.slot) => ?_) h
  change y ∈ A'.poolAt x.slot
  simp only [ACState.poolAt] at hy ⊢
  split_ifs at hy ⊢ with h0
  · exact hy
  · exact hg _ hy

/-- A counted declared vote of a slot-`s` proposal of the tree is a merged-view vote. -/
theorem mem_mergedVoteView_votes_of_declared {A : ACState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBs : B.slot = s) {x : Vote sp.n}
    (hx : x ∈ declaredHeadVotes B) (hc : ShouldCountDeclaredVote sp A x) :
    x ∈ (mergedVoteView sp A Φ s).votes :=
  Or.inr ⟨B, hB, hBs, hx, hc⟩

/-- A counted support entry `(v, s−1, H)` of a slot-`s` proposal of the tree, with `H` in the tree
and of a slot at most `s − 1`, is a merged-view support vote. -/
theorem mem_mergedVoteView_support_of_declared {A : ACState sp.n} {Φ : Frm sp.n FGP} {s : Nat}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hBs : B.slot = s) {x : Vote sp.n}
    (hx : x ∈ declaredSupportVotes B) (hc : ShouldCountDeclaredVote sp A x) (hxs : x.slot + 1 = s)
    {H : Blk sp.n FGP} (hH : H ∈ Φ.tree) (hHr : H.root = x.head) (hHs : H.slot + 1 ≤ s) :
    x ∈ (mergedVoteView sp A Φ s).support :=
  Or.inr ⟨B, hB, hBs, hx, hc, hxs, H, hH, hHr, hHs⟩

/-- **An early vote counts every declared vote**: when `try_vote` emits before `t_s + Δ`, every
declared vote and support entry of every slot-`s` proposal of the frame should be counted at the
state the handler received. -/
theorem allDeclaredVotesCounted_of_tryVote_early {self : Fin sp.n} {A : ACState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} (hlt : t < sp.ts (sp.slot t) + sp.Δ)
    (hem : (tryVote sp self A Φ t).2 ≠ []) :
    AllDeclaredVotesCounted sp A Φ (sp.slot t) := by
  by_contra hc
  apply hem
  simp only [tryVote]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; exact h2 ⟨hlt, Or.inr fun h => hc h.2⟩)

/-- **The read point of an emitted vote has the received state's pool** (the unlock and
`voted_slot ← s` change neither the pool nor the vote stamps). -/
theorem tryVote_readPoint_pool {self : Fin sp.n} {A : ACState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {e : Em sp FGP} (he : e ∈ (tryVote sp self A Φ t).2) :
    e.readPoint.pool = A.pool := by
  simp only [tryVote] at he
  split_ifs at he with h1 h2 h3 h4 <;>
    simp_all [List.mem_cons, List.not_mem_nil]

end Consensus.Goldilocks.AC

end
