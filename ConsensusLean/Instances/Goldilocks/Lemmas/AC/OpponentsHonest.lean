module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockViewOpponents

public section

/-! # Goldilocks SA: the opponents of a block are outside the validators that do not oppose it

The static half of the drain link of consensus-lean#135 (WI-15/16; r14 s1 L1.2). Let `Hn` be a
set of validators (the honest ones). If no validator of `Hn` equivocates in the votes of a view,
and every slot-`s` support vote of a validator of `Hn` has heads in the tree that are compatible
with `B`, then the opponents of `B` lie outside `Hn` (`opponents_subset_compl`). With
`2 · |Hnᶜ| < n`, `unlock` keeps `B` against the view of a call
(`unlockTarget_unlockView_held_of_honest`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {Φ : Frm sp.n FGP} {t : Time}

/-- **The opponents of `B` are not in `Hn`** when no validator of `Hn` equivocates in
`V.votes` and every slot-`s` support vote of `Hn` has only heads compatible with `B`. -/
theorem opponents_subset_compl {V : View sp.n} {s : Int} {B : Blk sp.n FGP}
    {Hn : Set (Fin sp.n)}
    (hne : ∀ x ∈ V.votes, ∀ y ∈ V.votes, x.val ∈ Hn → y.val = x.val → x = y)
    (hcompat : ∀ x ∈ V.support, x.val ∈ Hn → (x.slot : Int) = s →
      ∀ H ∈ Φ.tree, H.root = x.head → Compatible Φ.tree H B) :
    opponents sp Φ V s B ⊆ Hnᶜ := by
  rintro i (⟨x, hx, y, hy, hxy, rfl, hyi⟩ | ⟨x, hx, rfl, hs, H, hH, hr, hc⟩) hi
  · exact hxy (hne x hx y hy hi hyi)
  · exact hc (hcompat x hx hi hs H hH hr)

/-- **`unlock` keeps `B` when `Hn` does not oppose it.** For a call `c` from `A` to `A'`, if no
validator of `Hn` equivocates in the held votes, every held slot-`s` vote of `Hn` has only
heads compatible with `B`, and `2 · |Hnᶜ| < n`, then `unlockTarget` of the call's view is `B`. -/
theorem unlockTarget_unlockView_held_of_honest {ro : ReplayOrder sp FGP} (self : Fin sp.n)
    {A A' : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call)
    (hA' : ((goldilocksSA sp FGP ro).step self A Φ t c).1 = A') (hΦ : FrameOK Φ) (s : Int)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {Hn : Set (Fin sp.n)}
    (hne : ∀ x ∈ heldVotes A A' Φ, ∀ y ∈ heldVotes A A' Φ, x.val ∈ Hn → y.val = x.val → x = y)
    (hcompat : ∀ x ∈ heldVotes A A' Φ, x.val ∈ Hn → (x.slot : Int) = s →
      ∀ H ∈ Φ.tree, H.root = x.head → Compatible Φ.tree H B)
    (hf : 2 * Hnᶜ.ncard < sp.n) :
    unlockTarget sp Φ (unlockView A Φ t c) s B = B :=
  unlockTarget_unlockView_held self c hA' hΦ s hB
    (opponents_subset_compl (V := ⟨heldVotes A A' Φ, heldVotes A A' Φ⟩) hne hcompat) hf

end Consensus.Goldilocks.SA

end
