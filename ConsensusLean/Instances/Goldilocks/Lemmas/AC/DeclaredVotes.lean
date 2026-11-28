module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions

public section

/-! # Goldilocks AC: backing for declared votes

A vote is backed in a set when the set holds that vote or two distinct votes of its validator.
This is the relation `ShouldCountDeclaredVote` reads on the pool. -/

namespace Consensus.Goldilocks.AC

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

end Consensus.Goldilocks.AC

end
