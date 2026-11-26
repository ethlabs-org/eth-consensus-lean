module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Views
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Goldilocks AC: counting two incompatible sides of a pool

A vote `x` is backed in a vote set `P` when `P` holds `x` or two distinct votes of its validator.

* `voter_of_backed`: the validator of a backed vote is a voter of `P`;
* `side_count`: validators `T` each backed in `P` by a vote for a block `D`, and non-equivocating
  supporters `S` in `P` of a block `DY` incompatible with `D`, are disjoint voters of `P`, so
  `|T| + |S| ≤ |voters P|`. -/

namespace Consensus.Goldilocks.AC

variable {n : Nat} {FGP : Type}

/-- **A backed vote's validator is a voter.** -/
theorem voter_of_backed {P : Set (Vote n)} {x : Vote n}
    (h : x ∈ P ∨ x.val ∈ equivocators P) : x.val ∈ voters P := by
  rcases h with h | ⟨a, ha, -, -, -, hav, -⟩
  · exact ⟨x, h, rfl⟩
  · exact ⟨a, ha, hav⟩

/-- **Two incompatible sides of a vote set occupy disjoint voters.** In a coherent `U`, the
validators `T`, each with a vote backed in `P` whose head is at or above `D`, and the supporters
`S`, each not an equivocator of `P` and with a vote of `P` whose head is at or above `DY`, are
disjoint voters of `P` when `D` and `DY` are incompatible. -/
theorem side_count {U : Set (Blk n FGP)} (hU : Coherent U) {P : Set (Vote n)}
    {D DY : Blk n FGP} {S T : Set (Fin n)}
    (hS : ∀ u ∈ S, u ∉ equivocators P ∧
      ∃ v ∈ P, v.val = u ∧ ∃ R ∈ U, R.root = v.head ∧ Anc U DY R)
    (hT : ∀ u ∈ T, ∃ v : Vote n, v.val = u ∧ (∃ R ∈ U, R.root = v.head ∧ Anc U D R) ∧
      (v ∈ P ∨ u ∈ equivocators P))
    (hnc : ¬ Compatible U D DY) :
    T.ncard + S.ncard ≤ (voters P).ncard := by
  have hdisj : Disjoint T S := by
    rw [Set.disjoint_left]
    intro u hu hu'
    obtain ⟨hne, v', hv', hv'u, R', hR', hR'r, hDR'⟩ := hS u hu'
    obtain ⟨v, hvu, ⟨R, hR, hRr, hDR⟩, hv | heq⟩ := hT u hu
    · obtain rfl : v = v' := by
        by_contra h
        exact hne ⟨v, hv, v', hv', h, hvu, hv'u⟩
      obtain rfl : R = R' := hU.1 hR hR' (hRr.trans hR'r.symm)
      exact hnc (Anc.total hU hDR hDR')
    · exact hne heq
  rw [← Set.ncard_union_eq hdisj]
  refine Set.ncard_le_ncard ?_
  rintro u (hu | hu)
  · obtain ⟨v, rfl, -, h⟩ := hT u hu
    exact voter_of_backed h
  · obtain ⟨-, v, hv, rfl, -⟩ := hS u hu
    exact ⟨v, hv, rfl⟩

end Consensus.Goldilocks.AC

end
