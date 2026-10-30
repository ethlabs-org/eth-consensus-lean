module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Tree

public section

/-! # Goldilocks: ancestry facts

Ancestry inside a set of blocks grows with the set; a proper ancestry has both ends in the set;
ancestry below a common ancestor stays inside the blocks that extend it; adding a block that no
block of the set names as its parent leaves the ancestry of the set's blocks unchanged; and a
subset of a coherent set is coherent. -/

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type} {S T : Set (Block n FGP ACP)} {A B C X : Block n FGP ACP}

theorem Anc.mono (hST : S ⊆ T) (h : Anc S B C) : Anc T B C := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ e ih => exact ih.tail ⟨hST e.1, hST e.2.1, e.2.2⟩

theorem Anc.mem (h : Anc S B C) (hne : B ≠ C) : B ∈ S ∧ C ∈ S := by
  obtain rfl | ⟨c, e, -⟩ := Relation.ReflTransGen.cases_head_iff.1 h
  · exact absurd rfl hne
  obtain rfl | ⟨b, -, e'⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h
  · exact absurd rfl hne
  exact ⟨e.1, e'.2.1⟩

/-- Ancestry between descendants of `A` stays inside the blocks that extend `A`. -/
theorem Anc.restrict (hAB : Anc S A B) (h : Anc S B C) : Anc {Y | Y ∈ S ∧ Anc S A Y} B C := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hb e ih =>
    exact ih.tail ⟨⟨e.1, hAB.trans hb⟩, ⟨e.2.1, (hAB.trans hb).tail e⟩, e.2.2⟩

/-- Adding a block `X` that no block of `S` names as its parent leaves the ancestors of the
blocks of `S` unchanged. -/
theorem Anc.of_insert (h : Anc (insert X S) B C) (hC : C ∈ S)
    (hX : ∀ V ∈ S, V.parent ≠ some X.root) : Anc S B C := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ e ih =>
    have hb : b ∈ S := by
      rcases e.1 with rfl | hb
      · exact absurd e.2.2 (hX c hC)
      · exact hb
    exact (ih hb).tail ⟨hb, hC, e.2.2⟩

theorem Coherent.mono (hST : S ⊆ T) (h : Coherent T) : Coherent S :=
  ⟨fun _ hB _ hC => h.1 (hST hB) (hST hC), fun B hB C hC => h.2 B (hST hB) C (hST hC)⟩

end Consensus.Goldilocks

end
