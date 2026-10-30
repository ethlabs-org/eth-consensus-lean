module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Goldilocks: ancestry is a tree order inside a coherent set (claims F.2 (a), (b))

Inside a coherent set (roots injective, slots increasing along parent edges): slots increase
strictly along strict ancestry, so ancestry is antisymmetric, and the ancestors of a block form
a chain (a block has at most one parent in the set). -/

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type} {S : Set (Block n FGP ACP)}

/-- Slots do not decrease along ancestry, and increase strictly along strict ancestry. -/
theorem Anc.slot_le (hS : Coherent S) {B C : Block n FGP ACP} (h : Anc S B C) :
    B.slot ≤ C.slot ∧ (B ≠ C → B.slot < C.slot) := by
  induction h with
  | refl => exact ⟨Nat.le_refl _, fun h => absurd rfl h⟩
  | tail _ hYC ih =>
    have hlt := hS.2 _ hYC.1 _ hYC.2.1 hYC.2.2
    exact ⟨Nat.le_trans ih.1 (Nat.le_of_lt hlt), fun _ => Nat.lt_of_le_of_lt ih.1 hlt⟩

/-- **F.2 (a).** Inside a coherent set, ancestry is antisymmetric. -/
theorem Anc.antisymm (hS : Coherent S) {B C : Block n FGP ACP} (h : Anc S B C)
    (h' : Anc S C B) : B = C := by
  by_contra hne
  have := (h.slot_le hS).2 hne
  have := (h'.slot_le hS).1
  omega

/-- **F.2 (b).** Inside a coherent set, two ancestors of one block are compatible. -/
theorem Anc.total (hS : Coherent S) {A A' C : Block n FGP ACP} (h : Anc S A C)
    (h' : Anc S A' C) : Anc S A A' ∨ Anc S A' A := by
  revert h
  induction h' with
  | refl => exact fun h => Or.inl h
  | @tail Y C hA'Y hYC ih =>
    intro h
    rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y', hAY', hY'C⟩
    · subst heq
      exact Or.inr (hA'Y.tail hYC)
    · have : Y' = Y := hS.1 hY'C.1 hYC.1 (Option.some.inj (hY'C.2.2.symm.trans hYC.2.2))
      subst this
      exact ih hAY'

end Consensus.Goldilocks

end
