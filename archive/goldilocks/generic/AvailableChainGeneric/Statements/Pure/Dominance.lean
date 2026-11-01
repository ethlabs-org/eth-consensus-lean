module
public import AvailableChainGeneric.Statements.Pure.Quorum -- shake: keep (re-export)
public import AvailableChainModel.Objects.Blocks
public import Mathlib.Data.Finset.Card -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- At most one child has a strict majority of disjoint counted support sets.
DC: Goldfish/Confirmation.lean:405, 419–423; INTENTIONAL (lead ruling 2026-10-01): the count step of
eligible_compatible. -/
def MajUniqueChildStatement : Prop :=
  ∀ {n : Nat}
    (children : Finset Block)
    (support : Block → Finset (Fin n))
    (denominator : Finset (Fin n)),
    (∀ C ∈ children, support C ⊆ denominator) →
    (∀ C ∈ children, ∀ D ∈ children,
      C ≠ D → Disjoint (support C) (support D)) →
    ∀ C ∈ children, ∀ D ∈ children,
      denominator.card < 2 * (support C).card →
      denominator.card < 2 * (support D).card →
      C = D

/-- Defining equation.
DC: Goldfish/Confirmation.lean:405, 419–423; INTENTIONAL (lead ruling 2026-10-01): the count step of
eligible_compatible. -/
theorem MajUniqueChildStatement_def :
    MajUniqueChildStatement =
      (∀ {n : Nat}
        (children : Finset Block)
        (support : Block → Finset (Fin n))
        (denominator : Finset (Fin n)),
        (∀ C ∈ children, support C ⊆ denominator) →
        (∀ C ∈ children, ∀ D ∈ children,
          C ≠ D → Disjoint (support C) (support D)) →
        ∀ C ∈ children, ∀ D ∈ children,
          denominator.card < 2 * (support C).card →
          denominator.card < 2 * (support D).card →
          C = D) := by rfl

end AvailableChain.Gen.Pure
