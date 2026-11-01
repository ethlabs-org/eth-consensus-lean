module
public import Mathlib.Data.Fintype.Basic -- shake: keep (re-export)
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- Two strict majorities intersect if their union is in both denominator sets.
DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405 eligible_compatible;
INTENTIONAL: extract the finite-seat contradiction before the protocol proves
that conflicting supporter sets are disjoint; record
blueprint/02-clean.md:108-130; codex/reports/f2-design-full.md:428. -/
def TwoMajoritiesIntersectStatement : Prop :=
  ∀ {n : Nat} {P Q D D' : Finset (Fin n)},
    P ∪ Q ⊆ D → P ∪ Q ⊆ D' →
      D.card < 2 * P.card → D'.card < 2 * Q.card → (P ∩ Q).Nonempty

/-- Defining equation. DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405
eligible_compatible; INTENTIONAL: finite-seat intersection conclusion;
record blueprint/02-clean.md:108-130; codex/reports/f2-design-full.md:428. -/
theorem TwoMajoritiesIntersectStatement_def : TwoMajoritiesIntersectStatement =
    (∀ {n : Nat} {P Q D D' : Finset (Fin n)},
      P ∪ Q ⊆ D → P ∪ Q ⊆ D' →
        D.card < 2 * P.card → D'.card < 2 * Q.card → (P ∩ Q).Nonempty) := by rfl

end AvailableChain.Gen.Pure
