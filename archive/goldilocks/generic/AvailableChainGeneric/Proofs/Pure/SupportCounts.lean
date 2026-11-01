module
public import AvailableChainGeneric.Statements.Pure.SupportCounts
public import Mathlib.Tactic.Push -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

/-- The union lower bound contradicts two strict majorities with no intersection.
DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405 eligible_compatible;
INTENTIONAL: finite-seat intersection conclusion; record
blueprint/02-clean.md:108-130; codex/reports/f2-design-full.md:428. -/
theorem two_majorities_intersect_statement : TwoMajoritiesIntersectStatement := by
  rw [TwoMajoritiesIntersectStatement_def]
  intro n P Q D D' hD hD' hP hQ
  by_contra hn
  have hempty : P ∩ Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hcard := Finset.card_union_add_card_inter P Q
  have hle := Finset.card_le_card hD
  have hle' := Finset.card_le_card hD'
  rw [hempty, Finset.card_empty] at hcard
  omega

/-- Two strict majorities intersect when their union is in both denominators.
DC: Protocol/ForkChoice/Goldfish/Confirmation.lean:405 eligible_compatible;
INTENTIONAL: finite-seat intersection conclusion; record
blueprint/02-clean.md:108-130; codex/reports/f2-design-full.md:428. -/
theorem two_majorities_intersect {n : Nat} {P Q D D' : Finset (Fin n)}
    (hD : P ∪ Q ⊆ D) (hD' : P ∪ Q ⊆ D')
    (hP : D.card < 2 * P.card) (hQ : D'.card < 2 * Q.card) :
    (P ∩ Q).Nonempty :=
  two_majorities_intersect_statement hD hD' hP hQ

end AvailableChain.Gen.Pure
