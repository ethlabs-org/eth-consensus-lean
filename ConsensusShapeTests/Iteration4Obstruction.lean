module
public import ConsensusProblem.Basic
public import Mathlib.Tactic
@[expose] public section

namespace Consensus.Shape.Tests

open Consensus

/-- The inclusive endpoint permitted by iteration 4 forces an empty faulty set.
This contradicts the requested active fast-outage witness with nonempty faults. -/
theorem iteration4_inclusive_endpoint_obstruction
    {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V) (c t : Time)
    (h : (1 : ℚ) * Fintype.card V ≤ ((p.readyAt c t).card : ℚ)) :
    p.faulty = ∅ := by
  classical
  have hr : p.readyAt c t ⊆ p.honest := Finset.filter_subset _ _
  have hc := Finset.card_le_card hr
  have hh : p.honest.card ≤ Fintype.card V := Finset.card_le_univ _
  have hn : Fintype.card V ≤ (p.readyAt c t).card := by
    exact_mod_cast (by simpa using h : (Fintype.card V : ℚ) ≤ (p.readyAt c t).card)
  have heq : p.honest = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using (hn.trans hc))
  simp [EnvPoint.faulty, heq]

end Consensus.Shape.Tests
end
