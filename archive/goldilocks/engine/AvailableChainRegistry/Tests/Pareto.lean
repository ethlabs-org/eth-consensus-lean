module
public import AvailableChainFramework

@[expose] public section

namespace AvailableChain.Registry.Tests

open AvailableChain AvailableChain.Framework

/-- A toy two-constant claim: an arming lag (smaller is stronger) and a
budget (larger is stronger), with no regime. -/
def armedToy : ClaimSpec ClaimDomain.v1 where
  id := `test.armedToy.v1
  Const := Time × Time
  valid := fun _ => True
  le := fun a b => decide (a.1 ≤ b.1 ∧ b.2 ≤ a.2)
  le_refl := fun _ => decide_eq_true ⟨le_rfl, le_rfl⟩
  le_trans := by
    intro a b c hab hbc
    have h1 := of_decide_eq_true hab
    have h2 := of_decide_eq_true hbc
    exact decide_eq_true ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩
  Point := Unit
  regime := fun _ _ _ _ _ => True
  conclusion := fun _ _ _ _ _ => True
  trigger := fun _ _ _ _ _ _ => True
  transport := by intro _ _ _ _ _ _ _ W x hΔ p _; trivial
  refutable := .none

/-- `armedToy.Const` does not unfold during instance search. -/
instance : DecidableEq armedToy.Const := inferInstanceAs (DecidableEq (Time × Time))

-- (4,10) beats (5,10) and (4,8); (6,20) is incomparable with (4,10).
example : armedToy.pareto [(5, 10), (4, 10), (6, 20), (4, 8)] = [(4, 10), (6, 20)] := by
  rfl
-- The direction matters: a weaker constant never removes a stronger one.
example : armedToy.pareto [(4, 10), (5, 9)] = [(4, 10)] := by rfl

end AvailableChain.Registry.Tests

end
