module
public import AvailableChainGeneric.Statements.Pure.Stages -- shake: keep (re-export)
public import Mathlib.Data.Int.DivMod -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- A fixed periodic stage fold has the same elapsed value at one residue.
Consumers: F5.HG.7 and F5.HG.8a. Sources: 21:1695,1709–1717,2210–2217.
DC: additive (no DC counterpart); reason: fixed periodic deadline composition is a scalar helper. -/
def PeriodicShiftStatement : Prop :=
  ∀ {n : Nat} (f : Fin n → Int → Int) (P Δ u₀ : Int),
    0 < P → 0 ≤ 6 * Δ → 6 * Δ < P →
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    (∀ i x, f i (x + P) = f i x + P) → u₀ % P = 6 * Δ →
    (List.finRange n).foldl (fun x i => f i x) u₀ - u₀ =
      (List.finRange n).foldl (fun x i => f i x) (6 * Δ) - 6 * Δ

/-- This equation unfolds the closed contract.
Consumers: F5.HG.7 and F5.HG.8a. Sources: 21:1695,1709–1717,2210–2217.
DC: additive (no DC counterpart); reason: fixed periodic deadline composition is a scalar helper. -/
theorem PeriodicShiftStatement_def : PeriodicShiftStatement =
    (∀ {n : Nat} (f : Fin n → Int → Int) (P Δ u₀ : Int),
    0 < P → 0 ≤ 6 * Δ → 6 * Δ < P →
    (∀ i, Monotone (f i)) → (∀ i x, x ≤ f i x) →
    (∀ i x, f i (x + P) = f i x + P) → u₀ % P = 6 * Δ →
    (List.finRange n).foldl (fun x i => f i x) u₀ - u₀ =
      (List.finRange n).foldl (fun x i => f i x) (6 * Δ) - 6 * Δ) := by rfl

end AvailableChain.Gen.Pure
