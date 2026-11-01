module
public import AvailableChainGeneric.Statements.Pure.Stages -- shake: keep (re-export)
public import Mathlib.Algebra.BigOperators.Fin -- shake: keep (re-export)
public import Mathlib.Data.Int.Basic -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.Pure

open scoped BigOperators

/-- An additive stage fold equals its start plus the sum of increments.
Consumers: F5.H.10, H.11, HG.6 and H.11-Q. Sources: 21:1293–1318,1619–1622,1654–1663,2429–2439.
DC: additive (no DC counterpart); reason: ordered deadline sums are a new scalar helper. -/
def ComposeStagesAddStatement : Prop :=
  ∀ {α : Type} [AddCommMonoid α] {n : Nat}
    (f : Fin n → α → α) (c : Fin n → α),
    (∀ i x, f i x = x + c i) → ∀ u₀ : α,
      (List.finRange n).foldl (fun x i => f i x) u₀ = u₀ + ∑ i, c i

/-- This equation unfolds the closed contract.
Consumers: F5.H.10, H.11, HG.6 and H.11-Q. Sources: 21:1293–1318,1619–1622,1654–1663,2429–2439.
DC: additive (no DC counterpart); reason: ordered deadline sums are a new scalar helper. -/
theorem ComposeStagesAddStatement_def : ComposeStagesAddStatement =
    (∀ {α : Type} [AddCommMonoid α] {n : Nat}
    (f : Fin n → α → α) (c : Fin n → α),
    (∀ i x, f i x = x + c i) → ∀ u₀ : α,
      (List.finRange n).foldl (fun x i => f i x) u₀ = u₀ + ∑ i, c i) := by rfl

/-- Nonnegative budgets bound every increasing visited sequence.
Consumers: F5.H.10, H.11, HG.6 and H.11-Q. Sources: 21:1293–1318,1619–1622,1654–1663,2429–2439.
DC: additive (no DC counterpart); reason: ordered deadline sums are a new scalar helper. -/
def OrderedStagesAddBoundStatement : Prop :=
  ∀ {n : Nat} (f : Fin n → Int → Int) (c : Fin n → Int),
    (∀ i x, f i x = x + c i) → (∀ i, 0 ≤ c i) →
    ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ u₀ : Int,
      vis.foldl (fun x i => f i x) u₀ ≤ u₀ + ∑ i, c i

/-- This equation unfolds the closed contract.
Consumers: F5.H.10, H.11, HG.6 and H.11-Q. Sources: 21:1293–1318,1619–1622,1654–1663,2429–2439.
DC: additive (no DC counterpart); reason: ordered deadline sums are a new scalar helper. -/
theorem OrderedStagesAddBoundStatement_def : OrderedStagesAddBoundStatement =
    (∀ {n : Nat} (f : Fin n → Int → Int) (c : Fin n → Int),
    (∀ i x, f i x = x + c i) → (∀ i, 0 ≤ c i) →
    ∀ (vis : List (Fin n)), vis.Pairwise (· < ·) → ∀ u₀ : Int,
      vis.foldl (fun x i => f i x) u₀ ≤ u₀ + ∑ i, c i) := by rfl

end AvailableChain.Gen.Pure
