module
public import AvailableChainGeneric.Statements.Pure.SlotGrid

@[expose] public section

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- The first HEAD at the settlement threshold has the Int ceiling proposal time.
Consumers: F5.HG.7 and F5.HG.8a. Sources: S1b:815–817; 21:1721–1727,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA repair input. -/
def FirstHeadAfterStatement : Prop :=
  ∀ (Δ w : Time) (b : Nat), 0 < Δ → 0 ≤ w + 2 * Δ →
    (w + 3 * Δ ≤ v Δ b ∧
      ∀ j : Nat, j < b → v Δ j < w + 3 * Δ) →
    t Δ b = 4 * Δ * ((w + 2 * Δ + 4 * Δ - 1) / (4 * Δ))

/-- This equation unfolds the closed contract.
Consumers: F5.HG.7 and F5.HG.8a. Sources: S1b:815–817; 21:1721–1727,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA repair input. -/
theorem FirstHeadAfterStatement_def : FirstHeadAfterStatement =
    (∀ (Δ w : Time) (b : Nat), 0 < Δ → 0 ≤ w + 2 * Δ →
    (w + 3 * Δ ≤ v Δ b ∧
      ∀ j : Nat, j < b → v Δ j < w + 3 * Δ) →
    t Δ b = 4 * Δ * ((w + 2 * Δ + 4 * Δ - 1) / (4 * Δ))) := by rfl

/-- An upper bound on the settlement cut bounds the first HEAD proposal time.
Consumers: F5.HG.7 and F5.HG.8a. Sources: S1b:815–817; 21:1721–1727,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA repair input. -/
def FirstHeadAfterBoundStatement : Prop :=
  ∀ (Δ w U : Time) (b : Nat), 0 < Δ → 0 ≤ w + 2 * Δ → w ≤ U →
    (w + 3 * Δ ≤ v Δ b ∧
      ∀ j : Nat, j < b → v Δ j < w + 3 * Δ) →
    t Δ b ≤ 4 * Δ * ((U + 2 * Δ + 4 * Δ - 1) / (4 * Δ))

/-- This equation unfolds the closed contract.
Consumers: F5.HG.7 and F5.HG.8a. Sources: S1b:815–817; 21:1721–1727,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA repair input. -/
theorem FirstHeadAfterBoundStatement_def : FirstHeadAfterBoundStatement =
    (∀ (Δ w U : Time) (b : Nat), 0 < Δ → 0 ≤ w + 2 * Δ → w ≤ U →
    (w + 3 * Δ ≤ v Δ b ∧
      ∀ j : Nat, j < b → v Δ j < w + 3 * Δ) →
    t Δ b ≤ 4 * Δ * ((U + 2 * Δ + 4 * Δ - 1) / (4 * Δ))) := by rfl

end AvailableChain.Gen.Pure
