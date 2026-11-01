module
public import AvailableChainGeneric.Statements.Pure.SlotGrid

@[expose] public section

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- The first inclusive opening is at most P - 4Δ after a gate.
Consumers: F5.HG.1 and F5.HG.3. Sources: 21:1343–1346,1413–1415,1488–1506.
DC: additive (no DC counterpart); reason:
the gate-grid bound is sharper than least-action selection. -/
def FirstOpeningAfterGateStatement : Prop :=
  ∀ (Δ : Time) (R q r : Nat), 0 < Δ → 1 ≤ R →
    (d Δ q ≤ a Δ R r ∧ ∀ j : Nat, j < r → a Δ R j < d Δ q) →
    0 ≤ a Δ R r - d Δ q ∧
      a Δ R r - d Δ q ≤ P Δ R - 4 * Δ

/-- This equation unfolds the closed contract.
Consumers: F5.HG.1 and F5.HG.3. Sources: 21:1343–1346,1413–1415,1488–1506.
DC: additive (no DC counterpart); reason:
the gate-grid bound is sharper than least-action selection. -/
theorem FirstOpeningAfterGateStatement_def : FirstOpeningAfterGateStatement =
    (∀ (Δ : Time) (R q r : Nat), 0 < Δ → 1 ≤ R →
    (d Δ q ≤ a Δ R r ∧ ∀ j : Nat, j < r → a Δ R j < d Δ q) →
    0 ≤ a Δ R r - d Δ q ∧
      a Δ R r - d Δ q ≤ P Δ R - 4 * Δ) := by rfl

end AvailableChain.Gen.Pure
