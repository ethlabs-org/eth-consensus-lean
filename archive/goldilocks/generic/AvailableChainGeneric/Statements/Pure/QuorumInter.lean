module
public import AvailableChainGeneric.Statements.Pure.Quorum
public import Mathlib.Data.Finset.Card -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- Two unit-seat quorums have a member outside the faulty set.
DC: Generic/Conditions.lean:180 BelowOneThird; INTENTIONAL: unit-seat two-quorum bound;
record gly319/generic-layer.md:1297 (GLY r3.19 S044). -/
def FaultXInterHonestStatement : Prop :=
  ∀ {n a : Nat} {Q Q' F : Finset (Fin n)},
    FaultX n a → F.card ≤ a → qF n ≤ Q.card → qF n ≤ Q'.card →
      ∃ v ∈ Q ∩ Q', v ∉ F

/-- Defining equation.
DC: Generic/Conditions.lean:180 BelowOneThird; INTENTIONAL: unit-seat two-quorum bound;
record gly319/generic-layer.md:1297 (GLY r3.19 S044). -/
theorem FaultXInterHonestStatement_def : FaultXInterHonestStatement =
    (∀ {n a : Nat} {Q Q' F : Finset (Fin n)},
      FaultX n a → F.card ≤ a → qF n ≤ Q.card → qF n ≤ Q'.card →
        ∃ v ∈ Q ∩ Q', v ∉ F) := by rfl

end AvailableChain.Gen.Pure
