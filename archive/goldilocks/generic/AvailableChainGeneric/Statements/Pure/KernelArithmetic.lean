module
public import AvailableChainGeneric.Statements.Pure.SlotGrid

@[expose] public section

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- KernelArithmeticStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
def KernelArithmeticStatement : Prop :=
  ∀ (Δ : Time) (R q r : Nat), 0 < Δ → 2 ≤ R →
    T Δ R q + 9 * Δ < a Δ R (q + 1) ∧
    v Δ (q * R + 1) < a Δ R q ∧
    t Δ (q * R + 2) < d Δ (q * R + 1) ∧
    a Δ R r + Δ < T Δ R r + 8 * Δ

/-- KernelArithmeticStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem KernelArithmeticStatement_def : KernelArithmeticStatement =
    (∀ (Δ : Time) (R q r : Nat), 0 < Δ → 2 ≤ R →
      T Δ R q + 9 * Δ < a Δ R (q + 1) ∧
      v Δ (q * R + 1) < a Δ R q ∧
      t Δ (q * R + 2) < d Δ (q * R + 1) ∧
      a Δ R r + Δ < T Δ R r + 8 * Δ) := by rfl

-- These equations also connect the four inequalities to the lane's
-- existing ActionDeliveryBounds and carrierTime2 definitions.
/-- ActionCarrierArithmeticStatement gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
def ActionCarrierArithmeticStatement : Prop :=
  ∀ (Δ : Time) (R r : Nat), 0 < Δ → 2 ≤ R →
    a Δ R r + Δ = T Δ R r + 7 * Δ ∧
    t Δ (r * R + 2) = T Δ R r + 8 * Δ ∧
    a Δ R r + Δ < T Δ R (r + 1)

/-- ActionCarrierArithmeticStatement_def gives the scalar contract or its defining equation.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem ActionCarrierArithmeticStatement_def : ActionCarrierArithmeticStatement =
    (∀ (Δ : Time) (R r : Nat), 0 < Δ → 2 ≤ R →
      a Δ R r + Δ = T Δ R r + 7 * Δ ∧
      t Δ (r * R + 2) = T Δ R r + 8 * Δ ∧
      a Δ R r + Δ < T Δ R (r + 1)) := by rfl

end AvailableChain.Gen.Pure
