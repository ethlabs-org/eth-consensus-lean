module
public import ConsensusLean.Instances.Goldilocks.Statements.Growing
public import ConsensusLean.Main

public section

/-! # Open growing-fault endpoint

The dynamic obligations remain open while the certified constant-fault endpoint
uses the existing milestone proofs. This module is outside the Solution closure.
Certification of the dynamic roots also requires the compiled proposer hold-zero
counterexample, after the dynamic sleepy invariant is proved.
-/

namespace Consensus.Goldilocks.Growing

/-- The dynamic obligations endpoint, pending growing-fault milestone proofs. -/
theorem meets_obligations : MeetsObligations := by
  sorry

/-- Dynamic correctness follows from the open obligations endpoint. -/
theorem goldilocks_correct : GoldilocksCorrect := fun S A V =>
  Consensus.Shape.ShapeObligations.correct (meets_obligations S A).2 V

end Consensus.Goldilocks.Growing
end
