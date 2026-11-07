module
public import ConsensusLean.Instances.Goldilocks.Statements.Growing
public import ConsensusLean.Main

public section

/-! # Open growing-fault endpoint

The dynamic obligations remain open while the certified constant-fault endpoint
uses the existing milestone proofs. This module is outside the Solution closure.
-/

namespace Consensus.Goldilocks

/-- The dynamic obligations endpoint, pending growing-fault milestone proofs. -/
theorem meetsObligations : MeetsObligations := by
  sorry

/-- Dynamic correctness follows from the open obligations endpoint. -/
theorem goldilocksCorrect : GoldilocksCorrect := fun S A V =>
  Consensus.Shape.ShapeObligations.correct (meetsObligations S A).2 V

end Consensus.Goldilocks
end
