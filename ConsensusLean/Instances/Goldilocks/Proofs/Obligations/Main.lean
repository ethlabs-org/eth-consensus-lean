module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Obligations.Main
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Obligations.Constant
public import ConsensusLean.Main

public section

/-! # Goldilocks meets the shape obligations on constant faults

The constant-fault pair follows from the growing-fault endpoint, with unchanged
statements and no separate static assembly. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

/-- **Goldilocks meets the obligations on constant faults**: the concrete endpoint. -/
theorem meets_obligations_constant : MeetsObligationsConstant :=
  Growing.meetsObligationsConstant_of_growing Growing.meets_obligations

/-- **Goldilocks is correct on constant faults**: adequacy and realizability remain unrestricted. -/
theorem goldilocks_correct_constant : GoldilocksCorrectConstant := fun S A V =>
  Consensus.Shape.ShapeObligationsOn.correct _ (meets_obligations_constant S A).2 V

end Consensus.Goldilocks.Obligations

end
