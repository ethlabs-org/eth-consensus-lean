module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Main
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Obligations.Constant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Endpoint
public import ConsensusLean.Lemmas.Shape.OnRuns

public section

/-! # The growing-fault obligations endpoint

`MeetsObligations` (`Statements/Obligations`) at every vote binding from the shape obligations of
`Lemmas/Growing/Obligations/Concrete/Endpoint` (`meetsObligations_growing`, the capstone at the
Goldilocks engine binding) and the profile label (`schema_matches_ebbAndFlow`); the headline
`GoldilocksCorrect` by `ShapeObligations.correct`. The stock constant-fault endpoint
follows from the endpoint at the stock setup (`meetsObligationsConstant_of_growing`). This module is
the Goldilocks entry of the comparator solution. The compiled proposer hold-zero counterexample
(`ConsensusLeanTest/Goldilocks/Regimes/ProposerHold.lean`) shows the hold `1` of the contract is
needed. -/

namespace Consensus.Goldilocks.Obligations

/-- The Goldilocks schema provides the final, stable and available capabilities. -/
theorem schema_matches_ebbAndFlow : Profile.ebbAndFlow.Matches AsChainShape.schema := by
  intro cap; cases cap <;> rfl

end Consensus.Goldilocks.Obligations

namespace Consensus.Goldilocks.Growing

/-- **Goldilocks meets the obligations**: the concrete endpoint. -/
theorem meets_obligations : MeetsObligations := fun S A =>
  ⟨Obligations.schema_matches_ebbAndFlow, Obligations.Growing.meetsObligations_growing S A⟩

/-- **Goldilocks is correct**: the endpoint composed with `ShapeObligations.correct`. -/
theorem goldilocks_correct : GoldilocksCorrect := fun S A V =>
  ⟨Consensus.Shape.ShapeObligations.correct (meets_obligations S A).2 V,
    Obligations.meetsObligations_optimalFaultTolerance S A⟩

/-- The stock constant-fault endpoint follows from the growing-fault one at the stock setup,
restricted to the runs whose faults do not grow. -/
theorem meetsObligationsConstant_of_growing (h : MeetsObligations) : MeetsObligationsConstant :=
  fun S A =>
    (h { S with vote := AsChainShape.stock } ⟨A.fgSlots, A.two_le_fgSlots, A.timeout⟩).toOnAs _

end Consensus.Goldilocks.Growing
end
