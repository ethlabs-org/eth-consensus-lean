module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Main
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Obligations.Constant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Endpoint
public import ConsensusLean.Lemmas.Shape.OnRuns

public section

/-! # The growing-fault obligations endpoint

`MeetsObligations` (`Statements/Obligations`) from the nine claims assembled in
`Lemmas/Growing/Obligations/Concrete/Endpoint` (`meetsObligations_growing`) and the profile label
(`schema_matches_ebbAndFlow`); the headline `GoldilocksCorrect` by `ShapeObligations.correct`;
`PersistsWith` by the binding-generic `meetsObligations_persists_growing`. The
constant-fault endpoint follows (`meetsObligationsConstant_of_growing`). This module is the
Goldilocks entry of the comparator solution. The compiled proposer hold-zero counterexample
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
  Consensus.Shape.ShapeObligations.correct (meets_obligations S A).2 V

/-- **Goldilocks survives outages at every vote binding**: the binding-generic outage claim
`meetsObligations_persists_growing` at every bound setup. -/
theorem persists_with : PersistsWith := fun S A V =>
  Obligations.Growing.meetsObligations_persists_growing S A V

/-- The constant-fault endpoint follows from the growing-fault one. -/
theorem meetsObligationsConstant_of_growing (h : MeetsObligations) : MeetsObligationsConstant :=
  fun S A => (h S A).toOnAs _

end Consensus.Goldilocks.Growing
end
