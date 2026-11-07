module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Concrete
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Obligations.Constant
public import ConsensusLean.Main

public section

/-! # Goldilocks meets the shape obligations on constant faults

`MeetsObligationsConstant` (`Milestones/Statements/Obligations/Constant`) from
`Lemmas/Obligations/Concrete` (`meetsObligations_concrete`, the endpoint at the coefficients
`contract_coefficients`) and the profile label (`schema_matches_ebbAndFlow`: the schema provides
all three capabilities), and the headline on constant faults `GoldilocksCorrectConstant` by
`ShapeObligationsOn.correct`. Untrusted corollaries of the constant-fault milestones; the
certified pair is the growing-fault one (`Proofs/Growing/Obligations`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

/-- The Goldilocks schema is an Ebb-and-Flow schema: it provides the final, stable and
available capabilities (available and stable aliased to `confirmed`). -/
theorem schema_matches_ebbAndFlow : Profile.ebbAndFlow.Matches schema := by
  intro cap; cases cap <;> rfl

/-- **Goldilocks meets the obligations on constant faults**: the concrete endpoint. -/
theorem meets_obligations_constant : MeetsObligationsConstant := fun S A =>
  ⟨schema_matches_ebbAndFlow, meetsObligations_concrete S A⟩

/-- **Goldilocks is correct on constant faults**: adequacy and realizability remain unrestricted. -/
theorem goldilocks_correct_constant : GoldilocksCorrectConstant := fun S A V =>
  Consensus.Shape.ShapeObligationsOn.correct _ (meets_obligations_constant S A).2 V

end Consensus.Goldilocks.Obligations

end
