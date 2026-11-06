module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Concrete

public section

/-! # Goldilocks meets the shape obligations

`MeetsObligations` (`Statements/Obligations`) from `Lemmas/Obligations/Concrete`
(`meetsObligations_concrete`, the endpoint at the coefficients `contract_coefficients`) and the
profile label (`schema_matches_ebbAndFlow`: the schema provides all three capabilities). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

/-- The Goldilocks schema is an Ebb-and-Flow schema: it provides the final, stable and
available capabilities (available and stable aliased to `confirmed`). -/
theorem schema_matches_ebbAndFlow : Profile.ebbAndFlow.Matches schema := by
  intro cap; cases cap <;> rfl

/-- **Goldilocks meets the obligations**: the concrete obligations endpoint. -/
theorem meets_obligations : MeetsObligations := fun S A =>
  ⟨schema_matches_ebbAndFlow, meetsObligations_concrete S A⟩

end Consensus.Goldilocks.Obligations

end
