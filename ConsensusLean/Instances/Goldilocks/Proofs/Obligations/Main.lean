module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Concrete

public section

/-! # Goldilocks meets the shape obligations

`MeetsObligations` (`Statements/Obligations`) from `Lemmas/Obligations/Concrete`
(`meetsObligations_concrete`, the endpoint at the coefficients `contract_coefficients`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

/-- **Goldilocks meets the obligations**: the concrete obligations endpoint. -/
theorem meets_obligations : MeetsObligations := fun S A => meetsObligations_concrete S A

end Consensus.Goldilocks.Obligations

end
