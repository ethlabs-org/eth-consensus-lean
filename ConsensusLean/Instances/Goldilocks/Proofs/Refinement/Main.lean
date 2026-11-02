module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Accepted
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Accepted

public section

/-! # Goldilocks milestone Accepted

`AcceptedEndpoint` (`Statements/Refinement/Accepted`) from `Lemmas/Refinement/Accepted`
(`accepted_concrete`, the endpoint at the coefficients `accepted_coefficients`). -/

namespace Consensus.Goldilocks.Refinement

/-- **Goldilocks Accepted**: the concrete acceptance endpoint. -/
theorem accepted_endpoint : AcceptedEndpoint := fun S A => accepted_concrete S A

end Consensus.Goldilocks.Refinement

end
