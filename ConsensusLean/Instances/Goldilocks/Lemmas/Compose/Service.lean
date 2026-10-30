module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Service

public section

/-! # Goldilocks milestone Service: the available chain after C1.1

A1.6 (`head_extends_record`) and A1.7 (`inclusion`) over the Goldilocks run, under `Sleepy` and
`NoColl`. Interfaces: the proofs are open. -/

namespace Consensus.Goldilocks.Compose

/-- **A1.6, head extends the record under synchrony.** -/
theorem head_extends_record : HeadExtendsRecord := by
  sorry

/-- **A1.7, inclusion.** -/
theorem inclusion : Inclusion := by
  sorry

end Consensus.Goldilocks.Compose

end
