module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Outcome

public section

/-! # Goldilocks milestone Service

`ServiceStatements` (A1.6, A1.7, C1.2) from `Lemmas/Compose/Service`. -/

namespace Consensus.Goldilocks.Compose

/-- **Service**: A1.6, A1.7 and C1.2. -/
theorem service_statements : ServiceStatements where
  headExtendsRecord := head_extends_record
  inclusion := inclusion
  outcomeService := outcome_service

end Consensus.Goldilocks.Compose

end
