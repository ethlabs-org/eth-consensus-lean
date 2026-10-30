module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service

public section

/-! # Goldilocks milestone Service

`ServiceStatements` (A1.6, A1.7, C1.2) from `Lemmas/Compose/Service` and, for C1.2, which reads
HR.4, `Lemmas/Healing/Outcome`. -/

namespace Consensus.Goldilocks.Compose

/-- **Service**: A1.6, A1.7 and C1.2. -/
theorem service_statements : ServiceStatements where
  headExtendsRecord := head_extends_record
  inclusion := inclusion
  outcomeService := Healing.outcome_service

end Consensus.Goldilocks.Compose

end
