module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Inclusion

public section

/-! # Goldilocks milestone Service

`ServiceStatements` (A1.6, A1.7) from `Lemmas/Compose/Service`. C1.2 (`OutcomeService`) is stated in
`Statements/Healing/Outcome` and proved in `Lemmas/Healing/Outcome` (`Healing.outcome_service`). -/

namespace Consensus.Goldilocks.Compose

/-- **Service**: A1.6 and A1.7. -/
theorem service_statements : ServiceStatements where
  headExtendsRecord := head_extends_record
  inclusion := inclusion_sleepy

end Consensus.Goldilocks.Compose

end
