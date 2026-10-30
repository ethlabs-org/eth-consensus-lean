module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service

public section

/-! # Goldilocks milestone Service

`ServiceStatements` (A1.6, A1.7) from `Lemmas/Compose/Service`. -/

namespace Consensus.Goldilocks.Compose

/-- **Service**: A1.6 and A1.7. -/
theorem service_statements : ServiceStatements where
  headExtendsRecord := head_extends_record
  inclusion := inclusion

end Consensus.Goldilocks.Compose

end
