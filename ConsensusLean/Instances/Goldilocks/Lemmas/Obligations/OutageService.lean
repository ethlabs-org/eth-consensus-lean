module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageReader
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ReceiverService
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport

public section

/-! # Goldilocks Obligations: the outage's receiver service

`outage_receiver_service`
is the hypothesis `hS` of `Compose.restored_majority` in query form: every honest receiver gets the
receiver-scoped strict AC service from the outage's end `Q.stop`. It is
`receiverServiceAfter_of_psync` at `outage_psync`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The hypothesis `hS` of `Compose.restored_majority` in query form: receiver-scoped strict AC
service from the outage's GST, for every honest receiver. -/
theorem outage_receiver_service (Q : OutageQuery S A V) :
    ∀ y ∈ honestKeys S Q.run.2,
      Compose.ReceiverServiceAfter (honestKeys S Q.run.2)
        (Q.trace.HonestBlocks (honestKeys S Q.run.2)) Q.stop y Q.trace.projAC :=
  fun _ hy => receiverServiceAfter_of_psync S Q.run.2 Q.hn Q.valid
    (noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision) (outage_psync S A V Q) hy

end Consensus.Goldilocks.Obligations
