module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageReader
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ReceiverService
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport

public section

/-! # Goldilocks Refinement: the outage's receiver service (O4, cut 3)

Workbench `notes/outage/outage_reader_bridge.md` §10.4 (rev 4.4), cut 3. `outage_receiver_service`
is S5's `hS` in query form: every honest receiver gets the receiver-scoped strict AC service from
the outage's end `Q.stop`. It is `receiverServiceAfter_of_psync` at `outage_psync`. -/

namespace Consensus.Goldilocks.Refinement

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- S5's `hS` in query form: receiver-scoped strict AC service from the outage's GST, for every
honest receiver. -/
theorem outage_receiver_service (Q : OutageQuery S A V) :
    ∀ y ∈ honestKeys S Q.run.2,
      Compose.ReceiverServiceAfter (honestKeys S Q.run.2)
        (Q.trace.HonestBlocks (honestKeys S Q.run.2)) Q.stop y Q.trace.projAC :=
  fun _ hy => receiverServiceAfter_of_psync S Q.run.2 Q.hn Q.valid
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision) (outage_psync S A V Q) hy

end Consensus.Goldilocks.Refinement
