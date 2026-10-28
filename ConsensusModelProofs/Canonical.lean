module
public import ConsensusModelProofs.Canonical.Network

@[expose] public section

/-! # A canonical execution for every protocol

At every integer time through the horizon, schedule honest wake restarts,
then awake honest public ticks, then deliveries of the finite pool of all
objects released so far to all awake honest nodes. Objects are deduplicated
within each recipient's delivery batch. Delivering again at later times makes
the network service independent of sleep history.

The construction uses no laws about the protocol. `unforgeable_of_causal`
uses only the engine's signing and seen filter; `delivers_of_eager` applies
to every deadline strictly after its start, including both contract deadlines.
-/

namespace Consensus.Model
open AvailableChain (Time)
open AvailableChain.Generic

/-- Every choice of protocol, environment and run data admits a valid run
with partial synchrony and healthy delivery on every prefix. -/
theorem canonical_run : CanonicalRun := by
  intro F V _ _ E honest horizon hh holder submit hash
  let base := mkRun (F := F) (E := E) honest horizon holder submit hash []
  refine ⟨base.canonicalEvents, ?_⟩
  change (base.withEvents base.canonicalEvents).ExecutionValid ∧
    (base.withEvents base.canonicalEvents).PartialSynchrony ∧
    ∀ cut, (base.withEvents base.canonicalEvents).HealthyPrefixDelivery cut
  have hs := base.canonical_schedule hh
  have hw := base.canonical_sleep
  have he := base.canonical_eager hh
  refine ⟨⟨hs, hw, ?_⟩, ?_, ?_⟩
  · exact (base.withEvents base.canonicalEvents).unforgeable_of_causal base.canonical_causal
  · exact (base.withEvents base.canonicalEvents).partialSynchrony_of_eager hw he
  · exact (base.withEvents base.canonicalEvents).healthyPrefixDelivery_of_eager hw he

end Consensus.Model
end
