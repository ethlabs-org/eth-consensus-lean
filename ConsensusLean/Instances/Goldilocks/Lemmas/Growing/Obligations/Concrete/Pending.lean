module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Final
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Repair

public section

/-! # Pending engine interface of the growing obligations endpoint

The statement the endpoint consumes whose home module is not on this branch yet, under its agreed
name, so that the endpoint composes against the final interface: healed safety of a healthy
preparation query (`healthy_ready_safety_at`), home `Lemmas/Growing/Obligations/Healthy`.

It re-exports outage protection of an outage query (`outage_protected_at`) from
`Outage/Engine/Repair`, the final branch of healthy liveness
(`meetsObligations_healthyLive_final_growing`) from `Concrete/Final` and finite engine sleepy
safety (`sleepy_safe_engine_at`) from `Sleepy/Engine/Safety`.

The theorem here is an open `sorry`; this module is deleted when its home module lands. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Obligations
open Blocks Shape
open Consensus.Model (pubOf)

variable (S : Setup)

section Queries

variable (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **Healed safety under growing faults**: with progress on `[ready, heal]` and the heal point
within the horizon, the confirmed reads of nodes ready from the heal point are safe. -/
theorem healthy_ready_safety_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    (chainTrace Q.run.2).ReadySafe ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      .confirmed Q.heal := by
  sorry

end Queries

end Consensus.Goldilocks.Obligations.Growing

end
