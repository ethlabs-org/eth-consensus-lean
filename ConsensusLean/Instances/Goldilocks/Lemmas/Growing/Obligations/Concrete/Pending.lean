module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Endpoint.Accountable

public section

/-! # Pending engine interface of the growing obligations endpoint

Statements the endpoint consumes whose home modules are not on this branch yet, under their agreed
names, so that the endpoint composes against the final interface:

* finite engine sleepy safety under growing faults (`sleepy_safe_engine_at`), home
  `Lemmas/Growing/Sleepy/Engine/Safety`;
* healed safety of a healthy preparation query (`healthy_ready_safety_at`), home
  `Lemmas/Growing/Obligations/Healthy`;
* outage protection of an outage query (`outage_protected_at`), home
  `Lemmas/Growing/Outage/Engine/Repair`;
* the final branch of healthy liveness (`meetsObligations_healthyLive_final_growing`), home
  `Lemmas/Growing/Obligations/Concrete/Final`.

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Obligations
open Blocks Shape
open Consensus.Model (pubOf)

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Finite safety of the engine's confirmed output under growing faults**, under the finite
service and the L0 sleepy budget with look-ahead `5Δ` through the horizon. -/
theorem sleepy_safe_engine_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 rho.horizon) :
    (chainTrace rho).ReadySafe (Regimes.catchUp (S.params (pubOf E) hn) + 1) .confirmed 0 := by
  sorry

end Engine

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

/-- **Outage protection under growing faults**: every node ready from the recovery point holds
every confirmed block that a node ready at the arming time `T` held. -/
theorem outage_protected_at (Q : OutageQueryAt S A V) :
    (chainTrace Q.run.2).ProtectedReadyFrom Q.duration .confirmed
      (resilienceTarget schema .confirmed) Q.T
      ((Sys (goldilocks S) V).recoveryAt (K S A) Q.stop Q.run) := by
  sorry

/-- **Final healthy liveness under growing faults**: the `healthyLive` field of the shape claims
at the final capability. -/
theorem meetsObligations_healthyLive_final_growing : ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (goldilocks S) V).Holds
      (fun r => (Sys (goldilocks S) V).Healthy (K S A) gst r ∧
        (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) .final i
          ((Sys (goldilocks S) V).ready (K S A) gst r) ((Sys (goldilocks S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (goldilocks S) V).cDur (K S A) r)
        g ((Sys (goldilocks S) V).heal (K S A) .final i gst r)
        ((K S A).params.latency .final i) := by
  sorry

end Queries

end Consensus.Goldilocks.Obligations.Growing

end
