module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps

public section

/-! # Event-local engine transitions under growing faults

The delivery, restart and non-public tick transitions use no constant-fault law. Their
static implementations accept honesty at zero; an actual honest engine event supplies it
by monotonicity, without requiring the node to stay honest after the event.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every actual event's node was honest at time zero, even if compromised later. -/
theorem event_honest_zero (hv : rho.ExecutionValid) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) : e.node ∉ rho.faultyAt 0 := by
  have hm := List.mem_of_getElem? he
  exact fun hf => hv.honest_only e hm (rho.faultyAt_mono (hv.in_horizon e hm).1 hf)

/-- A delivery executes the canonical object handlers at the delivery time. -/
theorem node_of_deliver_at (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (t : Time)
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v (i + 1)).node =
      deliverState (runProposer S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node :=
  node_of_deliver S rho hn hv v (event_honest_zero S rho hv he) i o t he

/-- A restart executes the node's restart, preserving its durable record. -/
theorem node_of_restart_at (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.restart v t)) :
    (stateAt S rho hn v (i + 1)).node =
      (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t .restart).1 :=
  node_of_restart S rho hn hv v (event_honest_zero S rho hv he) i t he

/-- Non-public ticks leave the embedded node unchanged. -/
theorem node_of_tick_other_at (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node = (stateAt S rho hn v i).node :=
  node_of_tick_other S rho hn hv v (event_honest_zero S rho hv he) i t he hp

end Consensus.Goldilocks.Simulation
