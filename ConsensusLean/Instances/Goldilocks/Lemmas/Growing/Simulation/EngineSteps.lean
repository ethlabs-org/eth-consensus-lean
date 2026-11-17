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

end Consensus.Goldilocks.Simulation
