module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EventGroups

public section

/-! # Engine states agree with the canonical growing trace

Validity makes every actual event an honest event, so each event realizes its node handler.
The canonical state correspondence is consequently unconditional in the observed node;
the consumer-facing interface retains its time-local honesty premise.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every bounded engine state matches the canonical event expansion. -/
theorem simTraceAt_state_all (hv : rho.ExecutionValid) (v : V) :
    ∀ i ≤ rho.events.length, (stateAt S rho hn v i).node =
      (simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  rw [simTraceAt_eq]
  exact simTrace_state_of S rho hn hv (fun he hnode => hnode ▸ event_honest_zero S rho hv he)
    (fun he hp => node_of_tick_public_at S rho hn hv v _ _ he hp)

/-- Time-local state interface: the trace state at the mapped cut is the engine node
state observed while that node is honest. -/
theorem simTraceAt_state (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (_hh : v ∉ rho.faultyAt (rho.cutTime i)) (hi : i ≤ rho.events.length) :
    (simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i) =
      (stateAt S rho hn v i).node :=
  (simTraceAt_state_all S rho hn hv v i hi).symm

end Consensus.Goldilocks.Simulation
