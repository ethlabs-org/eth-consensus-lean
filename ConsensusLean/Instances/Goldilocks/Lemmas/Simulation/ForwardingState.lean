module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Lemmas.Model.Candidates

public section

/-! # Abstract forwarding publisher

This model is separate from runtime state; its transitions do not prove actual publication.
-/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape Blocks
open Consensus.Model

variable {binding : VoteBinding}

/-- Abstract publisher state, separate from the installed runtime state. The map
survives restarts; pending wrappers are drained in acceptance order before the event ends.
OPEN implementation: connecting this state to `State`, actual duties and own proposals. -/
structure ForwardingState (n : Nat) where
  wrappers : Nat → Option (Wire n binding)
  pending : List (Wire n binding)

end Consensus.Goldilocks.Simulation
