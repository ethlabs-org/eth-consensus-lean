module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Interface
public import ConsensusLean.Lemmas.Model.Candidates

public section

/-! # Abstract forwarding publisher

This model is separate from runtime state; its transitions do not prove actual publication.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model

/-- Abstract publisher state, separate from the installed runtime state. The map
survives restarts; pending wrappers are drained in acceptance order before the event ends.
OPEN implementation: connecting this state to `State`, actual duties and own proposals. -/
structure ForwardingState (n : Nat) where
  wrappers : Nat → Option (Wire n)
  pending : List (Wire n)

end Consensus.Goldilocks.Refinement
