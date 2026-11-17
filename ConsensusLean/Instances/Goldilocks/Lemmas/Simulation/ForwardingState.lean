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

end Consensus.Goldilocks.Simulation
