module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.State

@[expose] public section

/-! # Goldilocks milestone vocabulary: chain states of chains

The part of `Spec/FG/State` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. Names and bodies are unchanged.

A chain's chain state (`FGParams.chainState`) is the fold of `stateTransition` from
`ChainState.init`; a failed assertion makes the fold `none` (the block is refused). `roots` and
`chainAtts` are its blocks' roots and attestations. -/

namespace Consensus.Goldilocks.FG

namespace FGParams

variable (gp : FGParams)

/-- The chain state after a chain (oldest first), or `none` if a block is refused. -/
def chainState (c : List (FGBlock gp.n)) : Option (ChainState gp.n) :=
  c.foldl (fun o B => o.bind (fun σ => gp.stateTransition σ B)) (some (ChainState.init gp))

/-- The roots of a chain, genesis included. -/
def roots (c : List (FGBlock gp.n)) : List Nat := gp.genesis :: c.map FGBlock.root

/-- The attestations that a chain carries. -/
def chainAtts (c : List (FGBlock gp.n)) : List (Att gp.n) := c.flatMap FGBlock.atts

end FGParams

end Consensus.Goldilocks.FG

end
