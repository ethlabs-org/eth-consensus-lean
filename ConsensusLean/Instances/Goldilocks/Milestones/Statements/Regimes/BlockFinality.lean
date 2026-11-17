module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Params

@[expose] public section

/-! # Finality accountability over an arbitrary node AC

The R.7 conclusions use the generic node observations. Accountability and safety
take exactly the FG projection premises; non-framing needs only local execution.
-/

namespace Consensus.Goldilocks.BlockFinality

/-- Attestations on the chain of `X` in the reader's held tree before cut `i`. -/
def ChainAtts {P : Params} {A : NodeAC P} (tr : RunTrace A)
    (y : Fin P.n) (i : Nat) (X : A.Blk) : Set (FG.Att P.n) :=
  {a | ∃ Y ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc Y X ∧ a ∈ Y.fgPayload}

end Consensus.Goldilocks.BlockFinality

end
