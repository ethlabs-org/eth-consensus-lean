module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Params

@[expose] public section

/-! # Goldilocks milestone Regimes: the vocabulary of the rows that hold in every run

The R.7 and R.8 rows (`specs/goldilocks/tex/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)") are stated under growing faults in `Statements/Regimes/Growing` and proved by
`Regimes.Growing.always_statements`; their static forms over a fixed honest set are retired (owner
decision). This module keeps the vocabulary those rows read:

* `ChainAtts`: the attestations included on the chain of a block of a node's tree;
* `ValidOutput`: a block of a node's tree whose chain is linked to genesis with increasing slots
  and its slots' proposers, every block accepted by the node at an earlier cut.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open AC (ACParams Payload)

section Defs

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Set (Fin sp.n))

/-- The attestations included on the chain of `X` in the tree of `y` before cut `i`: the FG
payloads of the blocks of `y`'s tree at or below `X`. -/
def ChainAtts (y : Fin sp.n) (i : Nat) (X : AC.Blk sp.n (List (FG.Att sp.n))) :
    Set (FG.Att sp.n) :=
  {a | ∃ Y ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc Y X ∧ a ∈ Y.fgPayload}

/-- The block `X` of `y`'s tree before cut `i` is a valid output: its chain in that tree is linked
to genesis (`X` is in the tree, which is rooted), and every block of it other than genesis has its
digest as its root (`RootOk`), was accepted by `y` at an earlier cut (seen by the reader), has its
slot's proposer, and has a parent of a smaller slot in the tree. -/
def ValidOutput (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (y : Fin sp.n) (i : Nat)
    (X : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  X ∈ (tr.state y i).fg.tree ∧
    ∀ Z, (tr.state y i).fg.Anc Z X → Z.root ≠ sp.genesisRoot →
      Z.RootOk dg ∧ (∃ k < i, tr.AcceptAt y k Z) ∧
      Z.proposer = proposer Z.slot ∧
      ∃ Pz ∈ (tr.state y i).fg.tree, Z.parent = some Pz.root ∧ Pz.slot < Z.slot

end Defs

end Consensus.Goldilocks.Regimes

end
