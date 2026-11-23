module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Persist

@[expose] public section

/-! # Goldilocks Service vocabulary: the record at a cut

The milestone statements A1.6 (head extends the record) and A1.7 (inclusion) of
`specs/goldilocks/tex/goldilocks-claims.tex` §"Available chain, after C1.1" are retired; the
vocabulary the proofs of the obligations endpoint read stays: `RecordAt`, the block of a node's
record `𝒜.latest_confirmed` before a cut when it is in the frame's tree. C1.2 (AC
outcome service) is in `Statements/Healing/Outcome` (`OutcomeService`), C1.3 (finalizing coverage
recurs) in `Statements/Healing/Recovery` (`FinalizingCoverage`).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- The block of `y`'s record `𝒜.latest_confirmed` before cut `i`, if it is in the frame's
tree. -/
def RecordAt (y : Fin sp.n) (i : Nat) (R : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  R ∈ (Node.frame (tr.state y i)).tree ∧ R.root = (tr.state y i).ac.latestConfirmed

end Consensus.Goldilocks.Compose

end
