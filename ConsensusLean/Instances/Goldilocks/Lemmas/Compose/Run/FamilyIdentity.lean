module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Family
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.Identity
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection

/-! # The actual-node Goldilocks identity family run -/

public section

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload goldilocksFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {R : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

end Consensus.Goldilocks.Compose

end
