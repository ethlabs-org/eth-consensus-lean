module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.Identity
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.ServiceEquivalence
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Votes
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Records
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutagePostStop

/-! # Goldilocks supplies for packages requiring node-level provenance -/

public section

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload goldilocksFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {R : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

variable {FGP : Type} {ro : ReplayOrder sp FGP} {U : Set (SA.Blk sp.n FGP)}
  {o : SA.SATrace sp FGP ro}

end Consensus.Goldilocks.Compose

end
