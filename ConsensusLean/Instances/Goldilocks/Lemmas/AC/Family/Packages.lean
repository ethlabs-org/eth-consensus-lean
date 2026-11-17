module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Family.Identity
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Votes
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Records
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Retention
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Dominance
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Source
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Unlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockFloorStep
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

/-! # Independent Goldilocks component fact suppliers -/

public section

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {o : SATrace sp FGP ro}
  {proposer : Nat → Fin sp.n}

end Consensus.Goldilocks.SA

end
