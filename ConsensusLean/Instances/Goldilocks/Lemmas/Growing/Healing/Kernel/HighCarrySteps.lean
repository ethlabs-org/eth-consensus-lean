module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighCarry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighCarryProofs

public section

/-! # Frozen no-Catch carry steps for retained high-origin votes

These steps are independent of retained-vote induction. The later step consumes
strictly earlier votes explicitly; neither step may import Kernel.ResetFacts.
Both are proved in Kernel/HighCarryProofs, re-exported here.
-/

end
