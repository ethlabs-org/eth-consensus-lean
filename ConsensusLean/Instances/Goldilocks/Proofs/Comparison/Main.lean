module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.Defaults
public import ConsensusLean.Proofs.Comparison.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Comparison.TierA
public import ConsensusLean.Instances.Goldilocks.Proofs.Comparison.LatencyAC
public import ConsensusLean.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Obligations.Main

public section

/-! # Goldilocks comparison instances (Slice 0)

* `goldilocks_heal_default0`, `goldilocks_txLatency_default0`: the composite defaults, from the
  endpoint (`Growing.meets_obligations`, whose shape obligations give the L0 `Behaviour`) and the
  generic defaults `healDefault0`, `txLatencyDefault0`.
* The Tier A instances `healProfileAC0_free` and `signingRateAC0` (`TierA`), and
  `proposalLatencyAC0_sync` and `proposalLatencyAC0_bridge` (`LatencyAC`). -/

namespace Consensus.Goldilocks.Comparison

open AsChainShape Blocks Shape Consensus.Comparison

theorem goldilocks_heal_default0 : GoldilocksHealDefault0 := fun S A V _ _ cap X =>
  healDefault0 V _ _ _ _ ((Growing.meets_obligations S A).2.behaviour V) cap X

theorem goldilocks_txLatency_default0 : GoldilocksTxLatencyDefault0 := fun S A V _ _ cap X =>
  txLatencyDefault0 V _ _ _ _ ((Growing.meets_obligations S A).2.behaviour V) cap X

end Consensus.Goldilocks.Comparison

end
