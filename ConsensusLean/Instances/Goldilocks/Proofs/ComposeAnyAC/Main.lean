module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Node

public section

/-! # Goldilocks milestone Compose/AnyAC

`ComposeInterfaceStatements` and `ComposeNodeStatements` from `Lemmas/Compose/`. -/

namespace Consensus.Goldilocks.Compose

/-- **Compose/AnyAC, the interface.** -/
theorem compose_interface_statements : ComposeInterfaceStatements := fun _ _ A =>
  { tipsNested := tips_nested A
    proposalParentHeld := proposal_parent_held A
    sourceHeld := source_held A
    dutyHeadsHeld := duty_heads_held A }

/-- **Compose/AnyAC, the node.** -/
theorem compose_node_statements : ComposeNodeStatements := fun _ _ dg self =>
  { threeTips := three_tips dg self
    finalizedMonotone := finalized_monotone dg self
    restartKeepsFG := restart_keeps_fg self
    honestBlockAccepted := honest_block_accepted dg self
    tickOrder := tick_order dg self
    signedOnlyInTicks := signed_only_in_ticks dg self
    execIsCutChain := exec_is_cut_chain dg self
    acStatesReachable := ac_states_reachable dg self
    fgStatesReachable := fg_states_reachable dg self
    recordIsClientRun := record_is_client_run dg self
    sourcesHeld := sources_held dg self
    acSeesAcceptedBlocks := ac_sees_accepted_blocks dg self }

end Consensus.Goldilocks.Compose

end
