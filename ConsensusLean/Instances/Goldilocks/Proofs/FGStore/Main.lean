module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Goldilocks milestone FGStore: part 1, one FG store, and part 2, FG traces

`FGStoreLocal` from `Lemmas/FGStore/`: the reachable-state invariant (G0.1, F.2, G0.3, entry
states) and the frame (C0.2, the frame step, G0.4); part 2 so far, over FG traces (G1.4, the core
of G1.10); and part 3, the FG service lemmas (G1.6–G1.8, G1.9 (a)). -/

namespace Consensus.Goldilocks.Store

/-- **FGStore, part 1.** -/
theorem fg_store_local : FGStoreLocal := fun P ACP =>
  { chainStateOfChain := chain_state_of_chain P ACP
    acceptedTree := accepted_tree P ACP
    treeGrows := tree_grows P ACP
    cacheInvariants := cache_invariants P ACP
    finalizedMonotone := finalized_monotone P ACP
    acceptIsFrameStep := accept_is_frame_step P ACP
    frameRealization := frame_realization P ACP
    entryStateOfSource := entry_state_of_source P ACP }

/-- **FGStore, part 2 (so far).** -/
theorem fg_store_trace : FGStoreTrace := fun P ACP =>
  { finalizedSafety := finalized_safety P ACP
    quorumFreeEntries := quorum_free_entries P ACP }

/-- **FGStore, part 3.** -/
theorem fg_store_service : FGStoreService := fun P ACP =>
  { boundEntry := bound_entry P ACP
    unboundEntry := unbound_entry P ACP
    crossing := crossing P ACP
    coverage := coverage P ACP
    cacheAcceptance := cache_acceptance P ACP }

end Consensus.Goldilocks.Store

end
