module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service

public section

/-! # Goldilocks milestone FGStore: part 1, one FG store

`FGStoreLocal` from `Lemmas/FGStore/`: the reachable-state invariant (G0.1, F.2, G0.3, entry
states) and the frame (the frame step, G0.4; C0.2's `Σ` half follows). Parts 2 and 3 (FG traces
and the FG service lemmas) are bundled under growing faults (`Proofs/Growing/FGStore/Main`); their
row lemmas stay in `Lemmas/FGStore/`. -/

namespace Consensus.Goldilocks.Store

/-- **FGStore, part 1.** -/
theorem fg_store_local : FGStoreLocal := fun P ACP =>
  { chainStateOfChain := chain_state_of_chain P ACP
    acceptedTree := accepted_tree P ACP
    treeGrows := tree_grows P ACP
    cacheInvariants := cache_invariants P ACP
    acceptIsFrameStep := accept_is_frame_step P ACP
    frameRealization := frame_realization P ACP
    entryStateOfSource := entry_state_of_source P ACP }

end Consensus.Goldilocks.Store

end
