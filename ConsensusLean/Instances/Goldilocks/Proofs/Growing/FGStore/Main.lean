module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Crossing

public section

/-! # FG store trace and service milestones under growing faults

The pure single-store and chain milestones remain static. These bundles certify the dynamic
trace and service statements, without importing the open growing-obligations endpoint.
-/

namespace Consensus.Goldilocks.Store.Growing

/-- FG trace safety and quorum-free entries, with faults charged at consumption. -/
theorem fg_store_trace : FGStoreTrace := fun P ACP =>
  { finalizedSafety := fun _ _ _ _ hr _ _ _ _ hy hz hf => hr.finalized_safety hy hz hf
    quorumFreeEntries := quorum_free_entries P ACP }

/-- FG good-window service, with each node honest at its own observation. -/
theorem fg_store_service : FGStoreService := fun P ACP =>
  { previousHeightJustifiedEntry := previousHeightJustified_entry P ACP
    previousHeightNotJustifiedEntry := previousHeightNotJustified_entry P ACP
    crossing := crossing P ACP
    coverage := coverage P ACP }

end Consensus.Goldilocks.Store.Growing

end
