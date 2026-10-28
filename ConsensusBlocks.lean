module
public import ConsensusBlocks.TimeGrid
public import ConsensusBlocks.Progress
public import ConsensusBlocks.Chains
public import ConsensusBlocks.Payload
public import ConsensusBlocks.Facts

/-! Building blocks between L1 (the model) and L2 (the shape): time grid, progress
requirements, chains, payload. Protocol-free. Quorums and evidence are deferred
to the FG-SA migration. The definition files hold definitions only; their
lemmas are in `Facts`. -/
