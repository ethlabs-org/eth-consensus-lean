module
public import ConsensusBlocks.TimeGrid
public import ConsensusBlocks.Progress
public import ConsensusBlocks.Chains
public import ConsensusBlocks.Payload

/-! Building blocks between L1 (the model) and L2 (the shape): time grid, progress
requirements, chains, payload. Protocol-free; each block has at least two users
among the shapes. Quorums and evidence are deferred to the FG-SA migration.
-/
