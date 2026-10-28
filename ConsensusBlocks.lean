module
public import ConsensusBlocks.TimeGrid
public import ConsensusBlocks.Selection
public import ConsensusBlocks.Chains
public import ConsensusBlocks.Payload

/-! Building blocks between L1 (the model) and L2 (the shape): time grid, selection
premises, chains, payload. Protocol-free; each block has at least two users
among the shapes. Quorums and evidence are deferred to the FG-SA migration
(D-13). -/
