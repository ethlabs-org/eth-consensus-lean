module
public import ConsensusBlocks.TimeGrid
public import ConsensusBlocks.Selection
public import ConsensusBlocks.Chains
public import ConsensusBlocks.Payload

/-! Building blocks between layer ½ and layer 1: time grid, selection
premises, chains, payload. Protocol-free; each block has at least two users
among the shapes. Quorums and evidence are deferred to the FG-SA migration
(D-13). -/
