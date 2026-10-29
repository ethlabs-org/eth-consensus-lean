module
public import ConsensusSpec.Problem.Good
public import ConsensusProofs.Problem.Derived
public import ConsensusProofs.Problem.Facts.Atoms
public import ConsensusProofs.Problem.Facts.Transfer
public import ConsensusProofs.Problem.Facts.Network
public import ConsensusProofs.Problem.Facts.Properties
public import ConsensusProofs.Problem.Facts.Regimes
public import ConsensusProofs.Problem.Facts.Good

/-! Layer 0 (L0), the consensus problem. The definitions (the trusted
surface): Basic, Network, Properties, Regimes, Good (the definition of a good
protocol). `Facts/*` holds lemmas only and need not be read to know what
`Good` means; `Derived` holds definitions that `Good` does not read (used by
the facts, the sheet and the proofs). -/
