module
public import ConsensusProblem.Good
public import ConsensusProblem.Derived
public import ConsensusProblem.Facts.Atoms
public import ConsensusProblem.Facts.Transfer
public import ConsensusProblem.Facts.Network
public import ConsensusProblem.Facts.Properties
public import ConsensusProblem.Facts.Regimes
public import ConsensusProblem.Facts.Good

/-! Layer 0 (L0), the consensus problem. The definitions (the trusted
surface): Basic, Network, Properties, Regimes, Good (the definition of a good
protocol). `Facts/*` holds lemmas only and need not be read to know what
`Good` means; `Derived` holds definitions that `Good` does not read (used by
the facts, the sheet and the proofs). -/
