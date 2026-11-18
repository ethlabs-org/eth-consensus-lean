module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion

public section

/-! # Goldilocks milestone Regimes: the proved rows

Each row is a `Challenge` statement with its own theorem: R.7 and R.8 (the six rows of
`Statements/Regimes/Always`) in `Lemmas/Compose/Regimes/` (`Outputs`, `Accountable`). R.2 is
proved under growing faults at a committee in `Proofs/Growing/SleepyGrowth`. R.1 (`SleepySafe`)
and the inclusion packaging are retired as milestone statements. The node-level rows
R.3–R.6 (`Statements/Regimes/{Healed,Final,Outage,Weak}`) were retired unproved: R.3–R.5
correspond to the generic rows `healedSafe`, `healthyLive` and `persists` of the obligations
endpoint; R.6 (weak continuation) has no generic row and is dropped. -/

end
