module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion

public section

/-! # Goldilocks milestone Regimes: the proved rows

Each row is a `Challenge` statement with its own theorem: R.7 and R.8 (the six rows of
`Statements/Regimes/Always`) in `Lemmas/Compose/Regimes/` (`Outputs`, `Accountable`); the
sleepy rows (R.1, R.2) are `sleepy_safe` (`Lemmas/Compose/Regimes/Sleepy`), `include_sleepy` and
`grow_sleepy` (`Lemmas/Healing/Regimes/Inclusion`). The node-level rows
R.3–R.6 (`Statements/Regimes/{Healed,Final,Outage,Weak}`) were retired unproved: R.3–R.5
correspond to the generic rows `healedSafe`, `healthyLive` and `persists` of the Accepted endpoint;
R.6 (weak continuation) has no generic row and is dropped. -/

end
