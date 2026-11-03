module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion

public section

/-! # Goldilocks milestone Regimes: the proved rows

`AlwaysStatements` (R.7, R.8) from `Lemmas/Compose/Regimes/` (`Outputs`, `Accountable`), and
`SleepyStatements` (R.1, R.2) from `Lemmas/Compose/Regimes/Sleepy` (`sleepy_safe`) and
`Lemmas/Healing/Regimes/Inclusion` (`include_sleepy`, `grow_sleepy`). The node-level rows
R.3–R.6 (`Statements/Regimes/{Healed,Final,Outage,Weak}`) were retired unproved: R.3–R.5
correspond to the generic rows `healedSafe`, `healthyLive` and `persists` of the Accepted endpoint;
R.6 (weak continuation) has no generic row and is dropped. -/

namespace Consensus.Goldilocks.Regimes

/-- **Milestone Regimes, the rows that hold in every run** (R.7, R.8). -/
theorem always_statements : AlwaysStatements where
  outputsNested := outputs_nested
  finalizedMonotone := finalized_monotone
  outputsValid := outputs_valid
  finalAccountable := final_accountable
  nonFraming := non_framing
  finalizedSafe := finalized_safe

/-- **Milestone Regimes, the sleepy rows** (R.1, R.2). -/
theorem sleepy_statements : SleepyStatements where
  sleepySafe := sleepy_safe
  includeSleepy := include_sleepy
  growSleepy := grow_sleepy

end Consensus.Goldilocks.Regimes

end
