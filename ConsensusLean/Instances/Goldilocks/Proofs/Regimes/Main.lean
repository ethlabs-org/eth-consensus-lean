module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable

public section

/-! # Goldilocks milestone Regimes: the rows that hold in every run

`AlwaysStatements` (R.7, R.8) from `Lemmas/Compose/Regimes/` (`Outputs`, `Accountable`). The sleepy
and healed rows (`Statements/Regimes/{Sleepy,Healed}`) are not proved yet. -/

namespace Consensus.Goldilocks.Regimes

/-- **Milestone Regimes, the rows that hold in every run** (R.7, R.8). -/
theorem always_statements : AlwaysStatements where
  outputsNested := outputs_nested
  finalizedMonotone := finalized_monotone
  outputsValid := outputs_valid
  finalAccountable := final_accountable
  nonFraming := non_framing
  finalizedSafe := finalized_safe

end Consensus.Goldilocks.Regimes

end
