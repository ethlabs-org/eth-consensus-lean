module
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition

public section

/-! # Goldilocks FG: chain-state invariants (G0.2, G0.7 (c), G0.9)

The invariants of every chain state that a chain reaches (G0.2 (a), (d), (e) and
`Q_target ⊆ Q_prog`), by induction over the chain with one block at a time; then the facts
about one accepted block: the height step and entry constancy (G0.2 (b), (h), (i)), gated
consumption (G0.7 (c)) and retention (G0.9 (a), (b)). -/

namespace Consensus.Goldilocks.FG

variable (gp : FGParams)

/-- **G0.2 (a), (c) part, (d), (e).** -/
theorem chain_invariants : ChainInvariants gp := by
  sorry

/-- **G0.2 (b), (h), (i).** -/
theorem height_step : HeightStep gp := by
  sorry

/-- **G0.7 (c).** -/
theorem gated_consumption : GatedConsumption gp := by
  sorry

/-- **G0.9 (a).** -/
theorem retention : Retention gp := by
  sorry

/-- **G0.9 (b).** -/
theorem retention_through_append : RetentionThroughAppend gp := by
  sorry

end Consensus.Goldilocks.FG

end
