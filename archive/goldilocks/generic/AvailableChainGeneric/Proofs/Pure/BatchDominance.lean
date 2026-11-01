module
public import AvailableChainGeneric.Statements.Pure.BatchDominance

public section

namespace AvailableChain.Gen.Pure

/-- DC: DecoupledConsensusProofs/Availability/Confirmation.lean:489;
INTENTIONAL: extract scalar Batch premises. -/
theorem anchor_passes : AnchorPassesStatement := by
  rw [AnchorPassesStatement_def]
  intro h m denominator anchorScore hb hden hscore
  have hlt := hb.lt
  have hpass : denominator < 2 * anchorScore := by omega
  exact ⟨hpass, decide_eq_true_eq.mpr hpass⟩

/-- DC: DecoupledConsensusProofs/Availability/Confirmation.lean:562;
INTENTIONAL: extract the shared-denominator count argument. -/
theorem unsupported_fails : UnsupportedFailsStatement := by
  rw [UnsupportedFailsStatement_def]
  intro h m denominator score hb hden hcount
  have hlt := hb.lt
  have hfail : 2 * score ≤ denominator := by omega
  exact ⟨hfail, decide_eq_false_iff_not.mpr (by omega)⟩

end AvailableChain.Gen.Pure
