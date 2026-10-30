module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks SA: source compatibility after the cut (A1.9)

The block that `ac_to_fg` returns at an honest node after the cut is compatible with the block
of an earlier fast lock (it reads the fast-lock provenance of `Steps/Provenance`). -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A1.9.** -/
theorem source_compatible : SourceCompatible sp := by
  sorry

end Consensus.Goldilocks.SA

end
