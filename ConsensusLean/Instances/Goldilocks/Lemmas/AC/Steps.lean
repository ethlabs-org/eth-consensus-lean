module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks SA: the step lemmas (A1.1–A1.5, A1.8, A1.9)

The per-vote transfer lemmas over SA traces. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A1.1.** -/
theorem proposer_voters_agree : ProposerVotersAgree sp := by
  sorry

/-- **A1.2.** -/
theorem first_transfer : FirstTransfer sp := by
  sorry

/-- **A1.3.** -/
theorem next_transfer : NextTransfer sp := by
  sorry

/-- **A1.4 (a).** -/
theorem optimistic_transfer : OptimisticTransfer sp := by
  sorry

/-- **A1.4 (b).** -/
theorem optimistic_next_update : OptimisticNextUpdate sp := by
  sorry

/-- **A1.5.** -/
theorem source_age : SourceAge sp := by
  sorry

/-- **A1.8.** -/
theorem result_transfer : ResultTransfer sp := by
  sorry

/-- **A1.9.** -/
theorem source_compatible : SourceCompatible sp := by
  sorry

end Consensus.Goldilocks.SA

end
