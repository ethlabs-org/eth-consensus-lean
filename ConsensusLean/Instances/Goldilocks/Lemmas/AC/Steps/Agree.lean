module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission

public section

/-! # Goldilocks SA: proposer and voters agree on unlocking (A1.1)

The proposal's view and an honest voter's merged view give the same opponents to every block of
slot at most `s`, under `Sync[t_s, t_{s+1}]`, when both frames hold the same blocks of slot at
most `s`. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A1.1.** -/
theorem proposer_voters_agree : ProposerVotersAgree sp := by
  sorry

end Consensus.Goldilocks.SA

end
