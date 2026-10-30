module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps

public section

/-! # Goldilocks milestone ACSteps

`ACSteps sp` from `Lemmas/AC/Steps`. -/

namespace Consensus.Goldilocks.SA

/-- **ACSteps.** -/
theorem acSteps (sp : SAParams) : ACSteps sp where
  proposerVotersAgree := proposer_voters_agree sp
  firstTransfer := first_transfer sp
  nextTransfer := next_transfer sp
  optimisticTransfer := optimistic_transfer sp
  optimisticNextUpdate := optimistic_next_update sp
  sourceAge := source_age sp
  resultTransfer := result_transfer sp
  sourceCompatible := source_compatible sp

end Consensus.Goldilocks.SA

end
