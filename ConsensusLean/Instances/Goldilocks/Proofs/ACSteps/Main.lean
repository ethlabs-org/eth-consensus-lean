module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update

public section

/-! # Goldilocks milestone ACSteps

`ACSteps` (for population-sized committees) from `Lemmas/AC/Steps/`. -/

namespace Consensus.Goldilocks.SA

/-- **ACSteps** at the SA parameters `sp`. -/
theorem acStepsAt (sp : SAParams) : ACStepsAt sp where
  proposerVotersAgree := proposer_voters_agree sp
  firstTransfer := first_transfer sp
  nextTransfer := next_transfer sp
  optimisticTransfer := optimistic_transfer sp
  optimisticNextUpdate := optimistic_next_update sp
  sourceAge := source_age sp
  resultTransfer := result_transfer sp
  sourceCompatible := source_compatible sp

/-- **ACSteps.** -/
theorem acSteps : ACSteps := acStepsAt

end Consensus.Goldilocks.SA

end
