module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later


public section

/-! # Goldilocks milestone ACSteps

`ACSteps` (for population-sized committees) from `Lemmas/AC/Steps/`. -/

namespace Consensus.Goldilocks.AC

/-- **ACSteps** at the AC parameters `sp`. -/
theorem acStepsAt (sp : ACParams) : ACStepsAt sp where
  proposerVotersAgree := proposer_voters_agree sp
  firstTransfer := first_transfer sp
  nextTransfer := next_transfer sp
  optimisticTransfer := optimistic_transfer sp
  optimisticNextUpdate := optimistic_next_update sp
  sourceAge := source_age sp
  resultTransfer := result_transfer sp

/-- **ACSteps.** -/
theorem acSteps : ACSteps := acStepsAt

end Consensus.Goldilocks.AC

end
