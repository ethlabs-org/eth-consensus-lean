module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Optimistic
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Update

public section

/-! # Goldilocks AC milestone under growing faults

Each count is charged at its consuming cut; provenance retains the honesty of its writer
at the write. Proposer agreement requires honesty through the consuming vote.
-/

namespace Consensus.Goldilocks.SA.Growing

/-- Proposer agreement at the repaired, two-cut honesty premise. -/
theorem proposer_voters_agree (sp : SAParams) : ProposerVotersAgree sp := by
  intro FGP ro H U tr proposer hr s p y i j ℓp ℓy pay e hp hy hpp hprop hti hc hs hP
    hsync heq B hB hBs
  exact proposer_voters_agree_of_honest_max hr hp hy hpp hprop hti hc hs hP hsync heq B hB hBs

/-- The AC step statements for population-sized committees, with growing faults. -/
theorem acStepsAt (sp : SAParams) : ACStepsAt sp where
  proposerVotersAgree := proposer_voters_agree sp
  firstTransfer := first_transfer sp
  nextTransfer := next_transfer sp
  optimisticTransfer := optimistic_transfer sp
  optimisticNextUpdate := optimistic_next_update sp
  sourceAge := source_age sp
  resultTransfer := by
    intro FGP ro H U tr proposer hr s X y i₀ i C CV ℓ e hX hres hy hc hs hcarry hv hl hd
    exact result_transfer hr hX hres hy hc hs hcarry hv hl hd
  sourceCompatible := source_compatible sp

/-- The growing-fault ACSteps milestone. -/
theorem acSteps : ACSteps := acStepsAt

end Consensus.Goldilocks.SA.Growing

end
