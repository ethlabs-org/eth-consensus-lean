module
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition

public section

/-! # Goldilocks FG: finality before the gate (G0.8)

At a bound height whose predecessor is the highest pending pair, a finality quorum for it
makes `bestFinal` pick it, so the finality step of the same block finalizes it, and a target
quorum then justifies. -/

namespace Consensus.Goldilocks.FG

/-- **G0.8.** -/
theorem finality_before_gate (gp : FGParams) : FinalityBeforeGate gp := by
  sorry

end Consensus.Goldilocks.FG

end
