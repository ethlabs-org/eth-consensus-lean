module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client

public section

/-! # Goldilocks FG store: finalized safety (G1.4)

Two honest finalized tips that conflict are the finalizations of two accepted chains that
finalize conflicting blocks (G0.3, G0.1), so accountable safety (G1.3) gives `2q − n` validators
with a slashable pair on the two chains; one of them is honest. Its two attestations were
processed by the honest nodes that accepted the blocks carrying them, so (unforgeability) it
signed both, and they are outputs of one client run (`signed_run`): client safety (G0.5)
excludes the pair. -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- **G1.4.** -/
theorem finalized_safety : FinalizedSafety P ACP := by
  sorry

end Consensus.Goldilocks.Store

end
