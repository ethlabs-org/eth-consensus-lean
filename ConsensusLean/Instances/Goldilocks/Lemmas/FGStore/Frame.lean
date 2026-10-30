module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant

public section

/-! # Goldilocks FG store: the frame (C0.2, the frame step, G0.4)

From the reachable-state statements: accepting a block moves `Σ.F` only to a descendant
(the finalized tip of the new block's chain, between the old tip and the block); the frame of
the new state is the frame step by the block; and the frame of a reachable state is well
formed (its tree, the accepted blocks above `Σ.F`, is finite, coherent and rooted, and the
fork-choice root `Σ.J` or `Σ.F` lies in it). -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- **C0.2, the `Σ` half.** -/
theorem finalized_monotone : FinalizedMonotone P ACP := by
  sorry

/-- **The FG kernel of the frame step.** -/
theorem accept_is_frame_step : AcceptIsFrameStep P ACP := by
  sorry

/-- **G0.4 (height).** -/
theorem frame_realization : FrameRealization P ACP := by
  sorry

end Consensus.Goldilocks.Store

end
