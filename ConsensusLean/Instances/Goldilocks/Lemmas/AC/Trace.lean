module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Invariant

public section

/-! # Goldilocks AC traces: reachability and one node's life (F.1 (c), A0.7, A0.8)

The AC trace contract gives reachable states; and, over an SA trace, a joined node has been
awake with no restart since the previous slot, erased no recent vote at its restarts, and casts
one vote per slot. -/

namespace Consensus.Goldilocks

/-- The AC trace contract gives reachable states. -/
theorem localRun_reachable : LocalRunReachable := by
  sorry

end Consensus.Goldilocks

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **F.1 (c), a joined node.** -/
theorem joined_awake : JoinedAwake sp := by
  sorry

/-- **A0.7, joining.** -/
theorem joined_keeps_votes : JoinedKeepsVotes sp := by
  sorry

/-- **A0.8.** -/
theorem one_vote_per_slot : OneVotePerSlot sp := by
  sorry

end Consensus.Goldilocks.SA

end
