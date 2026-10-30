module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks SA: pools, stamps and resolution at reachable states (A0.1–A0.3, A0.7, A0.9)

The ACBase statements that ACSteps does not use: admission slots, stable stamps and carried votes
(A0.1), stable resolution (A0.2), the merged view's opponents (A0.3), what a joined node kept at
its restarts (A0.7) and the proposal payload (A0.9). Kept out of the import closure of ACSteps,
so that ACSteps' closure is free of `sorry` while these are open. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A0.1, admission slots.** -/
theorem admission_slots : AdmissionSlots sp := by
  sorry

/-- **A0.1, stamps.** -/
theorem stamp_stable : StampStable sp := by
  sorry

/-- **A0.1, carried votes.** -/
theorem carried_votes : CarriedVotes sp := by
  sorry

/-- **A0.2, resolution is stable.** -/
theorem resolution_stable : ResolutionStable sp := by
  sorry

/-- **A0.3, the merged view's opponents.** -/
theorem merged_opponents : MergedOpponents sp := by
  sorry

/-- **A0.9.** -/
theorem proposal_payload_valid : ProposalPayloadValid sp := by
  sorry

/-- **A0.7, joining.** -/
theorem joined_keeps_votes : JoinedKeepsVotes sp := by
  sorry

end Consensus.Goldilocks.SA

end
