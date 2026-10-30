module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart

public section

/-! # Goldilocks SA: the reachable-state invariant (A0.1–A0.6, A0.9)

The statements about reachable AC states, by induction over `ReachableAt`: the pools (slot,
two-vote cap, admission slots), the stamps (stable between restarts, ordered along parent
edges), resolution, the merged view's opponents, the stored locks on one chain and below the
record, the FG candidates, and the interface requirements 1–5. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A0.1, pool capacity.** -/
theorem pool_cap : PoolCap sp := by
  sorry

/-- **A0.1, admission slots.** -/
theorem admission_slots : AdmissionSlots sp := by
  sorry

/-- **A0.1, stamps.** -/
theorem stamp_stable : StampStable sp := by
  sorry

/-- **A0.1, carried votes.** -/
theorem carried_votes : CarriedVotes sp := by
  sorry

/-- **A0.1, stamps along parent edges.** -/
theorem stamp_parent : StampParent sp := by
  sorry

/-- **A0.2, resolution is stable.** -/
theorem resolution_stable : ResolutionStable sp := by
  sorry

/-- **A0.3, the merged view's opponents.** -/
theorem merged_opponents : MergedOpponents sp := by
  sorry

/-- **A0.4 (a), (b).** -/
theorem live_locks_chain : LiveLocksChain sp := by
  sorry

/-- **A0.4 (f).** -/
theorem candidates_chain : CandidatesChain sp := by
  sorry

/-- **A0.5.** -/
theorem lock_to_tip : LockToTip sp := by
  sorry

/-- **A0.6.** -/
theorem interface_requirements : InterfaceRequirements sp := by
  sorry

/-- **A0.9.** -/
theorem proposal_payload_valid : ProposalPayloadValid sp := by
  sorry

end Consensus.Goldilocks.SA

end
