module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore

public section

/-! # Goldilocks milestone ACBase

`ACBase sp` and `LocalRunReachable` from `Lemmas/AC/`. -/

namespace Consensus.Goldilocks.SA

/-- **ACBase.** -/
theorem acBase (sp : SAParams) : ACBase sp where
  slotArithmetic := slot_arithmetic sp
  lockExpiry := lock_expiry sp
  joinedFrom := joined_from sp
  joinedAwake := joined_awake sp
  poolCap := pool_cap sp
  admissionSlots := admission_slots sp
  stampStable := stamp_stable sp
  carriedVotes := carried_votes sp
  stampParent := stamp_parent sp
  resolutionStable := resolution_stable sp
  supportInTree := support_in_tree sp
  supportersAntitone := supporters_antitone sp
  opponentsMonotone := opponents_monotone sp
  majorityChain := majority_chain sp
  optimisticChain := optimistic_chain sp
  mergedOpponents := merged_opponents sp
  liveLocksChain := live_locks_chain sp
  locksMoveBack := locks_move_back sp
  unlockIdempotent := unlock_idempotent sp
  unlockNoFallback := unlock_no_fallback sp
  candidatesChain := candidates_chain sp
  lockToTip := lock_to_tip sp
  interfaceRequirements := interface_requirements sp
  restartState := restart_state sp
  joinedKeepsVotes := joined_keeps_votes sp
  oneVotePerSlot := one_vote_per_slot sp
  proposalPayloadValid := proposal_payload_valid sp

end Consensus.Goldilocks.SA

end
