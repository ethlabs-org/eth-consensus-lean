module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks SA: the lock store at reachable states (A0.4 (a), (b), (d), (f), A0.5, A0.6)

Unlocking is idempotent; at reachable states the live locks lie on one chain and are viable or
at or below `fc_root`, the FG candidates lie on one chain below the anchor, every live lock is
below the effective record, and the SA meets the interface requirements 1–4. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A0.4 (d).** -/
theorem unlock_idempotent : UnlockIdempotent sp := by
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

end Consensus.Goldilocks.SA

end
