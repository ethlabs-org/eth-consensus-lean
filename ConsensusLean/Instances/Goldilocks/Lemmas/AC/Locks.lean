module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Base

public section

/-! # Goldilocks SA: lock functions (A0.4 (c)–(e))

Facts about `live_locks`, `add_locks` and `unlock` in any well-formed frame: locks only move
back and keep their slot and fast bit, unlocking is idempotent, and with fewer than `n/2`
equivocators `Φ.F` has fewer than half of the committee as opponents. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A0.4 (c).** -/
theorem locks_move_back : LocksMoveBack sp := by
  sorry

/-- **A0.4 (d).** -/
theorem unlock_idempotent : UnlockIdempotent sp := by
  sorry

/-- **A0.4 (e).** -/
theorem unlock_no_fallback : UnlockNoFallback sp := by
  sorry

end Consensus.Goldilocks.SA

end
