module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # Goldilocks SA: the restart (A0.7)

What `ac_restart` keeps, resets and writes, and that the node is not joined at the restart, so
the replay emits nothing. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A0.7, restart.** -/
theorem restart_state : RestartState sp := by
  sorry

end Consensus.Goldilocks.SA

end
