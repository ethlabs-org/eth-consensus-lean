module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.State

public section

/-! # Goldilocks SA: the order of finite event times

`ETime.of` embeds times into event times monotonically in both directions. -/

namespace Consensus.Goldilocks.SA

theorem etime_of_lt_of {a b : Time} : ETime.of a < ETime.of b ↔ a < b := by
  simp [ETime.of]

theorem etime_of_le_of {a b : Time} : ETime.of a ≤ ETime.of b ↔ a ≤ b := by
  simp [ETime.of]

end Consensus.Goldilocks.SA

end
