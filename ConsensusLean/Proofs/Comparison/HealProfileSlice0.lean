module
public import ConsensusLean.Comparison.HealProfileSlice0

public section

/-! # The Slice 0 point of a Slice 1 point (proofs)

`healQ_slice0_mono`: the order of `HealQ` implies the order of the Slice 0 points, through
`IncidentClass.async_mono` (the class order implies the order of the delivery classes). -/

namespace Consensus.Comparison

/-- The order of an incident class implies the order of its delivery class. -/
theorem IncidentClass.async_mono {V : Type} {a a' : IncidentClass V} (h : a ≤ a') :
    a.async ≤ a'.async := by
  cases a <;> cases a' <;> trivial

theorem healQ_slice0_mono : HealQSlice0Mono := fun _ _ _ ⟨hL, _, _, _, hf, ha, _⟩ =>
  ⟨hL, hf, IncidentClass.async_mono ha⟩

end Consensus.Comparison

end
