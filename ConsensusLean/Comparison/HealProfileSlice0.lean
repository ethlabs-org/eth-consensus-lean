module
public import ConsensusLean.Comparison.HealProfile

@[expose] public section

/-! # The Slice 0 point of a Slice 1 point (statements)

`HealQ.slice0 q = ⟨L, fcap, a.async⟩`: the coordinates of a Slice 1 point that Slice 0 reads (the
incident length, the fault cap and the delivery class). Statements that add Slice 1's coordinates
to a Slice 0 premise read the Slice 0 part at `q.slice0`. The order of `HealQ` implies the order
of the Slice 0 points (`HealQSlice0Mono`; proved in `Proofs/Comparison`). -/

namespace Consensus.Comparison

variable {V : Type}

/-- The Slice 0 point of a Slice 1 point: `⟨L, fcap, a.async⟩`. -/
def HealQ.slice0 (q : HealQ V) : Slice0Q V := ⟨q.L, q.fcap, q.a.async⟩

/-- **The order passes to the Slice 0 points**: `q ≤ q'` implies `q.slice0 ≤ q'.slice0`. -/
def HealQSlice0Mono : Prop := ∀ (V : Type) (q q' : HealQ V), q ≤ q' → q.slice0 ≤ q'.slice0

end Consensus.Comparison

end
