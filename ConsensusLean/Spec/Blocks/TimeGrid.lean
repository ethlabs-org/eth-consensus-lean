module
public import ConsensusLean.Spec.Problem.Basic

@[expose] public section

/-! # Time grid (building block)

Slots have an instance-supplied positive length in time units; slot `s` starts
at `s · slotLen`. The grid does not refer to the network delay. Time is integer,
so slots exist only from time 0 on (slot 0 starts at 0). -/

namespace Consensus.Blocks

/-- A slot index. -/
abbrev Slot := Nat

/-- A positive slot length in time units, supplied by the instance. -/
structure TimeGrid where
  /-- The slot length in time units. -/
  slotLen : Time
  /-- Slots have positive length. -/
  slotLen_pos : 0 < slotLen

namespace TimeGrid

variable (G : TimeGrid)

/-- The start time of slot `s`: `s · slotLen`. -/
def slotTime (s : Slot) : Time := (s : Time) * G.slotLen

/-- The slot whose time plus `off` is `t`, if any. -/
def slotAt? (off t : Time) : Option Slot :=
  if 0 ≤ t - off ∧ (t - off) % G.slotLen = 0 then some ((t - off) / G.slotLen).toNat
  else none

end TimeGrid

end Consensus.Blocks
end
