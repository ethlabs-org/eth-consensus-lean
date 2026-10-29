module
public import ConsensusSpec.Problem.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Time grid (building block)

Slots of `slotDeltas · Δ` time units; slot `s` starts at `s · slotLen`. Duties of
a shape sit at `slotTime s + j · Δ` (phase `j`). Time is integer, so slots exist
only from time 0 on (slot 0 starts at 0). -/

namespace Consensus.Blocks

/-- A slot index. -/
abbrev Slot := Nat

/-- Slots of `slotDeltas · Δ`; duties sit at `slotTime s + j · Δ` (phase `j`). -/
structure TimeGrid where
  /-- The slot length in multiples of `Δ`; positive by type. -/
  slotDeltas : ℕ+

namespace TimeGrid

variable (G : TimeGrid)

/-- The slot length in time units: `slotDeltas · Δ`. -/
def slotLen (Δ : Time) : Time := ((G.slotDeltas : Nat) : Time) * Δ

/-- The start time of slot `s`: `s · slotLen`. -/
def slotTime (Δ : Time) (s : Slot) : Time := (s : Time) * G.slotLen Δ

/-- The slot whose time plus `off` is `t`, if any. -/
def slotAt? (Δ off t : Time) : Option Slot :=
  if 0 ≤ t - off ∧ (t - off) % G.slotLen Δ = 0 then some ((t - off) / G.slotLen Δ).toNat
  else none

end TimeGrid

end Consensus.Blocks
end
