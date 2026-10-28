module
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
@[expose] public section

/-! Service bounds only. Environment parameters are published in L0's
`Assumptions`; constants report slot length, inclusion, delay and growth. -/
namespace Consensus.Shape

/-- An affine bound `a + b·k` in units of `Δ`, for a recurrence gap of `k`
slots. -/
structure Affine where
  a : Nat
  b : Nat

def Affine.eval (f : Affine) (k : Nat) : Nat := f.a + f.b * k

structure Constants where
  /-- The slot length in units of `Δ`; `Claims` pins the family's `slotTicks`
  to it. -/
  slotTicks : Nat
  /-- Inclusion delays: confirmed, stable, fast stable. -/
  D_c : Nat
  D_s : Nat
  D_f : Nat
  /-- Growth delays (confirmed, stable), the recovery bound, and the finality
  startup and delay, as functions of the recurrence gap. -/
  growth : Affine
  stableGrowth : Affine
  /-- Growth after recovery; an L1 obligation, not yet exported to L0. -/
  recGrowth : Affine
  recovery : Affine
  finStart : Affine
  finDelay : Affine

/-- The bounds fixed by the contract. -/
structure Constants.Valid (C : Constants) : Prop where
  slotTicks_pos : 0 < C.slotTicks

end Consensus.Shape
end
