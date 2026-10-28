module
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.Field.Rat
@[expose] public section

/-! # Constants
Every time constant is a natural-number coefficient of `Δ`, so the claims can
hold for every `Δ`. The constants are a literal in an instance's top-level
theorem: they are its reported result, and a reviewer reads them, including
the premise-side ones (`catchUp`, `η`, `armingLag`, `fastArmingLag`, `budget`,
`θ`, `θrec`, `recoveryFull`), which narrow the guarantee. -/
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
  /-- A reader or proposer must have been awake for this long (no restart). -/
  catchUp : Nat
  /-- η, the history window of the η-sleepy premise. -/
  η : Nat
  /-- Inclusion delays: confirmed, stable, fast stable. -/
  D_c : Nat
  D_s : Nat
  D_f : Nat
  /-- The lag before an outage can start, and its fast variant. -/
  armingLag : Nat
  fastArmingLag : Nat
  /-- Π, the maximum outage length. -/
  budget : Nat
  /-- θ, the η-sleepy weight threshold; θrec, the participation threshold
  after GST. -/
  θ : ℚ
  θrec : ℚ
  /-- Whether recovery also needs every honest validator awake. -/
  recoveryFull : Bool
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
  theta_lower : (1 / 2 : ℚ) ≤ C.θ
  theta_upper : C.θ ≤ 3 / 4
  thetaRec_lower : (1 / 2 : ℚ) ≤ C.θrec
  thetaRec_upper : C.θrec ≤ 3 / 4
  fastArmingLag_le : C.fastArmingLag ≤ C.armingLag
  budget_pos : 0 < C.budget
  budget_le_eta : C.budget ≤ C.η

end Consensus.Shape
end
