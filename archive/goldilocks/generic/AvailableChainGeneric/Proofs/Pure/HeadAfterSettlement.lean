module
public import AvailableChainGeneric.Statements.Pure.HeadAfterSettlement
public import AvailableChainGeneric.Proofs.Pure.SlotGrid -- shake: keep (re-export)
public import Mathlib.Data.Int.DivMod -- shake: keep (re-export)
import Mathlib.Tactic.Linarith -- shake: keep (re-export)
import Mathlib.Tactic.Ring -- shake: keep (re-export)
import Mathlib.Tactic.Push -- shake: keep (re-export)
import Mathlib.Tactic.NormNum -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- The settlement threshold and predecessor give the Euclidean quotient.
Consumers: F5.HG.7 and F5.HG.8a. Sources: S1b:815–817; 21:1721–1727,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA repair input. -/
theorem firstHead_after : FirstHeadAfterStatement := by
  rw [FirstHeadAfterStatement_def]
  intro Δ w b hΔ hw hfirst
  have hh : 0 < 4 * Δ := by linarith
  have hlo : w + 2 * Δ ≤ 4 * Δ * (b : Int) := by
    have h := hfirst.1
    rw [v_def, t_def, slotLen_def] at h
    linarith
  have hsmall : 4 * Δ * (b : Int) < w + 2 * Δ + 4 * Δ := by
    cases b with
    | zero => simp only [Nat.cast_zero, mul_zero]; linarith
    | succ k =>
      have h := hfirst.2 k (by omega)
      rw [v_def, t_def, slotLen_def] at h
      push_cast
      nlinarith
  have hdiv : (w + 2 * Δ + 4 * Δ - 1) / (4 * Δ) = (b : Int) := by
    apply (Int.ediv_eq_iff_of_pos hh).mpr
    constructor
    · nlinarith [Int.add_one_le_iff.mpr hsmall]
    · nlinarith
  rw [t_def, slotLen_def, hdiv]

/-- A larger settlement cut gives a larger ceiling bound.
Consumers: F5.HG.7 and F5.HG.8a. Sources: S1b:815–817; 21:1721–1727,1840,2208–2217.
DC: additive (no DC counterpart); reason: the settlement HEAD cut is an FG-SA repair input. -/
theorem firstHead_after_bound : FirstHeadAfterBoundStatement := by
  rw [FirstHeadAfterBoundStatement_def]
  intro Δ w U b hΔ hw hwU hfirst
  rw [firstHead_after Δ w b hΔ hw hfirst]
  have hh : 0 < 4 * Δ := by linarith
  have hnum : w + 2 * Δ + 4 * Δ - 1 ≤ U + 2 * Δ + 4 * Δ - 1 := by linarith
  exact mul_le_mul_of_nonneg_left (Int.ediv_le_ediv hh hnum) (le_of_lt hh)

end AvailableChain.Gen.Pure
