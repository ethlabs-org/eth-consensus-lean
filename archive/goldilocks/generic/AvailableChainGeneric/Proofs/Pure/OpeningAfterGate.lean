module
public import AvailableChainGeneric.Statements.Pure.OpeningAfterGate
public import AvailableChainGeneric.Proofs.Pure.SlotGrid
import Mathlib.Tactic.Linarith -- shake: keep (re-export)
import Mathlib.Tactic.Ring -- shake: keep (re-export)
import Mathlib.Tactic.Push -- shake: keep (re-export)
import Mathlib.Tactic.NormNum -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- The inclusive first-opening witness gives the gate-grid delay bound.
Consumers: F5.HG.1 and F5.HG.3. Sources: 21:1343–1346,1413–1415,1488–1506.
DC: additive (no DC counterpart); reason:
the gate-grid bound is sharper than least-action selection. -/
theorem firstOpening_after_gate : FirstOpeningAfterGateStatement := by
  rw [FirstOpeningAfterGateStatement_def]
  intro Δ R q r hΔ hR hfirst
  have hqr : q ≤ r * R :=
    (grid_offset_order Δ (6 * Δ) q (r * R) hΔ).1.mp
      (by simpa only [a_def, d_def] using hfirst.1)
  have hgap : (r * R : Nat) - (q : Int) ≤ (R : Int) - 1 := by
    cases r with
    | zero =>
      have hq : q = 0 := by simpa using hqr
      subst q
      have hRi : (1 : Int) ≤ R := by exact_mod_cast hR
      simp only [Nat.zero_mul, Nat.cast_zero]
      omega
    | succ k =>
      have hp : k * R < q :=
        (grid_offset_order Δ (6 * Δ) (k * R) q hΔ).2.mp
          (by simpa only [a_def, d_def] using hfirst.2 k (by omega))
      have hpi : (k * R : Nat) + (1 : Int) ≤ (q : Int) := by exact_mod_cast hp
      push_cast at hpi ⊢
      nlinarith
  have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 4 * Δ)
  constructor
  · exact sub_nonneg.mpr hfirst.1
  · rw [a_def, d_def, d_def, t_def, t_def, P_def, slotLen_def]
    nlinarith

end AvailableChain.Gen.Pure
