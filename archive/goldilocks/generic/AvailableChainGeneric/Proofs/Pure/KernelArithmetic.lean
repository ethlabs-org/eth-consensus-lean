module
public import AvailableChainGeneric.Statements.Pure.KernelArithmetic
public import AvailableChainGeneric.Proofs.Pure.SlotGrid
import Mathlib.Tactic.Linarith -- shake: keep (re-export)
import Mathlib.Tactic.Ring -- shake: keep (re-export)
import Mathlib.Tactic.Push -- shake: keep (re-export)
import Mathlib.Tactic.NormNum -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- kernel_arith proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem kernel_arith : KernelArithmeticStatement := by
  rw [KernelArithmeticStatement_def]
  intro Δ R q r hΔ hR
  have hRcast : (2 : Time) ≤ R := by exact_mod_cast hR
  have hperiod : 8 * Δ ≤ P Δ R := by rw [P_def]; nlinarith
  have hnext : a Δ R (q + 1) = T Δ R q + P Δ R + 6 * Δ := by
    rw [a_def, d_def, T_def, t_def, t_def, slotLen_def, P_def]
    push_cast
    ring
  have hvote : v Δ (q * R + 1) = T Δ R q + 5 * Δ := by
    rw [v_def, T_def, t_def, t_def, slotLen_def]
    push_cast
    ring
  have hcarrier : t Δ (q * R + 2) = T Δ R q + 8 * Δ := by
    rw [T_def, t_def, t_def, slotLen_def]
    push_cast
    ring
  have hgate : d Δ (q * R + 1) = T Δ R q + 10 * Δ := by
    rw [d_def, T_def, t_def, t_def, slotLen_def]
    push_cast
    ring
  have hactionq := (grid_round_equations Δ R q).2.2
  have hactionr := (grid_round_equations Δ R r).2.2
  rw [hnext, hvote, hcarrier, hgate, hactionq, hactionr]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- action_carrier_arithmetic proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem action_carrier_arithmetic : ActionCarrierArithmeticStatement := by
  rw [ActionCarrierArithmeticStatement_def]
  intro Δ R r hΔ hR
  have hRcast : (2 : Time) ≤ R := by exact_mod_cast hR
  have hperiod : 8 * Δ ≤ P Δ R := by rw [P_def]; nlinarith
  have hnext : T Δ R (r + 1) = T Δ R r + P Δ R := by
    rw [T_def, T_def, t_def, t_def, slotLen_def, P_def]
    push_cast
    ring
  have hcarrier : t Δ (r * R + 2) = T Δ R r + 8 * Δ := by
    rw [T_def, t_def, t_def, slotLen_def]
    push_cast
    ring
  rw [(grid_round_equations Δ R r).2.2, hcarrier, hnext]
  exact ⟨by ring, rfl, by linarith⟩

end AvailableChain.Gen.Pure
