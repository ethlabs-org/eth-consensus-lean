module
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure

/-- This bridge gives the canonical residue of the FG-SA action clock.
Consumers: F5.HG.7 and F5.HG.8a. Sources: 21:1695,1709–1717,2203,2210–2217.
DC: additive (no DC counterpart); reason: periodic deadline normalization is scalar.
Lane definitions: Params.actionTime and Claims/Statements/Bounds.P. -/
theorem fgsa_action_time_residue (p : Params) (r : Nat) :
    p.actionTime r % P p = 6 * p.Δ := by
  have hR : (2 : Int) ≤ p.R := by exact_mod_cast p.RLarge
  have hres₀ : 0 ≤ 6 * p.Δ := by linarith [p.deltaPos]
  have hresP : 6 * p.Δ < P p := by
    change 6 * p.Δ < 4 * (p.R : Int) * p.Δ
    nlinarith [p.deltaPos]
  rw [← fgsa_grid_action_time, (grid_round_equations p.Δ p.R r).2.2,
    (grid_round_equations p.Δ p.R r).1, fgsa_grid_period]
  rw [Int.add_emod, Int.mul_emod]
  simp only [Int.emod_self, mul_zero, Int.zero_emod, zero_add]
  rw [Int.emod_eq_of_lt hres₀ hresP, Int.emod_eq_of_lt hres₀ hresP]

end AvailableChain.FGSA.Run
