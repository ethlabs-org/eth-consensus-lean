module
public import ConsensusLean.Spec.Problem.Basic
import ConsensusLean.Lemmas.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-! # Goldilocks Obligations: the final heal margin covers a gap window

The coefficient arithmetic of the final route: the heal margin of the final capability pays the
horizon step `B + (12c − 2)Δ` of a gap-`c` window of the reset bound `B`, for every `c` with
`3c ≤ δ_t` (`final_heal_horizon_fit`). Base of `FinalResetPremises`. -/

namespace Consensus.Goldilocks.Obligations

/-- **The final heal margin covers a window of span `3c`** (symbolic in `c`). With the reset bound
`B = ready + (20 L_drain + 24δ_t + 24X + 40)·Δ` and `M_f = 20 L_drain + 8k + 28δ_t + 28X + 56`
(`contract_heal_ge_final`), the horizon step of a gap-`c` window, `B + (12c − 2)·Δ`, stays below
`ready + M_f·Δ − 1` for every `c` with `3c ≤ δ_t`: the slack `M_f − (B − ready)/Δ − 12c + 2 =
8k + 4δ_t + 4X + 18 − 12c ≥ 8k + 4X + 18` is positive. So `contract_heal` needs no change for a
gap `c` with `3c ≤ δ_t`. -/
theorem final_heal_horizon_fit {D Ld k δt X c : Time} (hD : 0 < D) (hk : 0 ≤ k) (hX : 0 ≤ X)
    (h3c : 3 * c ≤ δt) :
    (20 * Ld + 24 * δt + 24 * X + 40 + (12 * c - 2)) * D + 1 ≤
      (20 * Ld + 8 * k + 28 * δt + 28 * X + 56) * D := by
  have h1 : 0 ≤ (4 * δt - 12 * c) * D := mul_nonneg (by linarith only [h3c]) hD.le
  have h2 : 0 ≤ k * D := mul_nonneg hk hD.le
  have h3 : 0 ≤ X * D := mul_nonneg hX hD.le
  have key : (20 * Ld + 8 * k + 28 * δt + 28 * X + 56) * D -
      ((20 * Ld + 24 * δt + 24 * X + 40 + (12 * c - 2)) * D + 1) =
      8 * (k * D) + (4 * δt - 12 * c) * D + 4 * (X * D) + 18 * D - 1 := by ring
  have hD1 : (1 : Time) ≤ D := hD
  linarith only [key, h1, h2, h3, hD1]

end Consensus.Goldilocks.Obligations

end
