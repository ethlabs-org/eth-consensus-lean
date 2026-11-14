module
public import ConsensusLean.Spec.Blocks.Progress
public import Mathlib.Tactic.Ring

public section

/-! # Goldilocks Obligations: the sufficient heal bound of the key-dependent rise route

The five-window sufficient heal bound with the key-dependent window of `Healing.M1.RiseWindow`
(`resetBoundRounds`, `ResetOfDrainRounds`). The window of key value `v` has the length
`len = 4D(L_drain + r·ρ + 2) + 2D`, `r = r(v) ≤ 2`, `ρ = δ_t + X − 1`, and the five attempts end
by `lo + 5(4D(L_drain + 2) + 2D + λ) + 6·4Dρ` (`sum_riseLen` at
`d = 4D(L + 2)`, round length `4Dρ`, slack `2D`). The round count `rr` cancels in the reset
bound, so the arithmetic needs no range for it: `a ≤ ready + (20 L_drain + 24ρ + 54)·D + 5λ − 1`,
against `40ρ` on the five-window route.

Pure integer arithmetic, time unit `D`, `ts s = 4D·s`. `heal` is any time with
`ready + T_heal ≤ heal`. -/

namespace Consensus.Goldilocks.Obligations

/-- The heal coefficient of the key-dependent rise route, in units of `D` (without the
`5λ − 2` term). At `λ = 2D`: `T_heal = (20L + 8k + 28δt + 28X + 56)·D − 2`. -/
def healBoundCoeffRounds (k δt X Ld : ℤ) : ℤ := 20 * Ld + 8 * k + 28 * δt + 28 * X + 46

/-- Unfolding equation of `healBoundCoeffRounds`. -/
theorem healBoundCoeffRounds_eq (k δt X Ld : ℤ) :
    healBoundCoeffRounds k δt X Ld = 20 * Ld + 8 * k + 28 * δt + 28 * X + 46 := by
  unfold healBoundCoeffRounds
  rfl

/-- At `λ = 2D` the key-dependent bound is `T_heal = (20L + 8k + 28δt + 28X + 56)·D − 2`. -/
theorem healBoundCoeffRounds_at_two (k δt X Ld D : ℤ) :
    healBoundCoeffRounds k δt X Ld * D + 5 * (2 * D) - 2 =
      (20 * Ld + 8 * k + 28 * δt + 28 * X + 56) * D - 2 := by
  rw [healBoundCoeffRounds_eq]
  ring

end Consensus.Goldilocks.Obligations
