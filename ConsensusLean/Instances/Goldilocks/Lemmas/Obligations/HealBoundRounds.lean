module
public import ConsensusLean.Spec.Blocks.Progress

public section

/-! # Goldilocks Obligations: the sufficient heal bound of the key-dependent rise route (#136)

recovery_time_savings item 1, piece (4). The five-window sufficient heal bound with the
key-dependent window of `exists_reset_of_drain_rounds` (`ResetOfDrainRounds`). The window of key
value `v` has the length `len = 4D(L_drain + r·ρ + 2) + 2D`, `r = r(v) ≤ 2`, `ρ = δ_t + X − 1`,
and the five attempts end by `lo + 5(4D(L_drain + 2) + 2D + λ) + 6·4Dρ` (`sum_riseLen` at
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

/-- **Sufficient heal bound, key-dependent rounds (arithmetic).** With `rr` rounds, the
window length `len = 4D(L_drain + rr·ρ + 2) + 2D` and the five-attempt bound
`a_f + len ≤ lo + 5(4D(L_drain + 2) + 2D + λ) + 6·4Dρ`: if
`ready + healBoundCoeffRounds·D + 5λ − 2 ≤ heal ≤ q`, then the slot-aligned frame
`[ts s₀, ts N + 2D]`, `N = s₀ + L_drain + rr·ρ + 1`, fits the window; the reset has
`a ≤ ready + (20 L_drain + 24ρ + 54)·D + 5λ − 1`; the rise deadline `ts N + 2D ≤ heal` holds;
and the placement (H3) holds for every `u_min ≤ slot a + 2k + 5`. -/
theorem heal_bound_sufficient_rounds {D ready heal q lo af len lam a : ℤ}
    {k δt X Ld s₀ u sa uMin rr : ℤ}
    (hD : 0 < D) (hready : 0 ≤ ready) (hlam : 0 ≤ lam)
    (hk : 0 ≤ k) (hδ : 1 ≤ δt) (hX : 1 ≤ X) (hLd : 0 ≤ Ld)
    (hlo : lo ≤ ready + 4 * D)
    (hlen : len = 4 * D * (Ld + rr * (δt + X - 1) + 2) + 2 * D)
    (hwin : af + len ≤ lo + (5 * (4 * D * (Ld + 2) + 2 * D + lam) + 6 * (4 * D * (δt + X - 1))))
    (hs₀ : 4 * D * s₀ < af + 4 * D)
    (hu : u ≤ s₀ + Ld)
    (hrise : a ≤ 4 * D * (u + rr * (δt + X - 1) + 1) + 2 * D)
    (hsa : 4 * D * sa ≤ a) (huMin : uMin ≤ sa + 2 * k + 5)
    (hheal : ready + healBoundCoeffRounds k δt X Ld * D + 5 * lam - 2 ≤ heal) (hq : heal ≤ q) :
    4 * D * (s₀ + Ld + rr * (δt + X - 1) + 1) + 2 * D < af + len ∧
      a ≤ ready + (20 * Ld + 24 * (δt + X - 1) + 54) * D + 5 * lam - 1 ∧
      4 * D * (s₀ + Ld + rr * (δt + X - 1) + 1) + 2 * D ≤ heal ∧
      max (max ready 0) (4 * D * uMin - 1) + (X + δt) * (4 * D) ≤ q + 4 * D := by
  rw [healBoundCoeffRounds_eq] at hheal
  have hu' : 4 * D * u ≤ 4 * D * (s₀ + Ld) := mul_le_mul_of_nonneg_left hu (by linarith)
  have hm' : 4 * D * uMin ≤ 4 * D * (sa + 2 * k + 5) :=
    mul_le_mul_of_nonneg_left huMin (by linarith)
  have hfit : 4 * D * (s₀ + Ld + rr * (δt + X - 1) + 1) + 2 * D < af + len := by
    rw [hlen]; linarith
  have hfrm : 4 * D * (s₀ + Ld + rr * (δt + X - 1) + 1) + 2 * D ≤
      ready + (20 * Ld + 24 * (δt + X - 1) + 54) * D + 5 * lam - 1 := by
    linarith
  have hDk : 0 ≤ D * k := mul_nonneg hD.le hk
  have hDδ : D ≤ D * δt := by nlinarith
  have hDX : D ≤ D * X := by nlinarith
  have hDL : 0 ≤ D * Ld := mul_nonneg hD.le hLd
  refine ⟨hfit, ?_, ?_, ?_⟩
  · have : a ≤ 4 * D * (s₀ + Ld + rr * (δt + X - 1) + 1) + 2 * D := by linarith
    linarith
  · linarith
  · have hr : max ready 0 = ready := max_eq_left hready
    rw [hr]
    apply add_le_of_le_sub_right
    apply max_le
    · linarith
    · have : a ≤ 4 * D * (s₀ + Ld + rr * (δt + X - 1) + 1) + 2 * D := by linarith
      linarith

/-- At `λ = 2D` the key-dependent bound is `T_heal = (20L + 8k + 28δt + 28X + 56)·D − 2`. -/
theorem healBoundCoeffRounds_at_two (k δt X Ld D : ℤ) :
    healBoundCoeffRounds k δt X Ld * D + 5 * (2 * D) - 2 =
      (20 * Ld + 8 * k + 28 * δt + 28 * X + 56) * D - 2 := by
  rw [healBoundCoeffRounds_eq]
  ring

end Consensus.Goldilocks.Obligations
