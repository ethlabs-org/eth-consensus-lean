module
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs

public section

/-! # Goldilocks Refinement: the named coefficients of the nonfinal reset envelope (#136, S5/S6)

Parameter-only coefficients, functions of the setup `S` and the index `X` alone, shared by the reset
envelope (`HealthyResetEnvelope`, S5) and the heal coefficient (S6). They are fixed before any run,
GST or reset is chosen.

* `healthyDrainLen S X = 2k + X`: the drain length `L_drain`. It pays the producer guard
  `2k + G ≤ L_drain + 1` at the gap `G = X`.
* `healthyResetCoeff S X = 24·L_drain + 48(δ_t + X) + 28`: `R`, with the envelope
  `a ≤ ready + R·Δ + r`. It is `resetBound`'s coefficient `24 L_drain + 48(δ_t + X − 1) + 64` plus
  the lag `6λ = 12Δ` at `λ = 2Δ`.
* `healthyResetSlack S X = 0`: `r`.
* `healMargin S X = R + 16k + 8δ_t + 8X + 64`: the margin `M` of the heal coefficient
  `accepted_heal = catchUp + 2M + 3` (`AcceptanceDefs`). It covers the nonfinal reset reserve
  `R + 8k + 4X + 26 + r` (`accepted_heal_ge_reset`) and the final route's heal-bound margin
  `24 L_drain + 8k + 52δ_t + 52X + 44` at `λ = 2Δ` (`heal_bound.md` §0.1;
  `healMargin_ge_final`), with slack. -/

namespace Consensus.Goldilocks.Refinement

/-- The drain length `L_drain = 2k + X` of the nonfinal reset envelope. -/
def healthyDrainLen (S : Setup) (X : ℕ+) : Nat := 2 * S.k + X

theorem healthyDrainLen_val (S : Setup) (X : ℕ+) : healthyDrainLen S X = 2 * S.k + X := by rfl

/-- The reset coefficient `R = 24·L_drain + 48(δ_t + X) + 28` of the nonfinal reset envelope. -/
def healthyResetCoeff (S : Setup) (X : ℕ+) : Nat := 24 * healthyDrainLen S X + 48 * (S.δt + X) + 28

theorem healthyResetCoeff_val (S : Setup) (X : ℕ+) :
    healthyResetCoeff S X = 24 * healthyDrainLen S X + 48 * (S.δt + X) + 28 := by rfl

/-- The literal slack `r = 0` of the nonfinal reset envelope. -/
def healthyResetSlack (_S : Setup) (_X : ℕ+) : Nat := 0

theorem healthyResetSlack_val (S : Setup) (X : ℕ+) : healthyResetSlack S X = 0 := by rfl

/-- The margin `M = R + 16k + 8δ_t + 8X + 64` of the heal coefficient. -/
def healMargin (S : Setup) (X : ℕ+) : Nat :=
  healthyResetCoeff S X + 16 * S.k + 8 * S.δt + 8 * X + 64

theorem healMargin_val (S : Setup) (X : ℕ+) :
    healMargin S X = healthyResetCoeff S X + 16 * S.k + 8 * S.δt + 8 * X + 64 := by rfl

/-- `M` covers the final route's heal-bound margin `M_f = 24 L_drain + 8k + 52δ_t + 52X + 44` at
`λ = 2Δ` (`heal_bound.md` §0.1, coefficient form `accepted_heal(final, X) ≥ C + 2 M_f`), at
`L_drain = healthyDrainLen`: `M = 24 L_drain + 16k + 56δ_t + 56X + 92`, slack
`8k + 4δ_t + 4X + 48`. -/
theorem healMargin_ge_final (S : Setup) (X : ℕ+) :
    24 * healthyDrainLen S X + 8 * S.k + 52 * S.δt + 52 * (X : Nat) + 44 ≤ healMargin S X := by
  rw [healMargin_val, healthyResetCoeff_val]
  omega

end Consensus.Goldilocks.Refinement

end
