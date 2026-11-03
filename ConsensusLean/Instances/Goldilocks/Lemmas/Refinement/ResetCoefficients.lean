module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Accepted

public section

/-! # Goldilocks Refinement: the named coefficients of the nonfinal reset envelope (#136, S5/S6)

Characterising lemmas of parameter-only coefficients, functions of the setup `S` and the index `X`
alone, shared by the reset envelope (`HealthyResetEnvelope`, S5) and the heal coefficient (S6). They
are defined in the statement module `Statements/Refinement/Accepted` and fixed before any run, GST
or reset is chosen.

* `healthyDrainLen S X = 2k + X`: the drain length `L_drain`. It pays the producer guard
  `2k + G ≤ L_drain + 1` at the gap `G = X`.
* `healthyResetCoeff S X = 24·L_drain + 48(δ_t + X) + 28`: `R`, with the envelope
  `a ≤ ready + R·Δ + r`. It is `resetBound`'s coefficient `24 L_drain + 48(δ_t + X − 1) + 64` plus
  the lag `6λ = 12Δ` at `λ = 2Δ`.
* `healthyResetSlack S X = 0`: `r`.
* `healMargin S X = 24 L_drain + 8k + 52δ_t + 52X + 44`: the margin `M_f` of the heal coefficient
  `accepted_heal = catchUp + M_f`, the final route's heal-bound margin at `λ = 2Δ`
  (`heal_bound.md` §0.1). It covers the nonfinal reset reserve `R + 8k + 4X + 29 + r` when
  `δ_t ≥ 6` (`healMargin_ge_reset`, slack `4δ_t − 13`). -/

namespace Consensus.Goldilocks.Refinement

theorem healthyDrainLen_val (S : Setup) (X : ℕ+) : healthyDrainLen S X = 2 * S.k + X := by rfl

theorem healthyResetCoeff_val (S : Setup) (X : ℕ+) :
    healthyResetCoeff S X = 24 * healthyDrainLen S X + 48 * (S.δt + X) + 28 := by rfl

theorem healthyResetSlack_val (S : Setup) (X : ℕ+) : healthyResetSlack S X = 0 := by rfl

theorem healMargin_val (S : Setup) (X : ℕ+) :
    healMargin S X = 24 * healthyDrainLen S X + 8 * S.k + 52 * S.δt + 52 * X + 44 := by rfl

/-- `M_f` covers the nonfinal reset reserve `R + 8k + 4X + 29` when `δ_t ≥ 6` (slack
`4δ_t − 13`). -/
theorem healMargin_ge_reset (S : Setup) (X : ℕ+) (hδ : 6 ≤ S.δt) :
    healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 29 ≤ healMargin S X := by
  rw [healMargin_val, healthyResetCoeff_val]
  omega

end Consensus.Goldilocks.Refinement

end
