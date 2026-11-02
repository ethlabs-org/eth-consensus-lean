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
* `healthyResetSlack S X = 0`: `r`. -/

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

end Consensus.Goldilocks.Refinement

end
