module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

public section

/-! # Goldilocks Obligations: the named coefficients of the nonfinal reset envelope

Characterising lemmas of parameter-only coefficients, functions of the setup `S` and the index `X`
alone, shared by the reset envelope (`Growing/Obligations/Healthy/PreparationReset`) and the heal
coefficient, all fixed before any run, GST or reset is chosen. `healthyDrainLen` and `healMargin`
are defined in the statement module `Statements/Obligations` (the heal coefficient reads them);
the envelope's `healthyResetCoeff` and `healthyResetSlack`, which no statement reads, are defined
here.

* `healthyDrainLen S X = 2k + X`: the drain length `L_drain`. It pays the producer guard
  `2k + G ≤ L_drain + 1` at the gap `G = X`.
* `healthyResetCoeff S X = 20·L_drain + 24(δ_t + X) + 40`: `R`, with the envelope
  `a ≤ ready + R·Δ + r`. It is the rise-round route's `resetBoundRounds` coefficient
  `20 L_drain + 24(δ_t + X − 1) + 54` plus the lag `5λ = 10Δ` at `λ = 2Δ`.
* `healthyResetSlack S X = 0`: `r`.
* `healMargin S A X = 20 L_drain + 8k + 28δ_t + 28X + 56 + 5G`: the heal margin, `G = A.signGap`,
  `contract_heal = catchUp + M_f`, the final route's heal-bound margin on the key-dependent
  rise-round route at `λ = 2Δ` (the test `Obligations.Test.Contract.heal_val`). It covers
  the nonfinal reset reserve `R + 8k + 4X + 29 + r` when `δ_t ≥ 6` (`healMargin_ge_reset`, slack
  `4δ_t − 13`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape

/-- The reset coefficient `R = 20·L_drain + 24(δ_t + X) + 40` of the nonfinal reset envelope
(rise-round route). -/
def healthyResetCoeff (S : Setup) (X : ℕ+) : Nat := 20 * healthyDrainLen S X + 24 * (S.δt + X) + 40

/-- The literal slack `0` of the nonfinal reset envelope (not an FG delay bound). -/
def healthyResetSlack (_S : Setup) (_X : ℕ+) : Nat := 0

theorem healthyDrainLen_val (S : Setup) (X : ℕ+) : healthyDrainLen S X = 2 * S.k + X := by rfl

theorem healthyResetCoeff_val (S : Setup) (X : ℕ+) :
    healthyResetCoeff S X = 20 * healthyDrainLen S X + 24 * (S.δt + X) + 40 := by rfl

theorem healthyResetSlack_val (S : Setup) (X : ℕ+) : healthyResetSlack S X = 0 := by rfl

theorem healMargin_val (S : Setup) (A : ContractAssumptions S) (X : ℕ+) :
    healMargin S A X =
      20 * healthyDrainLen S X + 8 * S.k + 28 * S.δt + 28 * X + 56 + 5 * A.signGap := by rfl

/-- `M_f` covers the nonfinal reset reserve `R + 8k + 4X + 29` when `δ_t ≥ 6` (slack
`4δ_t − 13`), also when both sides pay `5L` for vote latency. -/
private theorem healMargin_ge_reset_within (S : Setup) (A : ContractAssumptions S) (X : ℕ+)
    (hδ : 6 ≤ S.δt) (L : Nat) :
    healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 29 + 5 * L ≤ healMargin S A X + 5 * L := by
  rw [healMargin_val, healthyResetCoeff_val]
  omega

/-- The same-tick nonfinal reset reserve. -/
theorem healMargin_ge_reset (S : Setup) (A : ContractAssumptions S) (X : ℕ+) (hδ : 6 ≤ S.δt) :
    healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 29 ≤ healMargin S A X := by
  simpa only [mul_zero, add_zero] using healMargin_ge_reset_within S A X hδ 0

end Consensus.Goldilocks.Obligations

end
