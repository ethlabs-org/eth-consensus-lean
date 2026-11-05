module
public import ConsensusLean.Init

public section

/-! # Goldilocks FG liveness: the constants of the paper proof chain

The slot constants of the paper proof chain,
as functions of the parameters only: `k` (lock lifetime in slots), `gapH` (the honest-proposer
gap, the paper's `g`; `g` is the GST time here), `cF` (the paper's `c`, the attestation delivery
slots) and `δt` (the timeout delay). `P` is the number of phases per top height (3 under the premise
NF, `3 + 2m̄` with a bound `m̄` on finality moves). All values are in slots. -/

namespace Consensus.Goldilocks.FGLive

/-- `c = ⌈(6Δ + Δ_F) / (4Δ)⌉` (the spec's `c_F`), for `Δ ≥ 1`. -/
def cF (Δ ΔF : Nat) : Nat := (6 * Δ + ΔF + 4 * Δ - 1) / (4 * Δ)

/-- `L = k + 1`. -/
def L (k : Nat) : Nat := k + 1

/-- `D = max(c, δt)`. -/
def D (cF δt : Nat) : Nat := max cF δt

/-- One phase: `W = 2L + c + 2D + 6g − 6`. -/
def W (k gapH cF δt : Nat) : Nat := 2 * L k + cF + 2 * D cF δt + 6 * gapH - 6

/-- One top height: `R₁ = P · (W + g + c + 1)`. -/
def R1 (P k gapH cF δt : Nat) : Nat := P * (W k gapH cF δt + gapH + cF + 1)

end Consensus.Goldilocks.FGLive

end
