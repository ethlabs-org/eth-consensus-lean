module
public import ConsensusLean.Init

public section

/-! # Goldilocks FG liveness: the constants of the r14 proof chain

The slot constants of the paper proof chain (workbench `fg-liveness/r14-end-to-end`, README §2),
as functions of the parameters only: `k` (lock lifetime in slots), `gapH` (the honest-proposer
gap, r14 `g`; `g` stays the GST time in this project), `cF` (r14 `c`, the row delivery slots)
and `δt` (the timeout delay). `P` is the number of phases per top height (3 under the premise
NF, `3 + 2m̄` with a bound `m̄` on finality moves). All values are in slots. -/

namespace Consensus.Goldilocks.FGLive

/-- `c = ⌈(6Δ + Δ_F) / (4Δ)⌉` (fgsa: c_F), for `Δ ≥ 1`. -/
def cF (Δ ΔF : Nat) : Nat := (6 * Δ + ΔF + 4 * Δ - 1) / (4 * Δ)

/-- `L = k + 1`. -/
def L (k : Nat) : Nat := k + 1

/-- `D = max(c, δt)`. -/
def D (cF δt : Nat) : Nat := max cF δt

/-- One phase (s3 L3.3): `W = 2L + c + 2D + 6g − 6`. -/
def W (k gapH cF δt : Nat) : Nat := 2 * L k + cF + 2 * D cF δt + 6 * gapH - 6

/-- One top height (s3 L3.3): `R₁ = P · (W + g + c + 1)`. -/
def R1 (P k gapH cF δt : Nat) : Nat := P * (W k gapH cF δt + gapH + cF + 1)

/-- One phase at top `H + 1` (s3 L3.5): `W_row = 2L + c + D + 4g − 3`. -/
def Wrow (k gapH cF δt : Nat) : Nat := 2 * L k + cF + D cF δt + 4 * gapH - 3

/-- The reset row (s3 L3.5): `R_row = P · (W_row + g + c + 1)`. -/
def Rrow (P k gapH cF δt : Nat) : Nat := P * (Wrow k gapH cF δt + gapH + cF + 1)

/-- The reset (s3 L3.5): `T_reset = 2 R₁ + R_row`. -/
def Treset (P k gapH cF δt : Nat) : Nat := 2 * R1 P k gapH cF δt + Rrow P k gapH cF δt

/-- The AC heal after the reset (s1 L1.5 bound): `T_AC = 2L + g`. -/
def TAC (k gapH : Nat) : Nat := 2 * L k + gapH

/-- Follow (s4 L4.5, `B_CH = 1`): `T_follow = 1 + T_AC`. -/
def Tfollow (k gapH : Nat) : Nat := 1 + TAC k gapH

/-- The heal point offset from `s_G` (s4 L4.6): `T_heal = T_reset + T_follow`. -/
def Theal (P k gapH cF δt : Nat) : Nat := Treset P k gapH cF δt + Tfollow k gapH

/-- Justification latency (s5 L5.4): `Λ_J = c + 2(g − 1)`. -/
def ΛJ (gapH cF : Nat) : Nat := cF + 2 * (gapH - 1)

/-- Finality latency (s6 L6.5): `Λ_F = δt + 2c + 6g − 4`. -/
def ΛF (gapH cF δt : Nat) : Nat := δt + 2 * cF + 6 * gapH - 4

/-- The closed form of README §2 under NF (`P = 3`), for `g ≥ 1`:
`T_heal = 20L + 18c + 15D + 58g − 35`. -/
theorem Theal_closed {k gapH cF δt : Nat} (hg : 1 ≤ gapH) :
    Theal 3 k gapH cF δt = 20 * L k + 18 * cF + 15 * D cF δt + 58 * gapH - 35 := by
  simp only [Theal, Treset, R1, Rrow, W, Wrow, Tfollow, TAC, L]
  omega

/-- `Λ_F = δt + g + 2Λ_J + g` (s6 L6.5), for `g ≥ 1`. -/
theorem ΛF_eq {gapH cF δt : Nat} (hg : 1 ≤ gapH) :
    ΛF gapH cF δt = δt + gapH + 2 * ΛJ gapH cF + gapH := by
  simp only [ΛF, ΛJ]
  omega

/-- At `Δ_F = 32Δ`, `c = 10`. -/
theorem cF_32 {Δ : Nat} (hΔ : 1 ≤ Δ) : cF Δ (32 * Δ) = 10 := by
  simp only [cF]
  rw [Nat.div_eq_iff (by omega)]
  omega

end Consensus.Goldilocks.FGLive

end
