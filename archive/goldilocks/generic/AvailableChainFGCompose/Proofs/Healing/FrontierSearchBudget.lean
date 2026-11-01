module
public import AvailableChainFGCompose.Statements.FrontierSearch -- shake: keep (search API)
public import Mathlib.Tactic.Linarith -- shake: keep (budget algebra)
public import Mathlib.Tactic.Ring -- shake: keep (budget algebra)

public section
namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG

/-- Blueprint 21 HG.5. DC: SAME one contest repair plus the seed-gate rise tail. -/
theorem frontierSearch_contest_rise_cost (T : FGTiming) (hT : FGTimingLaws T) (G ΔF ρbar : Time)
    (hbound : LivenessBoundW T ΔF) :
    (ρbar + 3 * T.delta) + (2 * FGCompose.P T + Γ T G - 9 * T.delta) = B_cF T ΔF G ρbar := by
  have hk : (kappaF T ΔF : Time) ≤ T.roundSlots := by
    exact_mod_cast hbound.kappa_le_R
  have hb : betaF T ΔF ≤ FGCompose.P T := by
    unfold betaF FGCompose.P
    have hd := hT.delta_pos
    nlinarith
  unfold B_cF epsF
  rw [max_eq_right (by linarith [hT.delta_pos])]
  ring

/-- Blueprint 21 HG.5. DC: SAME one contest repair plus the exact-height row tail. -/
theorem frontierSearch_contest_row_cost (T : FGTiming) (ρbar : Time) :
    (ρbar + 3 * T.delta) + (FGCompose.P T - 4 * T.delta) = D_cF T ρbar := by
  change _ = ρbar + FGCompose.P T - T.delta
  ring

/-- Blueprint 21 HG.4. DC: SAME the opening-relative terminal bound
composes to 3P+Γ-13Δ, which is longer than the requested seed-gate tail. -/
theorem frontierSearch_terminal_opening_cost (T : FGTiming) (G d a t : Time)
    (hopening : a ≤ d + (FGCompose.P T - 4 * T.delta))
    (hterminal : t ≤ a + 2 * FGCompose.P T + Γ T G - 9 * T.delta) :
    t ≤ d + (3 * FGCompose.P T + Γ T G - 13 * T.delta) := by
  linarith only [hopening, hterminal]

/-- Run 2 R2-c STOP evidence. DC: SAME aligned G=8Δ, Δ=1, R=2.
This refutes only the horizon implication needed to call the terminal fact.
It does not refute HG.4 for valid executions. -/
theorem frontierSearch_terminal_horizon_gap8 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 8 - 9) ≤ horizon → a + 2 * 8 + 8 - 9 ≤ horizon) := by
  intro h
  have hb := h 0 4 15 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb

/-- Run 2 R2-c STOP evidence. DC: SAME aligned G=12Δ, Δ=1, R=2. -/
theorem frontierSearch_terminal_horizon_gap12 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 12 - 9) ≤ horizon → a + 2 * 8 + 12 - 9 ≤ horizon) := by
  intro h
  have hb := h 0 4 19 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hb


end AvailableChain.FGCompose
end
