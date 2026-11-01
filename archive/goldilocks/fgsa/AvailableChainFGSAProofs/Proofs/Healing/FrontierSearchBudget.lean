module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchBudget
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW -- shake: keep (frozen bound proof API)

public section

/-! Blueprint 21 HG.4/HG.5 and H.11. Keep the frozen budgets.
The terminal fact has an action-relative horizon. It does not state the
entry-age bound from HG.2a_F or continuation through same-frontier events. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5aBudgetTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5aBudgetTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5aBudgetTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl


/-- Blueprint 21 HG.5. DC: SAME one contest repair plus the seed-gate rise tail. -/
theorem frontierSearch_contest_rise_cost (p : Params) (G ΔF ρbar : Time)
    (hbound : LivenessBoundW p ΔF) :
    (ρbar + 3 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) = B_cF p ΔF G ρbar := by
  exact FGCompose.frontierSearch_contest_rise_cost (p0d5aBudgetTiming p)
    (p0d5aBudgetTimingLaws p) G ΔF ρbar ⟨hbound.1⟩


/-- Blueprint 21 HG.5. DC: SAME one contest repair plus the exact-height row tail. -/
theorem frontierSearch_contest_row_cost (p : Params) (ρbar : Time) :
    (ρbar + 3 * p.Δ) + (P p - 4 * p.Δ) = D_cF p ρbar := by
  exact FGCompose.frontierSearch_contest_row_cost (p0d5aBudgetTiming p) ρbar


/-- Blueprint 21 HG.4. DC: SAME the opening-relative terminal bound
composes to 3P+Γ-13Δ, which is longer than the requested seed-gate tail. -/
theorem frontierSearch_terminal_opening_cost (p : Params) (G d a t : Time)
    (hopening : a ≤ d + (P p - 4 * p.Δ))
    (hterminal : t ≤ a + 2 * P p + Γ p G - 9 * p.Δ) :
    t ≤ d + (3 * P p + Γ p G - 13 * p.Δ) := by
  exact FGCompose.frontierSearch_terminal_opening_cost (p0d5aBudgetTiming p) G d a t
    hopening hterminal


/-- Run 2 R2-c STOP evidence. DC: SAME aligned G=8Δ, Δ=1, R=2.
This refutes only the horizon implication needed to call the terminal fact.
It does not refute HG.4 for valid executions. -/
theorem frontierSearch_terminal_horizon_gap8 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 8 - 9) ≤ horizon → a + 2 * 8 + 8 - 9 ≤ horizon) := by
  exact FGCompose.frontierSearch_terminal_horizon_gap8


/-- Run 2 R2-c STOP evidence. DC: SAME aligned G=12Δ, Δ=1, R=2. -/
theorem frontierSearch_terminal_horizon_gap12 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 12 - 9) ≤ horizon → a + 2 * 8 + 12 - 9 ≤ horizon) := by
  exact FGCompose.frontierSearch_terminal_horizon_gap12


end AvailableChain.FGSA.Run
end
