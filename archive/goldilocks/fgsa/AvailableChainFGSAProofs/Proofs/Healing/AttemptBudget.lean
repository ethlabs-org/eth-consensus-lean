module
public import AvailableChainFGSAProofs.Proofs.Shared.Recurrence
public import AvailableChainFGSAClaims.Statements.ComposeStmt

public section

namespace AvailableChain.FGSA.Run

/-! Blueprint 21 H.10:1436–1492. These are integer-time budget calculations.
The repair allowance is ρΓ in every row. -/

theorem healing_attempt_raise_contest_budget (p : Params) (G : Time) (k : AttemptKey)
    (htask : k.task = .raise) (hphase : k.phase = .contest) :
    attemptBudget p G k = ρΓ p G + 3 * P p + Γ p G - 10 * p.Δ := by
  unfold attemptBudget
  rw [htask, hphase]

theorem healing_attempt_raise_other_budget (p : Params) (G : Time) (k : AttemptKey)
    (htask : k.task = .raise) (hphase : k.phase ≠ .contest) :
    attemptBudget p G k = ρΓ p G + 6 * P p + 2 * Γ p G - 18 * p.Δ := by
  unfold attemptBudget
  rw [htask]
  cases hp : k.phase with
  | gap => rfl
  | topJ => rfl
  | contest => exact (hphase hp).elim

theorem healing_attempt_firstRow_contest_budget (p : Params) (G : Time) (k : AttemptKey)
    (htask : k.task = .firstRow) (hphase : k.phase = .contest) :
    attemptBudget p G k = ρΓ p G + P p - p.Δ := by
  unfold attemptBudget
  rw [htask, hphase]

theorem healing_attempt_firstRow_other_budget (p : Params) (G : Time) (k : AttemptKey)
    (htask : k.task = .firstRow) (hphase : k.phase ≠ .contest) :
    attemptBudget p G k = ρΓ p G + 4 * P p + Γ p G - 9 * p.Δ := by
  unfold attemptBudget
  rw [htask]
  cases hp : k.phase with
  | gap => rfl
  | topJ => rfl
  | contest => exact (hphase hp).elim

theorem healing_attempt_raise_contest_cost (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) =
      ρΓ p G + 3 * P p + Γ p G - 10 * p.Δ := by ring

theorem healing_attempt_raise_other_cost (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 4 * p.Δ) +
      (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) =
      ρΓ p G + 6 * P p + 2 * Γ p G - 18 * p.Δ := by ring

theorem healing_attempt_firstRow_contest_cost (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) =
      ρΓ p G + P p - p.Δ := by ring

theorem healing_attempt_firstRow_other_cost (p : Params) (G : Time) :
    (3 * p.Δ + ρΓ p G) + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 4 * p.Δ) +
      (P p - 4 * p.Δ) = ρΓ p G + 4 * P p + Γ p G - 9 * p.Δ := by ring

/-- The high-source alternative fits the larger gap/top-J allowance. -/
theorem healing_attempt_high_source_cost (p : Params) (G : Time) (hG : 4 * p.Δ ≤ G) :
    4 * P p + Γ p G - 13 * p.Δ ≤ 6 * P p + 2 * Γ p G - 21 * p.Δ := by
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hΓ : 4 * p.Δ ≤ Γ p G := hG.trans (fgsa_gamma_bounds p G).1
  linarith [p.deltaPos]

/-- The existing promotion horizon is five Δ after its terminal deadline. -/
theorem healing_attempt_terminal_horizon_gap (p : Params) (a G : Time) :
    a + 2 * P p + Γ p G - 9 * p.Δ < a + 2 * P p + Γ p G - 4 * p.Δ := by
  linarith [p.deltaPos]

end AvailableChain.FGSA.Run
end
