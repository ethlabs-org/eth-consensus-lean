module
public import AvailableChainFGSAClaims.Statements.Recurrence -- shake: keep (public aliases or axiom audit commands)
public import AvailableChainFGSAClaims.Statements.Bounds
public import AvailableChainGeneric.Proofs.Pure.Schedule

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure

/-- GUP r2: integer-time recovery budgets round the gap up to the proposal grid. -/
theorem fgsa_gamma_bounds (p : Params) (G : Time) :
    G ≤ Γ p G ∧ Γ p G < G + 4 * p.Δ := by
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hlo := Int.ediv_mul_le (G + 4 * p.Δ - 1) (ne_of_gt hd)
  have hhi := Int.lt_ediv_add_one_mul_self (G + 4 * p.Δ - 1) hd
  change G ≤ 4 * p.Δ * ((G + 4 * p.Δ - 1) / (4 * p.Δ)) ∧
    4 * p.Δ * ((G + 4 * p.Δ - 1) / (4 * p.Δ)) < G + 4 * p.Δ
  constructor <;> nlinarith

/-- GUP r2: the rounded gap is a whole number of proposal slots. -/
theorem fgsa_gamma_aligned (p : Params) (G : Time) : 4 * p.Δ ∣ Γ p G := by
  exact dvd_mul_right _ _

/-- GUP r2: an aligned gap keeps its existing numerical value. -/
theorem fgsa_gamma_eq_of_dvd (p : Params) {G : Time} (h : 4 * p.Δ ∣ G) : Γ p G = G := by
  obtain ⟨z, rfl⟩ := h
  have hb := fgsa_gamma_bounds p (4 * p.Δ * z)
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  obtain ⟨q, hq⟩ := fgsa_gamma_aligned p (4 * p.Δ * z)
  rw [hq] at hb ⊢
  have hle : z ≤ q := by nlinarith [hb.1]
  have hlt : q < z + 1 := by nlinarith [hb.2]
  have : q = z := by omega
  rw [this]

/-- GUP r2: a second round-up does not change a bound. -/
theorem fgsa_gamma_idem (p : Params) (G : Time) : Γ p (Γ p G) = Γ p G :=
  fgsa_gamma_eq_of_dvd p (fgsa_gamma_aligned p G)

variable (H : Slot → Prop) (R : Nat) (P Δ : Time) (q g : Nat) (t GST horizon : Time)

/-- Pattern inclusion alone is insufficient: the last round and slot also agree. -/
theorem fgsa_strongW_recF
    (h : FinForm.strongW.holds H R P Δ GST horizon g) :
    FinForm.recF.holds H R P Δ GST horizon (g - 1) := by
  change 3 ≤ g ∧ Gen.Pure.RecPat _ _ _ _ _ _ _ 1 (g - 1) at h
  change 1 ≤ g - 1 ∧ Gen.Pure.RecPat _ _ _ _ _ _ _ 1 (g - 1)
  refine ⟨by omega, Gen.Pure.RecPat.recPat_mono (by decide) (le_refl _) (by omega) ?_ h.2⟩
  intro q
  simp only [Gen.Pure.windowEnd_def, Gen.Pure.Pattern.tailEnd_def,
    Gen.Pure.lr_strong, Gen.Pure.lr_recF, Gen.Pure.ls_strong, Gen.Pure.ls_recF, le_refl]

theorem fgsa_lit_recF
    (h : FinForm.lit.holds H R P Δ GST horizon g) :
    FinForm.recF.holds H R P Δ GST horizon (g - 2) := by
  change 3 ≤ g ∧ Gen.Pure.RecPat _ _ _ _ _ _ _ 1 (g - 2) at h
  change 1 ≤ g - 2 ∧ Gen.Pure.RecPat _ _ _ _ _ _ _ 1 (g - 2)
  refine ⟨by omega, Gen.Pure.RecPat.recPat_mono (by decide) (le_refl _) (by omega) ?_ h.2⟩
  intro q
  change Gen.Pure.windowEnd R P Δ Gen.Pure.FinForm.strongW.pat q (g - 2) ≤
    Gen.Pure.windowEnd R P Δ Gen.Pure.FinForm.recF.pat q (g - 2)
  simp only [Gen.Pure.windowEnd_def, Gen.Pure.Pattern.tailEnd_def,
    Gen.Pure.lr_strong, Gen.Pure.lr_recF, Gen.Pure.ls_strong, Gen.Pure.ls_recF, le_refl]

/-- Remove only the horizon guard from a round recurrence premise. -/
theorem fgsa_recPat_restricted (pat : Gen.Pure.Pattern) (lo : Nat)
    (hg : lo ≤ g)
    (h : ∀ q : Nat, 1 ≤ q → GST ≤ (q : Time) * P →
      ∃ r, Gen.Pure.InWindow q g r ∧ Gen.Pure.PatAt H R pat r) :
    Gen.Pure.RecPat H R pat P Δ GST horizon lo g :=
  ⟨hg, fun q hq hG _ => h q hq hG⟩

/-- Remove only the horizon guard from the integer-time recurrence premise. -/
theorem fgsa_recPatAt_restricted (pat : Gen.Pure.Pattern) (lo : Nat)
    (hg : lo ≤ g)
    (h : ∀ t : Time, max GST 1 ≤ t →
      ∃ b : Nat, t ≤ (b : Time) * P ∧
        ((b : Time) + pat.lastRound) * P ≤ t + g * P ∧ Gen.Pure.PatAt H R pat b) :
    Gen.Pure.RecPatAt H R pat P Δ GST horizon lo g :=
  ⟨hg, fun t ht _ => h t ht⟩

/-- An unrestricted recurrence supplies every finite horizon. -/
theorem fgsa_restricted_of_unrestricted (f : FinForm)
    (h : ∀ horizon : Time, f.holds H R P Δ GST horizon g) :
    f.holds H R P Δ GST horizon g := h horizon

/-- Restrict a finite recurrence to an earlier horizon. -/
theorem fgsa_horizon_mono (f : FinForm) {horizon' : Time}
    (hle : horizon' ≤ horizon) (h : f.holds H R P Δ GST horizon g) :
    f.holds H R P Δ GST horizon' g := by
  cases f with
  | fgood r => exact h
  | fgood4 r => exact h
  | recC =>
    exact ⟨h.1, fun t ht hw => h.2 t ht (hw.trans hle)⟩
  | recF | recF4 | recS | recSkip | strongW | lit =>
    exact ⟨h.1, h.2.1, fun q hq hG hw => h.2.2 q hq hG (hw.trans hle)⟩

theorem fgsa_B_max (p : Params) (G ρbar : Time) :
    B p G ρbar = max (6 * ρbar + 12 * Run.P p + 6 * Γ p G + p.Δ)
      (4 * ρbar + 14 * Run.P p + 6 * Γ p G - 13 * p.Δ) := by
  change 3 * Run.P p + 2 * (ρbar + 2 * Run.P p + Γ p G - p.Δ) +
    2 * max (ρbar + Run.P p + Γ p G + 3 * p.Δ) (2 * Run.P p + Γ p G - 4 * p.Δ) +
    (ρbar + 2 * Run.P p + Γ p G - 6 * p.Δ) + (ρbar + Run.P p - p.Δ) +
    Γ p G + 4 * p.Δ = _
  rcases le_total (ρbar + Run.P p + Γ p G + 3 * p.Δ)
    (2 * Run.P p + Γ p G - 4 * p.Δ) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
    linarith
  · rw [max_eq_left h, max_eq_left (by linarith)]
    linarith

/-! GEN-FIRST (F-31): QualSearch.of_recS, .of_recC and .of_lit are already
proved in Gen.Pure (Schedule.lean:294–332), with exactly hP : 0 < P.
The exported QualSearch name resolves those producers without duplicate proofs.
Blueprint 21:2377–2378; 00:297–301. Consumers: H-time and FF5. -/

namespace QualSearch
export Gen.Pure.QualSearch (of_recS of_recC of_lit)
end QualSearch

end AvailableChain.FGSA.Run

end
