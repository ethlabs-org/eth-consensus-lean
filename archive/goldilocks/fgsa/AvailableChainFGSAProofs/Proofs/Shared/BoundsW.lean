module
public import AvailableChainFGSAClaims.Statements.BoundsW
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule
public import AvailableChainFGSAProofs.Proofs.Shared.Recurrence
public import AvailableChainGeneric.Proofs.Pure.ScheduleW

public section

namespace AvailableChain.FGSA.Run

/-- The W carrier starts at slot rR + κ. -/
theorem fgsa_grid_carrier_timeW (p : Params) (ΔF : Time) (r : Nat) :
    Gen.Pure.SlotGrid.t p.Δ (r * p.R + kappaF p ΔF) = carrierTimeW p ΔF r := by
  rw [Gen.Pure.SlotGrid.t_def, Gen.Pure.slotLen_def, carrierTimeW_def, betaF_def]
  change 4 * p.Δ * ((r * p.R + kappaF p ΔF : Nat) : Time) =
    (r : Time) * (4 * (p.R : Time) * p.Δ) + 4 * (kappaF p ΔF : Time) * p.Δ
  push_cast
  ring

theorem fgsa_grid_kernel_deadlineW (p : Params) (ΔF : Time) (r : Nat) :
    Gen.Pure.SlotGrid.T p.Δ p.R r + betaF p ΔF + p.Δ = kernelDeadlineW p ΔF r := by
  rw [fgsa_grid_round_period, kernelDeadlineW_def]

theorem F4_W_implies_FE_W {p : Params} {ΔF : Time} {H : Slot → Prop}
    {GST horizon : Time} {g : Nat} (h : F4_W p ΔF H GST horizon g) :
    FE_W p ΔF H GST horizon g := by
  rw [FE_W_def]
  rw [F4_W_def] at h
  exact Gen.Pure.recF4_W_implies_recFE_W h

/-- Integer ceiling specification; subtraction is in Time, not Nat. -/
theorem kappaF_ceiling (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF) :
    ((kappaF p ΔF : Time) - 1) * (4 * p.Δ) < 6 * p.Δ + ΔF ∧
      6 * p.Δ + ΔF ≤ (kappaF p ΔF : Time) * (4 * p.Δ) := by
  have hd : 0 < 4 * p.Δ := by have := p.deltaPos; linarith
  have hn : 0 ≤ 6 * p.Δ + ΔF + 4 * p.Δ - 1 := by
    have hd1 : (1 : Time) ≤ p.Δ := p.deltaPos
    linarith
  rw [kappaF_def, Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
  have hlo := Int.ediv_mul_le (6 * p.Δ + ΔF + 4 * p.Δ - 1) (ne_of_gt hd)
  have hhi := Int.lt_ediv_add_one_mul_self (6 * p.Δ + ΔF + 4 * p.Δ - 1) hd
  constructor <;> nlinarith

theorem kappaF_ge_two (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF) :
    2 ≤ kappaF p ΔF := by
  have h := (kappaF_ceiling p ΔF hF).2
  have hd := p.deltaPos
  by_contra hnot
  have hk : (kappaF p ΔF : Time) ≤ 1 := by
    exact_mod_cast (show kappaF p ΔF ≤ 1 by omega)
  nlinarith

theorem kappaF_eq_two_iff (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF) :
    kappaF p ΔF = 2 ↔ ΔF ≤ 2 * p.Δ := by
  have hc := kappaF_ceiling p ΔF hF
  have hk := kappaF_ge_two p ΔF hF
  have hd := p.deltaPos
  constructor
  · intro h
    rw [h] at hc
    norm_num at hc
    nlinarith [hc.2]
  · intro h
    have hle : (kappaF p ΔF : Time) < 3 := by nlinarith [hc.1]
    have : kappaF p ΔF < 3 := by exact_mod_cast hle
    omega

theorem betaF_eq_eight_delta (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF)
    (hhi : ΔF ≤ 2 * p.Δ) : betaF p ΔF = 8 * p.Δ := by
  rw [betaF_def, (kappaF_eq_two_iff p ΔF hF).2 hhi]
  norm_num

theorem epsF_eq_zero (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF)
    (hhi : ΔF ≤ 2 * p.Δ) : epsF p ΔF = 0 := by
  rw [epsF_def, betaF_eq_eight_delta p ΔF hF hhi, sub_self]

theorem carrierTimeW_eq_carrierTime2 (p : Params) (ΔF : Time) (r : Nat)
    (hF : 0 ≤ ΔF) (hhi : ΔF ≤ 2 * p.Δ) : carrierTimeW p ΔF r = carrierTime2 p r := by
  rw [carrierTimeW_def, betaF_eq_eight_delta p ΔF hF hhi]
  rfl

theorem kernelDeadlineW_eq_kernelDeadline (p : Params) (ΔF : Time) (r : Nat)
    (hF : 0 ≤ ΔF) (hhi : ΔF ≤ 2 * p.Δ) : kernelDeadlineW p ΔF r = kernelDeadline p r := by
  rw [kernelDeadlineW_def, betaF_eq_eight_delta p ΔF hF hhi]
  change (r : Time) * P p + 8 * p.Δ + p.Δ = (r : Time) * P p + 9 * p.Δ
  ring

theorem W_W_eq_W_F (p : Params) (ΔF : Time) (g : Nat)
    (hF : 0 ≤ ΔF) (hhi : ΔF ≤ 2 * p.Δ) : W_W p ΔF g = W_F p g := by
  rw [W_W_def, betaF_eq_eight_delta p ΔF hF hhi]
  change ((g : Time) + 2) * P p + 8 * p.Δ + p.Δ = ((g : Time) + 2) * P p + 9 * p.Δ
  ring

theorem betaF_bounds (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF) :
    6 * p.Δ + ΔF ≤ betaF p ΔF ∧ betaF p ΔF < 10 * p.Δ + ΔF := by
  rw [betaF_def]
  have hc := kappaF_ceiling p ΔF hF
  constructor <;> nlinarith [hc.1, hc.2]

theorem betaF_le_period (p : Params) (ΔF : Time) (hR : LivenessBoundW p ΔF) :
    betaF p ΔF ≤ P p := by
  have hk : (kappaF p ΔF : Time) ≤ p.R := by exact_mod_cast hR.kappa_le_R
  change 4 * (kappaF p ΔF : Time) * p.Δ ≤ 4 * (p.R : Time) * p.Δ
  have := p.deltaPos
  nlinarith

theorem epsF_nonneg (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF) :
    0 ≤ epsF p ΔF := by
  have hk : (2 : Time) ≤ kappaF p ΔF := by exact_mod_cast kappaF_ge_two p ΔF hF
  rw [epsF_def, betaF_def]
  have := p.deltaPos
  nlinarith

theorem epsF_bounds (p : Params) (ΔF : Time) (hF : 0 ≤ ΔF)
    (hR : LivenessBoundW p ΔF) :
    0 ≤ epsF p ΔF ∧ epsF p ΔF ≤ P p - 8 * p.Δ := by
  rw [epsF_def]
  exact ⟨epsF_nonneg p ΔF hF, sub_le_sub_right (betaF_le_period p ΔF hR) _⟩

/-- The action clock in period coordinates; no equation export is needed. -/
theorem actionTime_periodW (p : Params) (r : Nat) :
    p.actionTime r = (r : Time) * P p + 6 * p.Δ := by
  rw [← fgsa_grid_action_time, Gen.Pure.SlotGrid.a_def, Gen.Pure.SlotGrid.d_def]
  rw [← Gen.Pure.SlotGrid.T_def, fgsa_grid_round_period]

theorem action_delivery_boundsW (p : Params) (ΔF : Time) (r : Nat)
    (hF : 0 ≤ ΔF) (hR : LivenessBoundW p ΔF) :
    ActionDeliveryBoundsW p ΔF r := by
  rw [ActionDeliveryBoundsW_def, actionTime_periodW, carrierTimeW_def]
  have hb := (betaF_bounds p ΔF hF).1
  have hP := betaF_le_period p ΔF hR
  exact ⟨rfl, by linarith, by nlinarith⟩

theorem kernel_before_next_actionW (p : Params) (ΔF : Time) (r : Nat)
    (hR : LivenessBoundW p ΔF) : KernelBeforeNextActionW p ΔF r := by
  rw [KernelBeforeNextActionW_def, kernelDeadlineW_def, actionTime_periodW]
  have hb := betaF_le_period p ΔF hR
  have hd := p.deltaPos
  push_cast
  nlinarith

theorem E_gF_eq (p : Params) (ΔF G ρbar : Time) (hR : LivenessBoundW p ΔF) :
    E_gF p ΔF G ρbar = E_g p G ρbar := by
  have hb := betaF_le_period p ΔF hR
  rw [E_gF_def, epsF_def, max_eq_right (by have := p.deltaPos; linarith)]
  change ρbar + Γ p G + (2 * P p - p.Δ) = ρbar + 2 * P p + Γ p G - p.Δ
  linarith

theorem B_cF_eq (p : Params) (ΔF G ρbar : Time) (hR : LivenessBoundW p ΔF) :
    B_cF p ΔF G ρbar = B_c p G ρbar := by
  have hb := betaF_le_period p ΔF hR
  rw [B_cF_def, epsF_def, max_eq_right (by have := p.deltaPos; linarith)]
  change ρbar + Γ p G + (2 * P p - 6 * p.Δ) = ρbar + 2 * P p + Γ p G - 6 * p.Δ
  linarith

theorem E_jF_bounds (p : Params) (ΔF G ρbar : Time) (hF : 0 ≤ ΔF) :
    E_j p G ρbar ≤ E_jF p ΔF G ρbar ∧
      E_jF p ΔF G ρbar ≤ E_j p G ρbar + epsF p ΔF := by
  have he := epsF_nonneg p ΔF hF
  change max _ _ ≤ max _ _ ∧ max _ _ ≤ max _ _ + _
  constructor
  · exact max_le_max (by linarith) le_rfl
  · apply max_le
    · have := le_max_left (ρbar + P p + Γ p G + 3 * p.Δ) (2 * P p + Γ p G - 4 * p.Δ)
      linarith
    · have := le_max_right (ρbar + P p + Γ p G + 3 * p.Δ) (2 * P p + Γ p G - 4 * p.Δ)
      linarith

theorem BF_bounds (p : Params) (ΔF G ρbar : Time) (hF : 0 ≤ ΔF)
    (hR : LivenessBoundW p ΔF) :
    B p G ρbar ≤ BF p ΔF G ρbar ∧
      BF p ΔF G ρbar ≤ B p G ρbar + 2 * epsF p ΔF := by
  have hj := E_jF_bounds p ΔF G ρbar hF
  rw [BF_def, B_resetF_def, E_gF_eq p ΔF G ρbar hR, B_cF_eq p ΔF G ρbar hR,
    D_cF_def]
  change (3 * P p + 2 * E_g p G ρbar + 2 * E_j p G ρbar + B_c p G ρbar +
    (ρbar + P p - p.Δ) + Γ p G + 4 * p.Δ ≤ _) ∧
    (_ ≤ 3 * P p + 2 * E_g p G ρbar + 2 * E_j p G ρbar + B_c p G ρbar +
    (ρbar + P p - p.Δ) + Γ p G + 4 * p.Δ + 2 * epsF p ΔF)
  constructor <;> linarith

theorem B_HF_bounds (p : Params) (ΔF G : Time) (hF : 0 ≤ ΔF)
    (hR : LivenessBoundW p ΔF) :
    B_H p G ≤ B_HF p ΔF G ∧ B_HF p ΔF G ≤ B_H p G + 2 * epsF p ΔF := by
  have h2 := BF_bounds p ΔF G (ρΓ p G) hF hR
  have h1 := BF_bounds p ΔF G (ρ₁ p G) hF hR
  change (if p.k ≤ 2 * p.R + 1 then min (B p G (ρΓ p G)) (B p G (ρ₁ p G))
      else B p G (ρΓ p G)) ≤ B_HF p ΔF G ∧ _
  rw [B_HF_def, B_H2F_def, B_H1F_def]
  change _ ∧ _ ≤ (if p.k ≤ 2 * p.R + 1 then min (B p G (ρΓ p G)) (B p G (ρ₁ p G))
      else B p G (ρΓ p G)) + _
  split_ifs with h
  · constructor
    · exact min_le_min h2.1 h1.1
    · calc
        min _ _ ≤ min (B p G (ρΓ p G) + 2 * epsF p ΔF)
          (B p G (ρ₁ p G) + 2 * epsF p ΔF) := min_le_min h2.2 h1.2
        _ = _ := min_add_add_right _ _ _
  · exact h2

theorem B_HF_eq_B_H (p : Params) (ΔF G : Time) (hF : 0 ≤ ΔF)
    (hhi : ΔF ≤ 2 * p.Δ) : B_HF p ΔF G = B_H p G := by
  have hR : LivenessBoundW p ΔF :=
    ⟨by rw [(kappaF_eq_two_iff p ΔF hF).2 hhi]; exact p.RLarge⟩
  have h := B_HF_bounds p ΔF G hF hR
  rw [epsF_eq_zero p ΔF hF hhi] at h
  exact le_antisymm (by simpa only [mul_zero, add_zero] using h.2) h.1


theorem B_bestF_le_healing (p : Params) (ΔF G : Time) (g : Nat) :
    B_bestF p ΔF G g ≤ B_HF p ΔF G := by
  rw [B_bestF_def]
  exact min_le_right _ _

/-- Closed form from the reset sum, under the paper round bound. -/
theorem BF_max (p : Params) (ΔF G ρbar : Time) (hR : LivenessBoundW p ΔF) :
    BF p ΔF G ρbar =
      max (6 * ρbar + 12 * P p + 6 * Γ p G + p.Δ + 2 * epsF p ΔF)
        (4 * ρbar + 14 * P p + 6 * Γ p G - 13 * p.Δ) := by
  rw [BF_def, B_resetF_def, E_gF_eq p ΔF G ρbar hR, B_cF_eq p ΔF G ρbar hR,
    E_jF_def, D_cF_def]
  change 3 * P p + 2 * (ρbar + 2 * P p + Γ p G - p.Δ) +
    2 * max (ρbar + P p + Γ p G + 3 * p.Δ + epsF p ΔF) (2 * P p + Γ p G - 4 * p.Δ) +
    (ρbar + 2 * P p + Γ p G - 6 * p.Δ) + (ρbar + P p - p.Δ) + Γ p G + 4 * p.Δ = _
  rcases le_total (ρbar + P p + Γ p G + 3 * p.Δ + epsF p ΔF)
    (2 * P p + Γ p G - 4 * p.Δ) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_left (by linarith)]
    ring

theorem resetF_healing_eq (p : Params) (ΔF G : Time) :
    B'_resetF p ΔF G = B_HF p ΔF G - Γ p G - 4 * p.Δ := by
  rw [B'_resetF_def, B_HF_def, B_H2F_def, B_H1F_def, BF_def, BF_def]
  split_ifs
  · rw [min_add_add_right, min_add_add_right]
    ring
  · ring

/-- Blueprint 21:1850–1863, with the full delay range of the third row. -/
theorem B_HF_numeric_351 (p : Params) (ΔF : Time)
    (hR : p.R = 3) (hk : p.k = 2) (hlo : 2 * p.Δ < ΔF) (hhi : ΔF ≤ 6 * p.Δ) :
    B_HF p ΔF (8 * p.Δ) = 351 * p.Δ := by
  have hd := p.deltaPos
  have hF : 0 ≤ ΔF := by linarith
  have hc := kappaF_ceiling p ΔF hF
  have hc3 : kappaF p ΔF = 3 := by
    have hlt : (kappaF p ΔF : Time) < 4 := by nlinarith [hc.1]
    have hge : 2 < (kappaF p ΔF : Time) := by nlinarith [hc.2]
    have hnlt : kappaF p ΔF < 4 := by exact_mod_cast hlt
    have hnge : 2 < kappaF p ΔF := by exact_mod_cast hge
    omega
  have hreg : LivenessBoundW p ΔF := ⟨by rw [hc3, hR]⟩
  have he : epsF p ΔF = 4 * p.Δ := by rw [epsF_def, betaF_def, hc3]; norm_num; ring
  have hP : P p = 12 * p.Δ := by change 4 * (p.R : Time) * p.Δ = _; rw [hR]; ring
  have hL : L p = 7 * p.Δ := by change (4 * (p.k : Time) - 1) * p.Δ = _; rw [hk]; ring
  have hG : Γ p (8 * p.Δ) = 8 * p.Δ := by
    exact fgsa_gamma_eq_of_dvd p ⟨2, by ring⟩
  rw [B_HF_def, ite_eq_left (by omega), B_H2F_def, B_H1F_def,
    BF_max p ΔF _ _ hreg, BF_max p ΔF _ _ hreg]
  change min (max (6 * (2 * L p + Γ p (8 * p.Δ) + 8 * p.Δ) + 12 * P p +
    6 * Γ p (8 * p.Δ) + p.Δ + 2 * epsF p ΔF)
    (4 * (2 * L p + Γ p (8 * p.Δ) + 8 * p.Δ) + 14 * P p + 6 * Γ p (8 * p.Δ) - 13 * p.Δ))
    (max (6 * (L p + Γ p (8 * p.Δ) + 10 * p.Δ) + 12 * P p +
    6 * Γ p (8 * p.Δ) + p.Δ + 2 * epsF p ΔF)
    (4 * (L p + Γ p (8 * p.Δ) + 10 * p.Δ) + 14 * P p + 6 * Γ p (8 * p.Δ) - 13 * p.Δ)) = _
  rw [he, hP, hL, hG]
  rw [max_eq_left (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]
  ring

/-- Common arithmetic for the first two rows of blueprint 21:1850–1863. -/
private theorem B_HF_numeric_low_delay (p : Params) (ΔF : Time)
    (hR : p.R ≤ 3) (hk : p.k = 2) (hF : 0 ≤ ΔF) (hhi : ΔF ≤ 2 * p.Δ) :
    B_HF p ΔF (8 * p.Δ) = (199 + 48 * (p.R : Time)) * p.Δ := by
  have hd := p.deltaPos
  have hR' : (p.R : Time) ≤ 3 := by exact_mod_cast hR
  have hreg : LivenessBoundW p ΔF :=
    ⟨by rw [(kappaF_eq_two_iff p ΔF hF).2 hhi]; exact p.RLarge⟩
  have hL : L p = 7 * p.Δ := by change (4 * (p.k : Time) - 1) * p.Δ = _; rw [hk]; ring
  have hG : Γ p (8 * p.Δ) = 8 * p.Δ := by
    exact fgsa_gamma_eq_of_dvd p ⟨2, by ring⟩
  have hP : P p ≤ 12 * p.Δ := by
    change 4 * (p.R : Time) * p.Δ ≤ 12 * p.Δ
    nlinarith
  rw [B_HF_def, ite_eq_left (by rw [hk]; have := p.RLarge; omega), B_H2F_def, B_H1F_def,
    BF_max p ΔF _ _ hreg, BF_max p ΔF _ _ hreg]
  change min (max (6 * (2 * L p + Γ p (8 * p.Δ) + 8 * p.Δ) + 12 * P p +
    6 * Γ p (8 * p.Δ) + p.Δ + 2 * epsF p ΔF)
    (4 * (2 * L p + Γ p (8 * p.Δ) + 8 * p.Δ) + 14 * P p + 6 * Γ p (8 * p.Δ) - 13 * p.Δ))
    (max (6 * (L p + Γ p (8 * p.Δ) + 10 * p.Δ) + 12 * P p +
    6 * Γ p (8 * p.Δ) + p.Δ + 2 * epsF p ΔF)
    (4 * (L p + Γ p (8 * p.Δ) + 10 * p.Δ) + 14 * P p + 6 * Γ p (8 * p.Δ) - 13 * p.Δ)) = _
  rw [epsF_eq_zero p ΔF hF hhi, hL, hG]
  rw [max_eq_left (by linarith), max_eq_left (by linarith), min_eq_right (by linarith)]
  change 6 * (7 * p.Δ + 8 * p.Δ + 10 * p.Δ) + 12 * (4 * (p.R : Time) * p.Δ) +
    6 * (8 * p.Δ) + p.Δ + 2 * 0 = (199 + 48 * (p.R : Time)) * p.Δ
  ring

/-- The first numeric row, for every positive integer Δ and its full delay range. -/
theorem B_HF_numeric_295 (p : Params) (ΔF : Time)
    (hR : p.R = 2) (hk : p.k = 2) (hF : 0 ≤ ΔF) (hhi : ΔF ≤ 2 * p.Δ) :
    B_HF p ΔF (8 * p.Δ) = 295 * p.Δ := by
  rw [B_HF_numeric_low_delay p ΔF (by omega) hk hF hhi, hR]
  norm_num

/-- The second numeric row, for every positive integer Δ and its full delay range. -/
theorem B_HF_numeric_343 (p : Params) (ΔF : Time)
    (hR : p.R = 3) (hk : p.k = 2) (hF : 0 ≤ ΔF) (hhi : ΔF ≤ 2 * p.Δ) :
    B_HF p ΔF (8 * p.Δ) = 343 * p.Δ := by
  rw [B_HF_numeric_low_delay p ΔF (by omega) hk hF hhi, hR]
  norm_num

end AvailableChain.FGSA.Run
