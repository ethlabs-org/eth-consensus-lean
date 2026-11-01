module
public import AvailableChainGeneric.Statements.Pure.ScheduleW
public import AvailableChainGeneric.Proofs.Pure.Schedule
public import Mathlib.Data.Nat.Find -- shake: keep (Nat.find in the alignment proof)
import Mathlib.Tactic.Linarith -- shake: keep (nlinarith in the proofs)
import Mathlib.Tactic.Positivity -- shake: keep (positivity in the window proofs)
import Mathlib.Tactic.Ring -- shake: keep (ring in the receipt-tail proof)
import Mathlib.Tactic.Tauto -- shake: keep (tauto in the coincidence proofs)

public section

namespace AvailableChain.Gen.Pure

/-- Held S arithmetic; plan §4.2. No protocol conclusion is attached. -/
theorem schedule_round_alignment {P t : Time} (hP : 0 < P) (ht : 0 < t) :
    ∃ q : Nat, 1 ≤ q ∧ t ≤ (q : Time) * P ∧ (q : Time) * P < t + P := by
  have hex : ∃ n : Nat, t ≤ (n : Time) * P := by
    refine ⟨t.toNat, ?_⟩
    rw [Int.toNat_of_nonneg ht.le]
    have hPone : 1 ≤ P := hP
    nlinarith
  let q := Nat.find hex
  have hqt : t ≤ (q : Time) * P := Nat.find_spec hex
  have hq : 1 ≤ q := by
    by_contra h
    have hz : q = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_mul] at hqt
    exact (not_le_of_gt ht) hqt
  have hprev : ((q - 1 : Nat) : Time) * P < t :=
    lt_of_not_ge (Nat.find_min hex (show q - 1 < q by omega))
  have hcast : ((q - 1 : Nat) : Time) = (q : Time) - 1 := by
    simp only [Nat.cast_sub hq, Nat.cast_one]
  rw [hcast] at hprev
  exact ⟨q, hq, hqt, by nlinarith⟩

/-- Held S arithmetic; plan §4.2. No protocol conclusion is attached. -/
theorem schedule_alignment_gst {P t GST : Time} (hP : 0 < P) (ht : 0 < t)
    (hGST : GST ≤ t) :
    ∃ q : Nat, 1 ≤ q ∧ GST ≤ (q : Time) * P ∧
      t ≤ (q : Time) * P ∧ (q : Time) * P < t + P := by
  obtain ⟨q, hq, hlo, hhi⟩ := schedule_round_alignment hP ht
  exact ⟨q, hq, hGST.trans hlo, hlo, hhi⟩

/-- Held S arithmetic; plan §4.2. No protocol conclusion is attached. -/
theorem schedule_window_round_lt {P t : Time} {q g r : Nat} (hP : 0 < P)
    (hq : (q : Time) * P < t + P) (hr : InWindow q g r) :
    (r : Time) * P < t + (g : Time) * P := by
  have hround : (r : Time) + 1 ≤ (q : Time) + g := by
    exact_mod_cast (show r + 1 ≤ q + g by have := hr.2; omega)
  have hmul := mul_le_mul_of_nonneg_right hround hP.le
  nlinarith

/-- Held S arithmetic; plan §4.2. No protocol conclusion is attached. -/
theorem schedule_finality_window_pos {x P Δ : Time} {g a : Nat}
    (hP : 0 < P) (hΔ : 0 ≤ Δ) (ha : 1 ≤ a) :
    x < x + ((g : Time) + a) * P + 9 * Δ := by
  have ha' : (1 : Time) ≤ a := by exact_mod_cast ha
  have hg : (0 : Time) ≤ g := by positivity
  nlinarith

/-- Held S arithmetic; plan §4.2. No protocol conclusion is attached. -/
theorem schedule_fgood_window_le_skip {x P Δ : Time} {g : Nat} (hP : 0 ≤ P) :
    x + ((g : Time) + 2) * P + 9 * Δ ≤ x + ((g : Time) + 4) * P + 9 * Δ := by
  nlinarith

/-- Held S arithmetic; plan §4.2. No protocol conclusion is attached. -/
theorem schedule_best_window_le_healing {qualified healing w : Time} :
    min qualified healing + w ≤ healing + w := by
  simpa only [add_comm] using add_le_add_right (min_le_right qualified healing) w

/-- Held S arithmetic; plan §4.2. No protocol conclusion is attached. -/
theorem schedule_trigger_deadline_lt {t GST healing w : Time}
    (ht : t < GST + healing) : t + w < GST + (healing + w) := by
  have := add_lt_add_right ht w
  simpa only [add_comm, add_left_comm, add_assoc] using this

/-- A positive number of rounds plus any nonnegative receipt tail. -/
theorem schedule_finality_window_pos_tail {t P x : Time} {g a : Nat}
    (hP : 0 < P) (hx : 0 ≤ x) (ha : 1 ≤ a) :
    t < t + ((g : Time) + a) * P + x := by
  have ha' : (1 : Time) ≤ a := by exact_mod_cast ha
  have hg : (0 : Time) ≤ g := by positivity
  nlinarith

theorem fgood4_W_implies_fgoodE_W {H : Slot → Prop} {R κ r : Nat}
    (h : FGood4_W H R κ r) : FGoodE_W H R κ r := h.1

theorem recF4_W_implies_recFE_W {H : Slot → Prop} {R κ g : Nat}
    {P Δ β GST horizon : Time} (h : RecF4_W H R κ P Δ β GST horizon g) :
    RecFE_W H R κ P Δ β GST horizon g := by
  refine ⟨h.1, ?_⟩
  intro q hq hGST hw
  obtain ⟨r, hr, hgood⟩ := h.2 q hq hGST hw
  exact ⟨r, hr, fgood4_W_implies_fgoodE_W hgood⟩

theorem fgoodE_W_two (H : Slot → Prop) (R r : Nat) :
    FGoodE_W H R 2 r ↔ FGood H R r ∧
      (∃ c : Slot, (r + 1) * R + 2 ≤ c ∧ c ≤ (r + 2) * R ∧ H c) := by
  rw [FGoodE_W_def, FGood_def]
  tauto

theorem fgood4_W_two (H : Slot → Prop) (R r : Nat) :
    FGood4_W H R 2 r ↔ FGood4 H R r ∧
      (∃ c : Slot, (r + 1) * R + 2 ≤ c ∧ c ≤ (r + 2) * R ∧ H c) := by
  rw [FGood4_W_def, fgoodE_W_two, FGood4_def]
  tauto

/-- At κ = 2, the fourth honest slot supplies the early carrier. -/
theorem fgood4_W_two_iff (H : Slot → Prop) (R r : Nat) (hR : 2 ≤ R) :
    FGood4_W H R 2 r ↔ FGood4 H R r := by
  rw [fgood4_W_two]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, (r + 1) * R + 2, le_rfl, ?_, h.2⟩
    have heq : (r + 2) * R = (r + 1) * R + R := by ring
    rw [heq]
    exact Nat.add_le_add_left hR _

/-- At κ = R, the carrier interval has one slot, the next round opening. -/
theorem fgoodE_W_full_round_iff (H : Slot → Prop) (R r : Nat) :
    FGoodE_W H R R r ↔ FGood4_W H R R r := by
  rw [FGood4_W_def]
  constructor
  · intro h
    obtain ⟨c, hlo, hhi, hc⟩ := h.2.2.1
    have hend : (r + 2) * R = (r + 1) * R + R := by ring
    rw [hend] at hhi
    have heq : c = (r + 1) * R + R := le_antisymm hhi hlo
    exact ⟨h, heq ▸ hc⟩
  · exact And.left

/-- Both guards end at the last pattern slot plus Δ. -/
theorem recF4_W_two_iff (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time)
    (g : Nat) (hR : 2 ≤ R) :
    RecF4_W H R 2 P Δ (8 * Δ) GST horizon g ↔ RecF4 H R P Δ GST horizon g := by
  have hguard (q : Nat) :
      windowEnd R P Δ FinForm.recF4.pat q g =
        ((q : Time) + g + 1) * P + 8 * Δ + Δ := by
    have hw := wE_recF4 R P Δ q g
    rw [windowEndA_def, FinForm.len_def] at hw
    rw [hw]
    ring
  simp only [RecF4_W_def, RecF4_def, hguard, fgood4_W_two_iff H R _ hR]

theorem recF4_W_two_iff_holds (H : Slot → Prop) (R : Nat) (P Δ GST horizon : Time)
    (g : Nat) (hR : 2 ≤ R) :
    RecF4_W H R 2 P Δ (8 * Δ) GST horizon g ↔
      FinForm.recF4.holds H R P Δ GST horizon g :=
  (recF4_W_two_iff H R P Δ GST horizon g hR).trans
    (holds_iff_recF4 H R P Δ g GST horizon).symm

/-- The right side is the Tail form at D; D is not imported. -/
theorem tail_W_two (H : Slot → Prop) (R r : Nat) :
    Tail_W H R 2 r ↔ H (r * R) ∧
      (∃ c : Slot, r * R + 2 ≤ c ∧ c ≤ (r + 1) * R ∧ H c) ∧
      H ((r + 1) * R + 2) := by rw [Tail_W_def]

theorem recFE_W_eight_delta (H : Slot → Prop) (R κ : Nat)
    (P Δ GST horizon : Time) (g : Nat) :
    RecFE_W H R κ P Δ (8 * Δ) GST horizon g ↔
      1 ≤ g ∧ ∀ q : Nat, 1 ≤ q → GST ≤ (q : Time) * P →
        ((q : Time) + g + 1) * P + 9 * Δ ≤ horizon →
        ∃ r, InWindow q g r ∧ FGoodE_W H R κ r := by
  rw [RecFE_W_def]
  have htail (x : Time) : x + 8 * Δ + Δ = x + 9 * Δ := by ring
  simp only [htail]

/-- The complete W search ends within the trigger horizon (blueprint FF5-S). -/
theorem recFE_W_guard_lt {P Δ β t horizon : Time} {q g : Nat}
    (hq : (q : Time) * P < t + P)
    (hw : t + ((g : Time) + 2) * P + β + Δ ≤ horizon) :
    ((q : Time) + g + 1) * P + β + Δ < horizon := by
  nlinarith

theorem recFE_W_extract {H : Slot → Prop} {R κ g : Nat}
    {P Δ β GST horizon t : Time}
    (hrec : RecFE_W H R κ P Δ β GST horizon g) (hP : 0 < P) (ht : 0 < t)
    (hGST : GST ≤ t) (hw : t + ((g : Time) + 2) * P + β + Δ ≤ horizon) :
    ∃ q r : Nat, t ≤ (q : Time) * P ∧ (q : Time) * P < t + P ∧
      InWindow q g r ∧ FGoodE_W H R κ r := by
  obtain ⟨q, hq, hG, hlo, hhi⟩ := schedule_alignment_gst hP ht hGST
  obtain ⟨r, hr, hgood⟩ := hrec.2 q hq hG (recFE_W_guard_lt hhi hw).le
  exact ⟨q, r, hlo, hhi, hr, hgood⟩

theorem recFE_W_receipt_lt {P Δ β t : Time} {q g r : Nat} (hP : 0 < P)
    (hq : (q : Time) * P < t + P) (hr : InWindow q g r) :
    ((r : Time) + 2) * P + β + Δ < t + ((g : Time) + 2) * P + β + Δ := by
  have := schedule_window_round_lt hP hq hr
  nlinarith

end AvailableChain.Gen.Pure
