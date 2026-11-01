module
public import AvailableChainGeneric.Statements.Pure.Schedule
import Mathlib.Tactic.Linarith -- shake: keep (re-export)
import Mathlib.Tactic.Positivity -- shake: keep (re-export)
import Mathlib.Tactic.Ring -- shake: keep (re-export)
import Mathlib.Tactic.Tauto -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

/-- Pattern inclusion and window growth (a D36 shape): the guard premise `hend` is
necessary, because a sub-pattern can end earlier. -/
-- Source: GenScheduleBodies.lean:59; use a distinct short name for F-13.
theorem RecPat.recPat_mono {H : Slot → Prop} {R : Nat} {pat pat' : Pattern}
    {P Δ GST horizon : Time} {lo lo' g g' : Nat}
    (hsub : pat' ⊆ pat) (hg : g ≤ g') (hlo : lo' ≤ g')
    (hend : ∀ q, windowEnd R P Δ pat q g ≤ windowEnd R P Δ pat' q g') :
    RecPat H R pat P Δ GST horizon lo g → RecPat H R pat' P Δ GST horizon lo' g' := by
  rintro ⟨-, h⟩
  refine ⟨hlo, fun q hq hG hw => ?_⟩
  obtain ⟨r, ⟨h1, h2⟩, hr⟩ := h q hq hG ((hend q).trans hw)
  exact ⟨r, ⟨h1, by omega⟩, fun o ho => hr o (hsub ho)⟩


section FG
variable (H : Slot → Prop) (R : Nat)

/-! ### Pattern constants (by `decide`) -/

theorem lr_recS : FinForm.recS.pat.lastRound = 0 := by decide
theorem ls_recS : FinForm.recS.pat.lastSlot = 2 := by decide
theorem lr_recF : FinForm.recF.pat.lastRound = 2 := by decide
theorem ls_recF : FinForm.recF.pat.lastSlot = 2 := by decide
theorem lr_recF4 : FinForm.recF4.pat.lastRound = 2 := by decide
theorem ls_recF4 : FinForm.recF4.pat.lastSlot = 2 := by decide
theorem lr_recSkip : FinForm.recSkip.pat.lastRound = 2 := by decide
theorem ls_recSkip : FinForm.recSkip.pat.lastSlot = 2 := by decide
theorem lr_strong : FinForm.strongW.pat.lastRound = 2 := by decide
theorem ls_strong : FinForm.strongW.pat.lastSlot = 2 := by decide

/-! ### The windowEndA table (P3 §4.5), no hypothesis on P, Δ, R -/

variable (P Δ : Time) (q g : Nat) (t : Time)

theorem wE_recS : windowEndA .recS R P Δ q g = ((q:Time) + g - 1) * P + 9 * Δ := by
  simp only [windowEndA_def, windowEnd_def, Pattern.tailEnd_def, slotLen_def, FinForm.len_def,
    lr_recS, ls_recS]
  push_cast
  ring
theorem wE_recF : windowEndA .recF R P Δ q g = ((q:Time) + g + 1) * P + 9 * Δ := by
  simp only [windowEndA_def, windowEnd_def, Pattern.tailEnd_def, slotLen_def, FinForm.len_def,
    lr_recF, ls_recF]
  push_cast
  ring
theorem wE_recF4 : windowEndA .recF4 R P Δ q g = ((q:Time) + g + 1) * P + 9 * Δ := by
  simp only [windowEndA_def, windowEnd_def, Pattern.tailEnd_def, slotLen_def, FinForm.len_def,
    lr_recF4, ls_recF4]
  push_cast
  ring
theorem wE_recSkip : windowEndA .recSkip R P Δ q g = ((q:Time) + g + 1) * P + 9 * Δ := by
  simp only [windowEndA_def, windowEnd_def, Pattern.tailEnd_def, slotLen_def, FinForm.len_def,
    lr_recSkip, ls_recSkip]
  push_cast; ring
theorem wE_strongW (hg : 1 ≤ g) :
    windowEndA .strongW R P Δ q g = ((q:Time) + g) * P + 9 * Δ := by
  have : FinForm.lit.pat = FinForm.strongW.pat := rfl
  simp only [windowEndA_def, windowEnd_def, Pattern.tailEnd_def, slotLen_def, FinForm.len_def,
    lr_strong, ls_strong]
  push_cast [Nat.cast_sub hg]; ring
theorem wE_lit (hg : 2 ≤ g) :
    windowEndA .lit R P Δ q g = ((q:Time) + g - 1) * P + 9 * Δ := by
  have e : FinForm.lit.pat = FinForm.strongW.pat := rfl
  simp only [windowEndA_def, windowEnd_def, Pattern.tailEnd_def, slotLen_def, FinForm.len_def,
    e, lr_strong, ls_strong]
  push_cast [Nat.cast_sub hg]; ring
/-- The literal value (fgsa-lean O5). -/
theorem wEAt_recC : windowEndAt R P Δ FinForm.recC.pat t g = t + g * P + 9 * Δ := by
  have e : FinForm.recC.pat = FinForm.strongW.pat := rfl
  simp only [windowEndAt_def, Pattern.tailEnd_def, slotLen_def, e, ls_strong]; push_cast; ring

theorem wEAtA_value : windowEndAtA R P Δ t g = t + g * P + 9 * Δ := wEAt_recC R P Δ g t

/-- The P3 sanity lemma (§12.1): needs 0 ≤ P. -/
theorem sanity_recSkip (hP : 0 ≤ P) :
    windowEndA .recSkip R P Δ q 0 ≤ ((q:Time) + 3) * P + 9 * Δ := by
  rw [wE_recSkip]; push_cast; nlinarith

/-! ### PatAt of each pattern -/

theorem patAt_recS (r : Nat) : PatAt H R FinForm.recS.pat r ↔ Qualified H R r := by
  simp [PatAt_def, FinForm.pat_def, Qualified_def]
theorem patAt_recF (r : Nat) : PatAt H R FinForm.recF.pat r ↔ FGood H R r := by
  simp [PatAt_def, FinForm.pat_def, FGood_def]
theorem patAt_recF4 (r : Nat) : PatAt H R FinForm.recF4.pat r ↔ FGood4 H R r := by
  simp [PatAt_def, FinForm.pat_def, FGood4_def, FGood_def]; tauto
theorem patAt_recSkip (r : Nat) : PatAt H R FinForm.recSkip.pat r ↔ Skip H R r := by
  simp [PatAt_def, FinForm.pat_def, Skip_def]
theorem patAt_strong (b : Nat) : PatAt H R FinForm.strongW.pat b ↔ Strong H R (b + 2) := by
  simp only [PatAt_def, FinForm.pat_def, Strong_def, Qualified_def,
    Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, Nat.add_sub_cancel, show b + 2 - 1 = b + 1 by omega]
  simp only [add_zero, le_add_iff_nonneg_left, zero_le, true_and]
  tauto

theorem strong_two {r : Nat} (h : Strong H R r) : 2 ≤ r := h.2.1

/-! ### FinForm.holds_iff, every g -/

variable (GST horizon : Time)

theorem holds_iff_recS :
    FinForm.recS.holds H R P Δ GST horizon g ↔ RecS H R P Δ GST horizon g := by
  simp only [FinForm.holds_def, RecPat_def, RecS_def, FinForm.lo_def, FinForm.len_def, patAt_recS]
  constructor
  · rintro ⟨h1, -, h⟩; exact ⟨h1, h⟩
  · rintro ⟨h1, h⟩; exact ⟨h1, h1, h⟩
theorem holds_iff_recF :
    FinForm.recF.holds H R P Δ GST horizon g ↔ RecF H R P Δ GST horizon g := by
  simp only [FinForm.holds_def, RecPat_def, RecF_def, FinForm.lo_def, FinForm.len_def, patAt_recF]
  constructor
  · rintro ⟨h1, -, h⟩; exact ⟨h1, h⟩
  · rintro ⟨h1, h⟩; exact ⟨h1, h1, h⟩
theorem holds_iff_recF4 :
    FinForm.recF4.holds H R P Δ GST horizon g ↔ RecF4 H R P Δ GST horizon g := by
  simp only [FinForm.holds_def, RecPat_def, RecF4_def, FinForm.lo_def, FinForm.len_def, patAt_recF4]
  constructor
  · rintro ⟨h1, -, h⟩; exact ⟨h1, h⟩
  · rintro ⟨h1, h⟩; exact ⟨h1, h1, h⟩
theorem holds_iff_recSkip :
    FinForm.recSkip.holds H R P Δ GST horizon g ↔ RecSkip H R P Δ GST horizon g := by
  simp only [FinForm.holds_def, RecPat_def, RecSkip_def, FinForm.lo_def, FinForm.len_def,
    patAt_recSkip]
  constructor
  · rintro ⟨h1, -, h⟩; exact ⟨h1, h⟩
  · rintro ⟨h1, h⟩; exact ⟨h1, h1, h⟩

theorem holds_iff_strongW :
    FinForm.strongW.holds H R P Δ GST horizon g ↔ StrongRecW H R P Δ GST horizon g := by
  simp only [FinForm.holds_def, RecPat_def, StrongRecW_def, FinForm.lo_def, FinForm.len_def,
    patAt_strong, InWindow_def]
  constructor
  · rintro ⟨h3, -, h⟩
    refine ⟨h3, fun q hq hG hw => ?_⟩
    obtain ⟨b, ⟨h1, h2⟩, hb⟩ := h q hq hG hw
    exact ⟨b + 2, by omega, by omega, hb⟩
  · rintro ⟨h3, h⟩
    refine ⟨h3, by omega, fun q hq hG hw => ?_⟩
    obtain ⟨r, h1, h2, hr⟩ := h q hq hG hw
    have := strong_two H R hr
    exact ⟨r - 2, ⟨by omega, by omega⟩, by rwa [Nat.sub_add_cancel this]⟩

theorem holds_iff_lit :
    FinForm.lit.holds H R P Δ GST horizon g ↔ Lit H R P Δ GST horizon g := by
  have e : FinForm.lit.pat = FinForm.strongW.pat := rfl
  simp only [FinForm.holds_def, RecPat_def, Lit_def, FinForm.lo_def, FinForm.len_def, e,
    patAt_strong, InWindow_def]
  constructor
  · rintro ⟨h3, -, h⟩
    refine ⟨h3, fun q hq hG hw => ?_⟩
    obtain ⟨b, ⟨h1, h2⟩, hb⟩ := h q hq hG hw
    exact ⟨b + 2, by omega, by omega, hb⟩
  · rintro ⟨h3, h⟩
    refine ⟨h3, by omega, fun q hq hG hw => ?_⟩
    obtain ⟨r, h1, h2, hr⟩ := h q hq hG hw
    have := strong_two H R hr
    exact ⟨r - 2, ⟨by omega, by omega⟩, by rwa [Nat.sub_add_cancel this]⟩

theorem holds_iff_recC :
    FinForm.recC.holds H R P Δ GST horizon g ↔ RecC H R P Δ GST horizon g := by
  have e : FinForm.recC.pat = FinForm.strongW.pat := rfl
  simp only [FinForm.holds_def, RecPatAt_def, RecC_def, FinForm.lo_def, wEAt_recC]
  simp only [e, lr_strong, patAt_strong]
  constructor
  · rintro ⟨h3, h⟩
    refine ⟨h3, fun t ht hw => ?_⟩
    obtain ⟨b, h1, h2, hb⟩ := h t ht hw
    exact ⟨b + 2, by push_cast; linarith, by push_cast at h2 ⊢; linarith, hb⟩
  · rintro ⟨h3, h⟩
    refine ⟨h3, fun t ht hw => ?_⟩
    obtain ⟨r, h1, h2, hr⟩ := h t ht hw
    have h2r := strong_two H R hr
    refine ⟨r - 2, ?_, ?_, by rwa [Nat.sub_add_cancel h2r]⟩
    · push_cast [Nat.cast_sub h2r]; linarith
    · push_cast [Nat.cast_sub h2r]; linarith

theorem holds_iff_fgood (r : Nat) :
    (FinForm.fgood r).holds H R P Δ GST horizon g ↔ FGood H R r := by
  simp [FinForm.holds_def, PatAt_def, FinForm.pat_def, FGood_def]
theorem holds_iff_fgood4 (r : Nat) :
    (FinForm.fgood4 r).holds H R P Δ GST horizon g ↔ FGood4 H R r := by
  simp [FinForm.holds_def, PatAt_def, FinForm.pat_def, FGood4_def, FGood_def]; tauto

/-! ### holds_iff at the minimum g of each form -/

theorem inWindow_one (q r : Nat) : InWindow q 1 r ↔ r = q := by
  simp only [InWindow_def]; omega

theorem recS_min :
    FinForm.recS.holds H R P Δ GST horizon 1 ↔
      ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P →
        windowEnd R P Δ FinForm.recS.pat q 1 ≤ horizon → Qualified H R q := by
  simp only [FinForm.holds_def, RecPat_def, FinForm.lo_def, FinForm.len_def, patAt_recS,
    inWindow_one]
  simp

theorem recF_min :
    FinForm.recF.holds H R P Δ GST horizon 1 ↔
      ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P →
        windowEnd R P Δ FinForm.recF.pat q 1 ≤ horizon → FGood H R q := by
  simp only [FinForm.holds_def, RecPat_def, FinForm.lo_def, FinForm.len_def, patAt_recF,
    inWindow_one]
  simp

theorem recF4_min :
    FinForm.recF4.holds H R P Δ GST horizon 1 ↔
      ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P →
        windowEnd R P Δ FinForm.recF4.pat q 1 ≤ horizon → FGood4 H R q := by
  simp only [FinForm.holds_def, RecPat_def, FinForm.lo_def, FinForm.len_def, patAt_recF4,
    inWindow_one]
  simp

theorem recSkip_min :
    FinForm.recSkip.holds H R P Δ GST horizon 1 ↔
      ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P →
        windowEnd R P Δ FinForm.recSkip.pat q 1 ≤ horizon → Skip H R q := by
  simp only [FinForm.holds_def, RecPat_def, FinForm.lo_def, FinForm.len_def, patAt_recSkip,
    inWindow_one]
  simp

theorem strongPair_iff :
    FinForm.strongW.holds H R P Δ GST horizon 3 ↔
      ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P →
        windowEnd R P Δ FinForm.strongW.pat q 2 ≤ horizon →
        Strong H R (q + 2) ∨ Strong H R (q + 3) := by
  simp only [FinForm.holds_def, RecPat_def, FinForm.lo_def, FinForm.len_def, patAt_strong,
    InWindow_def]
  constructor
  · rintro ⟨-, -, h⟩ q hq hG hw
    obtain ⟨b, ⟨h1, h2⟩, hb⟩ := h q hq hG hw
    rcases (show b = q ∨ b = q + 1 by omega) with rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hb
  · intro h
    refine ⟨le_refl _, by omega, fun q hq hG hw => ?_⟩
    rcases h q hq hG hw with h2 | h3
    · exact ⟨q, ⟨le_refl _, by omega⟩, h2⟩
    · exact ⟨q + 1, ⟨by omega, by omega⟩, h3⟩

theorem lit_min :
    FinForm.lit.holds H R P Δ GST horizon 3 ↔
      ∀ q : Nat, 1 ≤ q → GST ≤ ↑q * P →
        windowEnd R P Δ FinForm.lit.pat q 1 ≤ horizon → Strong H R (q + 2) := by
  have e : FinForm.lit.pat = FinForm.strongW.pat := rfl
  simp only [FinForm.holds_def, RecPat_def, FinForm.lo_def, FinForm.len_def, e, patAt_strong]
  simp [inWindow_one]

theorem recC_min :
    FinForm.recC.holds H R P Δ GST horizon 3 ↔
      ∀ t : Time, max GST 1 ≤ t → t + 3 * P + 9 * Δ ≤ horizon →
        ∃ r : Nat, t + 2 * P ≤ r * P ∧ r * P ≤ t + 3 * P ∧ Strong H R r := by
  rw [holds_iff_recC]; simp [RecC_def]

/-! ### OPEN 7 bridge and producers -/

theorem QualSearch_iff_recPat (hP : 0 < P) (hg : 1 ≤ g) :
    QualSearch H R P Δ GST horizon g ↔ RecPat H R FinForm.recS.pat P Δ GST horizon 1 (g + 1) := by
  have hw : ∀ q : Nat, windowEnd R P Δ FinForm.recS.pat q (g + 1) = ↑q * P + ↑g * P + 9 * Δ := by
    intro q
    simp only [windowEnd_def, Pattern.tailEnd_def, slotLen_def, lr_recS, ls_recS]
    push_cast
    ring
  have hr : ∀ q r : Nat, (↑q * P ≤ ↑r * P ∧ ↑r * P ≤ ↑q * P + ↑g * P) ↔ InWindow q (g + 1) r := by
    intro q r
    simp only [InWindow_def]
    constructor
    · rintro ⟨h1, h2⟩
      have a : (q : ℤ) ≤ r := le_of_mul_le_mul_right h1 hP
      have b : (r : ℤ) ≤ ((q + g : ℕ) : ℤ) := le_of_mul_le_mul_right (by push_cast; linarith) hP
      exact ⟨by exact_mod_cast a, by have := (Int.ofNat_le.mp b); omega⟩
    · rintro ⟨h1, h2⟩
      have a : (q : ℤ) ≤ r := by exact_mod_cast h1
      have b : (r : ℤ) ≤ q + g := by exact_mod_cast (show r ≤ q + g by omega)
      constructor <;> nlinarith
  simp only [QualSearch_def, RecPat_def, hw, ← patAt_recS]
  constructor
  · intro h; refine ⟨by omega, fun q hq hG hw' => ?_⟩
    obtain ⟨r, h1, h2, h3⟩ := h q hq hG hw'
    exact ⟨r, (hr q r).1 ⟨h1, h2⟩, h3⟩
  · rintro ⟨-, h⟩ q hq hG hw'
    obtain ⟨r, h1, h2⟩ := h q hq hG hw'
    exact ⟨r, ((hr q r).2 h1).1, ((hr q r).2 h1).2, h2⟩

theorem QualSearch.of_recS (hP : 0 < P) :
    FinForm.recS.holds H R P Δ GST horizon g → QualSearch H R P Δ GST horizon g := by
  rw [holds_iff_recS]
  rintro ⟨h1, h⟩ q hq hG hw
  have hwe : windowEnd R P Δ FinForm.recS.pat q g ≤ horizon := by
    have := wE_recS R P Δ q g; simp only [windowEndA_def, FinForm.len_def] at this
    rw [this]; nlinarith
  obtain ⟨r, ⟨h2, h3⟩, hr⟩ := h q hq hG hwe
  refine ⟨r, ?_, ?_, hr⟩
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h2) hP.le
  · have : (r : Time) ≤ q + g := by exact_mod_cast (show r ≤ q + g by omega)
    nlinarith

theorem QualSearch.of_lit (hP : 0 < P) :
    FinForm.lit.holds H R P Δ GST horizon g → QualSearch H R P Δ GST horizon g := by
  rw [holds_iff_lit]
  rintro ⟨h3, h⟩ q hq hG hw
  have : windowEnd R P Δ FinForm.lit.pat q (g - 2) ≤ horizon := by
    have := wE_lit R P Δ q g (by omega); simp only [windowEndA_def, FinForm.len_def] at this
    rw [this]
    have : (1 : Time) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
    nlinarith
  obtain ⟨r, h1, h2, hr⟩ := h q hq hG this
  refine ⟨r, ?_, ?_, hr.1⟩
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show q ≤ r by omega)) hP.le
  · have : (r : Time) ≤ q + g := by exact_mod_cast (show r ≤ q + g by omega)
    nlinarith

theorem QualSearch.of_recC (hP : 0 < P) :
    FinForm.recC.holds H R P Δ GST horizon g → QualSearch H R P Δ GST horizon g := by
  rw [holds_iff_recC]
  rintro ⟨h3, h⟩ q hq hG hw
  have hq1 : (1 : Time) ≤ q * P := by
    have : (1 : Time) ≤ q := by exact_mod_cast hq
    have hP1 : (1 : Time) ≤ P := hP
    nlinarith
  obtain ⟨r, h1, h2, hr⟩ := h (q * P) (max_le hG hq1) hw
  exact ⟨r, by linarith, h2, hr.1⟩

end FG

section SlotReading
variable (R : Nat) (P Δ : Time) (q g : Nat)

/-- For every FinForm pattern and every R, the true last slot index at base b is
(b + lastRound)·R + lastSlot, so the lexicographic body is the "last slot" reading. -/
theorem idx_lex (f : FinForm) (b : Nat) :
    lastSlotIdx R f.pat b = (b + f.pat.lastRound) * R + f.pat.lastSlot := by
  cases f <;> simp [lastSlotIdx_def, FinForm.pat_def, Pattern.lastRound_def, Pattern.lastSlot_def,
    Finset.filter_insert, Finset.filter_singleton, add_mul] <;> omega

theorem slotReading (f : FinForm) (hP : P = 4 * R * Δ) (hb : 1 ≤ q + g) :
    windowEnd R P Δ f.pat q g = 4 * Δ * (lastSlotIdx R f.pat (q + g - 1) : Time) + Δ := by
  rw [idx_lex, windowEnd_def, Pattern.tailEnd_def, slotLen_def, hP]
  push_cast [Nat.cast_sub hb]; ring

theorem compat_finForm (f : FinForm) : f.pat.Compat R := by
  have e1 : FinForm.lit.pat = FinForm.strongW.pat := rfl
  have e2 : FinForm.recC.pat = FinForm.strongW.pat := rfl
  have e3 : ∀ r, (FinForm.fgood r).pat = FinForm.recF.pat := fun _ => rfl
  have e4 : ∀ r, (FinForm.fgood4 r).pat = FinForm.recF4.pat := fun _ => rfl
  cases f <;> simp only [Pattern.Compat_def, e1, e2, e3, e4, ls_recS, ls_recF, ls_recF4,
    ls_recSkip, ls_strong] <;> rintro ⟨a, c⟩ ho <;> simp [FinForm.pat_def] at ho ⊢ <;> omega

/-- Every slot of the pattern at base b is at most slot (b + lastRound)·R + lastSlot. -/
theorem slot_le_last {pat : Pattern} (hc : pat.Compat R) {o : Nat × Nat} (ho : o ∈ pat)
    (b : Nat) : (b + o.1) * R + o.2 ≤ (b + pat.lastRound) * R + pat.lastSlot := by
  have h1 : o.1 ≤ pat.lastRound := Finset.le_sup (f := Prod.fst) ho
  rcases Nat.lt_or_ge o.1 pat.lastRound with h | h
  · have h2 := hc o ho
    have : (b + o.1 + 1) * R ≤ (b + pat.lastRound) * R := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · have heq : o.1 = pat.lastRound := le_antisymm h1 h
    have : o.2 ≤ pat.lastSlot :=
      Finset.le_sup (f := Prod.snd) (Finset.mem_filter.2 ⟨ho, heq⟩)
    rw [heq]; omega

/-- Each pattern event in the window (slot start + Δ) is at or before `windowEnd`. -/
theorem event_le_windowEnd {pat : Pattern} (hc : pat.Compat R) (hP : P = 4 * R * Δ)
    (hΔ : 0 ≤ Δ) {b : Nat} (hb : InWindow q g b) {o : Nat × Nat} (ho : o ∈ pat) :
    slotLen Δ * (((b + o.1) * R + o.2 : Nat) : Time) + Δ ≤ windowEnd R P Δ pat q g := by
  have hs := slot_le_last R hc ho b
  have hb' : b + 1 ≤ q + g := hb.2
  have hs' : (((b + o.1) * R + o.2 : Nat) : Time) ≤
      ((b : Time) + pat.lastRound) * R + pat.lastSlot := by exact_mod_cast hs
  have hbq : ((b : Time) + 1) ≤ (q : Time) + g := by exact_mod_cast hb'
  have hR : (0 : Time) ≤ R := by positivity
  simp only [windowEnd_def, Pattern.tailEnd_def, slotLen_def, hP]
  have : ((b : Time) + pat.lastRound) * R ≤ ((q : Time) + g - 1 + pat.lastRound) * R :=
    mul_le_mul_of_nonneg_right (by linarith) hR
  nlinarith

/-- The same for `windowEndAt`: a base b whose last pattern round starts by t + gP. -/
theorem event_le_windowEndAt {pat : Pattern} (hc : pat.Compat R) (hP : P = 4 * R * Δ)
    (hΔ : 0 ≤ Δ) {t : Time} {b : Nat} (hb : (↑b + ↑pat.lastRound) * P ≤ t + ↑g * P)
    {o : Nat × Nat} (ho : o ∈ pat) :
    slotLen Δ * (((b + o.1) * R + o.2 : Nat) : Time) + Δ ≤ windowEndAt R P Δ pat t g := by
  have hs := slot_le_last R hc ho b
  have hs' : (((b + o.1) * R + o.2 : Nat) : Time) ≤
      ((b : Time) + pat.lastRound) * R + pat.lastSlot := by exact_mod_cast hs
  simp only [windowEndAt_def, Pattern.tailEnd_def, slotLen_def]
  rw [hP] at hb ⊢
  nlinarith

/-- f.lo ≤ g gives a nonempty RecPat width (P3 FinForm.len_pos). -/
theorem FinForm.len_pos (f : FinForm) (h : f.lo ≤ g) : 1 ≤ f.len g := by
  cases f <;> simp only [FinForm.lo_def, FinForm.len_def] at h ⊢ <;> omega

/-! ### Positive control (P3 Tests/Recurrence, the Astra example) -/
theorem strong_all (q : Nat) (hq : 1 ≤ q) : Strong (fun s : Nat => 0 < s) 2 (q + 2) := by
  simp only [Strong_def, Qualified_def]; refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega

end SlotReading

end AvailableChain.Gen.Pure
