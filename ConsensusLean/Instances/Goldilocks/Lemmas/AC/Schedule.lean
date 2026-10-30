module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public section

/-! # Goldilocks SA: schedule arithmetic (F.1)

`slot(t) = ⌊t / 4Δ⌋` from time `0` on, and the facts of claims F.1 (a)–(c) about the SA's slot
times `t_s = 4Δs`: slot arithmetic, lock expiry constant on a slot, and joining. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

theorem four_delta_pos : 0 < 4 * sp.Δ := by
  have := sp.toParams.hΔ; change (0 : Int) < 4 * sp.toParams.Δ; linarith

/-- From time `0` on, `slot(t) = ⌊t / 4Δ⌋`. -/
theorem slot_eq {t : Time} (ht : 0 ≤ t) : (sp.slot t : Int) = t / (4 * sp.Δ) := by
  have hd := four_delta_pos sp
  have hq : 0 ≤ t / (4 * sp.Δ) := Int.ediv_nonneg ht hd.le
  have hst : ∀ s : Nat, sp.toParams.slotTime s = 4 * sp.Δ * s := sp.slotTime_eq
  have key : sp.slot t = (t / (4 * sp.Δ)).toNat := by
    simp only [SAParams.slot, Params.slotOf]
    rw [Nat.findGreatest_eq_iff]
    refine ⟨?_, fun _ => ?_, fun n hn hle => ?_⟩
    · have h1 : t / (4 * sp.Δ) ≤ t := Int.ediv_le_self _ ht
      exact Int.toNat_le_toNat h1
    · rw [hst, Int.toNat_of_nonneg hq]
      have := Int.ediv_mul_le t hd.ne'
      linarith
    · rw [hst]
      have h2 := Int.lt_ediv_add_one_mul_self t hd
      have : t / (4 * sp.Δ) + 1 ≤ (n : Int) := by
        exact (Int.toNat_lt' (lt_of_le_of_lt (Nat.zero_le _) hn)).mp hn
      nlinarith
  rw [key, Int.toNat_of_nonneg hq]

/-- The slot of a time in `[t_s, t_{s+1})` is `s`. -/
theorem slot_of_mem (s : Nat) {t : Time} (h₁ : sp.ts s ≤ t) (h₂ : t < sp.ts (s + 1 : Nat)) :
    sp.slot t = s := by
  have hd := four_delta_pos sp
  have ht : 0 ≤ t := le_trans (by simp only [SAParams.ts]; have := sp.toParams.hΔ; positivity) h₁
  have he := slot_eq sp ht
  simp only [SAParams.ts] at h₁ h₂
  have hlo := Int.ediv_mul_le t hd.ne'
  have hhi := Int.lt_ediv_add_one_mul_self t hd
  obtain ⟨q, hqd⟩ : ∃ q, q = t / (4 * sp.Δ) := ⟨_, rfl⟩
  rw [← hqd] at hlo hhi he
  push_cast at h₂
  have hq : q = s := by
    rcases lt_trichotomy q s with h | h | h
    · have h3 : q + 1 ≤ (s : Int) := h
      have := mul_le_mul_of_nonneg_right h3 hd.le
      nlinarith
    · exact h
    · have h3 : (s : Int) + 1 ≤ q := h
      have := mul_le_mul_of_nonneg_right h3 hd.le
      nlinarith
  exact_mod_cast he.trans hq

theorem ts_le_iff {a b : Int} : sp.ts a ≤ sp.ts b ↔ a ≤ b := by
  simp only [SAParams.ts]; exact mul_le_mul_iff_of_pos_left (four_delta_pos sp)

theorem ts_lt_iff {a b : Int} : sp.ts a < sp.ts b ↔ a < b := by
  simp only [SAParams.ts]; exact mul_lt_mul_iff_of_pos_left (four_delta_pos sp)

/-- From time `0` on, a slot starts at or before `t` exactly when it is at most `slot(t)`. -/
theorem ts_le_iff_le_slot {t : Time} (ht : 0 ≤ t) (a : Int) : sp.ts a ≤ t ↔ a ≤ sp.slot t := by
  have hd := four_delta_pos sp
  have he := slot_eq sp ht
  have hlo := Int.ediv_mul_le t hd.ne'
  have hhi := Int.lt_ediv_add_one_mul_self t hd
  rw [← he] at hlo hhi
  simp only [SAParams.ts]
  constructor
  · intro h
    by_contra hc
    have h3 : (sp.slot t : Int) + 1 ≤ a := lt_of_not_ge hc
    have := mul_le_mul_of_nonneg_left h3 hd.le
    nlinarith
  · intro h
    have := mul_le_mul_of_nonneg_left h hd.le
    nlinarith

/-- **F.1 (a).** -/
theorem slot_arithmetic : SlotArithmetic sp := by
  intro s
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  refine ⟨fun i hi => slot_of_mem sp s ?_ ?_, ?_, ?_⟩
  · simp only [SAParams.ts]
    have : (0 : Int) ≤ i * sp.Δ := by positivity
    linarith
  · simp only [SAParams.ts]; push_cast
    have : (i : Int) ≤ 3 := by exact_mod_cast Nat.le_of_lt_succ hi
    nlinarith
  · simp only [SAParams.ts]; push_cast; ring
  · simp only [SAParams.ts]; push_cast; ring

/-- **F.1 (b).** -/
theorem lock_expiry : LockExpiry sp := by
  intro FGP L Φ m t t' h₁ h₂ h₁' h₂'
  simp only [liveLocks, slot_of_mem sp m h₁ h₂, slot_of_mem sp m h₁' h₂']

/-- **F.1 (c), joining.** -/
theorem joined_from : JoinedFrom sp := by
  intro A j w t hA hwt
  have hj : (0 : Time) ≤ sp.ts j := by
    have : (0 : Time) ≤ sp.Δ := sp.toParams.hΔ.le
    simp only [SAParams.ts]; positivity
  simp only [joined, hA, WithBot.coe_le_coe]
  refine ⟨fun hw => ?_, fun hw₁ hw₂ => ?_⟩
  · subst hw
    have ht : 0 ≤ t := le_trans hj hwt
    rw [ts_le_iff, ts_le_iff_le_slot sp ht]; push_cast; omega
  · have ht : 0 ≤ t := le_trans (le_trans hj hw₁.le) hwt
    rw [ts_le_iff_le_slot sp ht]; push_cast
    constructor
    · intro h
      have := lt_of_lt_of_le hw₁ h
      rw [ts_lt_iff] at this; omega
    · intro h
      have : sp.ts ((j + 1 : Nat) : Int) ≤ sp.ts ((sp.slot t : Int) - 1) := by
        rw [ts_le_iff]; push_cast; omega
      exact le_trans hw₂.le this

end Consensus.Goldilocks.SA

end
