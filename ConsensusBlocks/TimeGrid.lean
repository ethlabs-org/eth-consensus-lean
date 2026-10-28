module
public import ConsensusProblem.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Time grid (building block)

Slots of `slotDeltas · Δ` time units; slot `s` starts at `s · slotLen`. Duties of
a shape sit at `slotTime s + j · Δ` (phase `j`). Time is integer, so slots exist
only from time 0 on (slot 0 starts at 0). -/

namespace Consensus.Blocks

/-- A slot index. -/
abbrev Slot := Nat

/-- Slots of `slotDeltas · Δ`; duties sit at `slotTime s + j · Δ` (phase `j`). -/
structure TimeGrid where
  /-- The slot length in multiples of `Δ`; positive by type. -/
  slotDeltas : ℕ+

namespace TimeGrid

variable (G : TimeGrid)

/-- The slot length in time units: `slotDeltas · Δ`. -/
def slotLen (Δ : Time) : Time := ((G.slotDeltas : Nat) : Time) * Δ

/-- The start time of slot `s`: `s · slotLen`. -/
def slotTime (Δ : Time) (s : Slot) : Time := (s : Time) * G.slotLen Δ

/-- The slot whose time plus `off` is `t`, if any. -/
def slotAt? (Δ off t : Time) : Option Slot :=
  if 0 ≤ t - off ∧ (t - off) % G.slotLen Δ = 0 then some ((t - off) / G.slotLen Δ).toNat
  else none

theorem slotLen_pos {Δ : Time} (hΔ : 0 < Δ) : 0 < G.slotLen Δ :=
  Int.mul_pos (by exact_mod_cast G.slotDeltas.pos) hΔ

theorem slotAt?_eq_some {Δ : Time} (hΔ : 0 < Δ) {off t : Time} {s : Slot} :
    G.slotAt? Δ off t = some s ↔ G.slotTime Δ s + off = t := by
  have hl := G.slotLen_pos hΔ
  unfold slotAt? slotTime
  by_cases hc : 0 ≤ t - off ∧ (t - off) % G.slotLen Δ = 0
  · rw [ite_eq_left hc, Option.some.injEq]
    obtain ⟨h0, hm⟩ := hc
    have hdiv : 0 ≤ (t - off) / G.slotLen Δ := Int.ediv_nonneg h0 hl.le
    have ht : (t - off) / G.slotLen Δ * G.slotLen Δ = t - off :=
      Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hm)
    constructor
    · rintro rfl
      rw [Int.toNat_of_nonneg hdiv, ht]; ring
    · intro he
      have : t - off = (s : Time) * G.slotLen Δ := by linarith
      rw [this, Int.mul_ediv_cancel _ hl.ne']; simp
  · rw [ite_eq_right hc]
    refine ⟨fun h => (nomatch h), fun he => ?_⟩
    have : t - off = (s : Time) * G.slotLen Δ := by linarith
    exact absurd ⟨this ▸ Int.mul_nonneg (by positivity) hl.le, this ▸ Int.mul_emod_left _ _⟩ hc

theorem slotTime_add {Δ : Time} (s j : Slot) :
    G.slotTime Δ (s + j) = G.slotTime Δ s + (j : Time) * G.slotLen Δ := by
  unfold slotTime; push_cast; ring

/-- Every window `(t, t + k · slotLen]` with `t ≥ 0` and `k ≥ 1` contains a slot
start. -/
theorem exists_slot_in_window {Δ : Time} (hΔ : 0 < Δ) {t : Time} (ht : 0 ≤ t) {k : Nat}
    (hk : 1 ≤ k) :
    ∃ s, t < G.slotTime Δ s ∧ G.slotTime Δ s ≤ t + k * G.slotLen Δ := by
  have hl := G.slotLen_pos hΔ
  refine ⟨(t / G.slotLen Δ).toNat + 1, ?_, ?_⟩
  · have hq : 0 ≤ t / G.slotLen Δ := Int.ediv_nonneg ht hl.le
    unfold slotTime
    push_cast
    rw [Int.toNat_of_nonneg hq]
    have := Int.lt_ediv_add_one_mul_self t hl
    linarith
  · have hq : 0 ≤ t / G.slotLen Δ := Int.ediv_nonneg ht hl.le
    unfold slotTime
    push_cast
    rw [Int.toNat_of_nonneg hq]
    have h1 := Int.ediv_mul_le t hl.ne'
    have hk' : (1 : Time) ≤ k := by exact_mod_cast hk
    nlinarith

end TimeGrid

end Consensus.Blocks
end
