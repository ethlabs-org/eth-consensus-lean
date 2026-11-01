module
public import AvailableChainFGSA.Model.Spec.Transitions
public import Mathlib.Tactic.Ring -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Spec

/-- Revocation of s occurs at the vote time of s+1, before that vote. -/
theorem revoke_vote_time (Δ : Time) (s : Int) :
    phaseTime Δ s 5 = phaseTime Δ (s + 1) 1 := by
  unfold phaseTime slotTime
  ring

/-- Confirmation of s occurs at the support cutoff of s+1. -/
theorem confirmation_cutoff_time (Δ : Time) (s : Int) :
    phaseTime Δ s 6 = phaseTime Δ (s + 1) 2 := by
  unfold phaseTime slotTime
  ring

theorem phaseTime_strict (Δ : Time) (hΔ : 0 < Δ) (s a b : Int) (hab : a < b) :
    phaseTime Δ s a < phaseTime Δ s b := by
  unfold phaseTime
  exact Int.add_lt_add_left (mul_lt_mul_of_pos_right hab hΔ) _

/-- Every represented public phase has the unchanged Lean schedule time. -/
theorem schedule_embedding (p : Params) (s : Slot) :
    slotTime p.Δ s = SA.proposalTime p.toParams s ∧
    phaseTime p.Δ s 1 = SA.voteTime p.toParams s ∧
    phaseTime p.Δ s 2 = SA.earlyTime p.toParams s ∧
    phaseTime p.Δ s 3 = SA.freezeTime p.toParams s ∧
    phaseTime p.Δ s 5 = SA.releaseTime p.toParams s ∧
    phaseTime p.Δ s 6 = SA.gateTime p.toParams s := by
  dsimp only [slotTime, phaseTime, SA.proposalTime, SA.voteTime, SA.earlyTime,
    SA.freezeTime, SA.releaseTime, SA.gateTime, GridCO.proposalTime,
    GridCO.voteTime, GridCO.earlyTime, GridCO.freezeTime, GridCO.releaseTime,
    GridCO.gateTime, SA.Params.engine]
  simp only [one_mul, and_self]

theorem actionTime_embedding (p : Params) (r : Nat) :
    p.actionTime r = phaseTime p.Δ (r * p.R) 6 := rfl

/-- A pure composition fact, not a scheduled-run theorem. -/
theorem tick_order {σ : Type} (clock ac proposal attest : σ → σ) (state : σ) :
    tick clock ac proposal attest state = attest (proposal (ac (clock state))) := rfl

/-- A receipt and its last public tick agree at every strict public cutoff.
This covers real receipt times between integer public times, without rounding a cutoff. -/
theorem receipt_lt_public_iff (Δ : Time) (hΔ : 0 < Δ) (k m : Int) (receipt : ℝ)
    (hlo : ((k * Δ : Time) : ℝ) ≤ receipt)
    (hhi : receipt < (((k + 1) * Δ : Time) : ℝ)) :
    receipt < ((m * Δ : Time) : ℝ) ↔ k * Δ < m * Δ := by
  by_cases hkm : k < m
  · have hnext : k + 1 ≤ m := by omega
    have hbound := mul_le_mul_of_nonneg_right hnext (le_of_lt hΔ)
    exact ⟨fun _ => mul_lt_mul_of_pos_right hkm hΔ,
      fun _ => lt_of_lt_of_le hhi (Int.cast_le.mpr hbound)⟩
  · have hbound := mul_le_mul_of_nonneg_right (le_of_not_gt hkm) (le_of_lt hΔ)
    have hreceipt : ((m * Δ : Time) : ℝ) ≤ receipt := (Int.cast_le.mpr hbound).trans hlo
    exact ⟨fun h => False.elim ((not_lt_of_ge hreceipt) h),
      fun h => False.elim ((not_lt_of_ge hbound) h)⟩

/-- Resolution uses the later of the vote and block receipts. -/
theorem resolution_lt_public_iff (Δ : Time) (hΔ : 0 < Δ) (kv kb m : Int)
    (vote block : ℝ) (hv0 : ((kv * Δ : Time) : ℝ) ≤ vote)
    (hv1 : vote < (((kv + 1) * Δ : Time) : ℝ))
    (hb0 : ((kb * Δ : Time) : ℝ) ≤ block)
    (hb1 : block < (((kb + 1) * Δ : Time) : ℝ)) :
    max vote block < ((m * Δ : Time) : ℝ) ↔ max (kv * Δ) (kb * Δ) < m * Δ := by
  rw [max_lt_iff, max_lt_iff, receipt_lt_public_iff Δ hΔ kv m vote hv0 hv1,
    receipt_lt_public_iff Δ hΔ kb m block hb0 hb1]

/-- The slot-zero guard suppresses revocation, but the vote still runs. -/
theorem acOnTick_zero_vote {σ : Type} (Δ : Time)
    (expireStep : Time → σ → σ) (revoke vote confirm : Slot → σ → σ) (state : σ) :
    acOnTick Δ 0 (phaseTime Δ 0 1) expireStep revoke vote confirm state =
      vote 0 (expireStep (phaseTime Δ 0 1) state) := by
  simp [acOnTick]

/-- The slot-zero guard suppresses confirmation. -/
theorem acOnTick_zero_confirmation {σ : Type} (Δ : Time) (hΔ : 0 < Δ)
    (expireStep : Time → σ → σ) (revoke vote confirm : Slot → σ → σ) (state : σ) :
    acOnTick Δ 0 (phaseTime Δ 0 2) expireStep revoke vote confirm state =
      expireStep (phaseTime Δ 0 2) state := by
  have hne := ne_of_gt (phaseTime_strict Δ hΔ 0 1 2 (by decide))
  simp [acOnTick, hne]

/-- At vote time, expiry precedes revocation of s-1 and then the slot-s vote. -/
theorem acOnTick_vote_order {σ : Type} (Δ : Time) (hΔ : 0 < Δ)
    (s : Slot) (hs : 0 < s) (expireStep : Time → σ → σ)
    (revoke vote confirm : Slot → σ → σ) (state : σ) :
    acOnTick Δ s (phaseTime Δ s 1) expireStep revoke vote confirm state =
      vote s (revoke (s - 1) (expireStep (phaseTime Δ s 1) state)) := by
  have hne := ne_of_lt (phaseTime_strict Δ hΔ s 1 2 (by decide))
  simp [acOnTick, hs, hne]

/-- At confirmation time, the call evaluates s-1. -/
theorem acOnTick_confirmation_slot {σ : Type} (Δ : Time) (hΔ : 0 < Δ)
    (s : Slot) (hs : 0 < s) (expireStep : Time → σ → σ)
    (revoke vote confirm : Slot → σ → σ) (state : σ) :
    acOnTick Δ s (phaseTime Δ s 2) expireStep revoke vote confirm state =
      confirm (s - 1) (expireStep (phaseTime Δ s 2) state) := by
  have hne := ne_of_gt (phaseTime_strict Δ hΔ s 1 2 (by decide))
  simp [acOnTick, hs, hne]

end AvailableChain.FGSA.Spec
end
