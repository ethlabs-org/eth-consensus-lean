module
public import AvailableChainFGSA.Proofs.Fields -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA

open AvailableChain.Generic

/-- [Sleep v6; plan §14.3] The initial epoch permits duties. -/
theorem joinedNow_none (p : Params) (st : State p.n) (h : st.restartTime = none) :
    joinedNow p st = true := by
  unfold joinedNow
  rw [h]
  rfl

/-- [Sleep v6; plan §14.3] The exact inclusive join boundary. -/
theorem joinedNow_iff (p : Params) (st : State p.n) (w : Time)
    (h : st.restartTime = some w) :
    joinedNow p st = true ↔ w ≤ 4 * p.Δ * ((p.slotOf st.base.now : Int) - 1) := by
  unfold joinedNow
  rw [h]
  change decide (w ≤ 4 * p.Δ * ((p.slotOf st.base.now : Int) - 1)) = true ↔ _
  simp only [decide_eq_true_eq]

/-- [Sleep v6; plan §14.3] Slot zero tests the negative previous-slot start. -/
theorem joinedNow_slot_zero (p : Params) (st : State p.n) (w : Time)
    (h : st.restartTime = some w) (hs : p.slotOf st.base.now = 0) :
    joinedNow p st = true ↔ w ≤ -(4 * p.Δ) := by
  rw [joinedNow_iff p st w h, hs]
  simp

/-- [Sleep v6; plan §14.3] The pre-gate tick sets time and keeps the restart marker. -/
theorem clockPre_joined (p : Params) (st : State p.n) (t : Time) :
    joinedNow p (clockPre p st t) = joinedAtTime p st.restartTime t := by
  unfold clockPre joinedNow
  dsimp only
  split_ifs <;> rfl

/-- [Sleep v6; plan §14.3] An unjoined pre-gate tick only expires leases. -/
theorem clockPre_obligations_unjoined (p : Params) (st : State p.n) (t : Time)
    (hj : joinedNow p { st with base := GridCO.expire { st.base with now := t } t } = false) :
    (clockPre p st t).base.obligations =
      (GridCO.expire { st.base with now := t } t).obligations := by
  change joinedAtTime p st.restartTime t = false at hj
  unfold clockPre
  dsimp only
  split_ifs with hf he hr
  all_goals try rfl
  all_goals dsimp only [joinedNow, onView, actView, GridCO.freeze, GridCO.expire] at *
  all_goals simp_all only [Bool.and_false, Bool.false_eq_true]

end AvailableChain.FGSA
end
