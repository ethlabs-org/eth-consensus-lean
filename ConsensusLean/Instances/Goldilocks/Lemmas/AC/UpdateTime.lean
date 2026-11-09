module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Schedule
public import Mathlib.Tactic.Ring

public section

/-! # The time of a slot's update

`ac_on_tick` runs the update of slot `slot(t) − 1` at `t = t_{slot(t)} + 2Δ` when `slot(t) > 0`
(`acOnTickWith`, `acOnTickWithM`); `tickCond_time` restates that time in terms of the updated
slot: `t_{s} + 6Δ` for `s = slot(t) − 1`. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams}

/-- The update condition of a tick at `t`: at `t_{s+1} + 2Δ` with `s + 1 = slot(t) > 0`, that is
at `t_s + 6Δ`, the time of the update of `s`. -/
theorem tickCond_time {t : Time} (h : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) :
    t = sp.ts ((sp.slot t - 1 : Nat) : Int) + 6 * sp.Δ := by
  have h1 : ((sp.slot t - 1 : Nat) : Int) = (sp.slot t : Int) - 1 := by omega
  rw [h1]
  conv_lhs => rw [h.1]
  simp only [SAParams.ts]; ring

end Consensus.Goldilocks.SA

end
