module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model

public section

/-! # The delivery deadline is monotone in its time bound

`max(τ, w_y) + Δ'` grows with `τ`. Used by the relay arguments of the constant- and
growing-fault frame-key lags. -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- The delivery deadline is monotone in its time bound. -/
theorem deadline_mono (y : Fin P.n) (j : Nat) {τ τ' : Time} (h : τ ≤ τ') (Δ' : Time) :
    tr.deadline y j τ Δ' ≤ tr.deadline y j τ' Δ' := by
  unfold deadline
  cases tr.lastWake y j with
  | bot => exact add_le_add_left h _
  | coe w => exact add_le_add_left (max_le_max h le_rfl) _

end Consensus.Goldilocks.RunTrace

end
