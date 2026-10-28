module
public import ConsensusModel.System
public import Mathlib.Tactic
@[expose] public section

namespace Consensus.Shape.Tests
open Consensus

/-- A legal L0 environment point whose sleepy time window is empty. -/
def negativeHorizonPoint : EnvPoint (Fin 2) where
  env := ⟨1, by decide, 0, fun _ _ => true⟩
  honest := {0}
  horizon := -1
  submit := fun _ _ => []

/-- Every proposed sleepy threshold passes on this point, regardless of its
parameter domain. The environment has a genuine faulty validator. -/
theorem negativeHorizon_sleepy (θ : ℚ) (c : Time) :
    negativeHorizonPoint.env.gst = 0 ∧
    negativeHorizonPoint.faulty.Nonempty ∧
    ∀ t, 0 ≤ t → t ≤ negativeHorizonPoint.horizon →
      θ * ((negativeHorizonPoint.readyAt c t).card +
        negativeHorizonPoint.faulty.card : ℚ) <
        (negativeHorizonPoint.readyAt c t).card := by
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨1, by decide⟩
  · intro t ht hh
    change t ≤ -1 at hh
    simp only [Time] at *
    omega

/-- No execution profile containing validity can conservatively cover this
point: validity already contradicts its horizon, before synchrony or shape. -/
theorem negativeHorizon_not_covered (F : Model.Family) :
    ¬ ∃ r : (Model.sysOf F (Fin 2)).Run,
      ((Model.sysOf F (Fin 2)).trace r).point = negativeHorizonPoint ∧
      (Model.sysOf F (Fin 2)).Valid r := by
  rintro ⟨r, hp, hv⟩
  have hh := hv.horizon_nonneg
  have he := congrArg EnvPoint.horizon hp
  change r.2.horizon = -1 at he
  simp only [Time] at *
  omega

#print axioms negativeHorizon_sleepy
#print axioms negativeHorizon_not_covered
end Consensus.Shape.Tests
end
