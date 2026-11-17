module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.FamilyIdentity

/-! # The Goldilocks identity observation -/

public section

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

theorem projCall_goldilocks (c : (goldilocksSA sp FGP ro).Call) :
    (goldilocksFamily sp FGP ro).projCall c = some c := by cases c <;> rfl

theorem projLabel_goldilocks (ℓ : ACLabel (goldilocksSA sp FGP ro)) :
    (goldilocksFamily sp FGP ro).projLabel ℓ = some ℓ := by
  cases ℓ with
  | mk c Φ es =>
    simp only [SAFamily.projLabel, projCall_goldilocks, Option.map_some]
    have hem : es.filterMap (goldilocksFamily sp FGP ro).projEm = es := by
      induction es with
      | nil => rfl
      | cons e es ih =>
        change e :: es.filterMap (goldilocksFamily sp FGP ro).projEm = e :: es
        rw [ih]
    rw [hem]

theorem proj_goldilocks (tr : SATrace sp FGP ro) :
    (goldilocksFamily sp FGP ro).proj tr = tr := by
  have hl : (fun i => (tr.label i).bind (goldilocksFamily sp FGP ro).projLabel) = tr.label := by
    funext i
    cases h : tr.label i with
    | none => rfl
    | some ℓ => exact projLabel_goldilocks ℓ
  change { tr with init := fun y => tr.init y, label := _, post := fun i => tr.post i } = tr
  exact congrArg (fun labels => { tr with label := labels }) hl

end Consensus.Goldilocks.SA

end
