module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.FamilyIdentity

/-! # The Goldilocks identity observation -/

public section

namespace Consensus.Goldilocks.AC

variable {sp : ACParams} {FGP : Type} {ro : ReplayOrder sp FGP}

theorem projCall_goldilocks (c : (goldilocksAC sp FGP ro).Call) :
    (goldilocksFamily sp FGP ro).projCall c = some c := by cases c <;> rfl

theorem projLabel_goldilocks (ℓ : ACLabel (goldilocksAC sp FGP ro)) :
    (goldilocksFamily sp FGP ro).projLabel ℓ = some ℓ := by
  cases ℓ with
  | mk c Φ es =>
    simp only [ACFamily.projLabel, projCall_goldilocks, Option.map_some]
    have hem : es.filterMap (goldilocksFamily sp FGP ro).projEm = es := by
      induction es with
      | nil => rfl
      | cons e es ih =>
        change e :: es.filterMap (goldilocksFamily sp FGP ro).projEm = e :: es
        rw [ih]
    rw [hem]

theorem proj_goldilocks (tr : GTrace sp FGP ro) :
    (goldilocksFamily sp FGP ro).proj tr = tr := by
  have hl : (fun i => (tr.label i).bind (goldilocksFamily sp FGP ro).projLabel) = tr.label := by
    funext i
    cases h : tr.label i with
    | none => rfl
    | some ℓ => exact projLabel_goldilocks ℓ
  change { tr with init := fun y => tr.init y, label := _, post := fun i => tr.post i } = tr
  exact congrArg (fun labels => { tr with label := labels }) hl

end Consensus.Goldilocks.AC

end
