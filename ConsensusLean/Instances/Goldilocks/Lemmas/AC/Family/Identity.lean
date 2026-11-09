module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.FamilyIdentity

/-! # The Goldilocks identity observation -/

public section

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

theorem projEm_goldilocks (e : Em sp FGP) :
    (goldilocksFamily sp FGP ro).projEm e = some e := by cases e; rfl

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

theorem goldilocksObservationAgreement (H : Set (Fin sp.n)) (tr : SATrace sp FGP ro) :
    ObservationAgreement (goldilocksFamily sp FGP ro) H tr := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy i; rw [proj_goldilocks]; rfl
  · intro y hy i ℓ hc he
    have h := projCall_goldilocks (sp := sp) (ro := ro) ℓ.call
    exact False.elim (Option.some_ne_none _ (h.symm.trans he))
  · intro y hy i ℓ hc he
    have h := projCall_goldilocks (sp := sp) (ro := ro) ℓ.call
    exact False.elim (Option.some_ne_none _ (h.symm.trans he))

theorem goldilocksObservation {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    {tr : SATrace sp FGP ro} (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) :
    ACObsRun (goldilocksSA sp FGP ro) H U ((goldilocksFamily sp FGP ro).proj tr) := by
  rw [proj_goldilocks]
  exact ⟨hr.coherent, hr.init, hr.frameLaw, hr.time_nonneg, hr.time_mono,
    hr.awake_of_call, hr.restart_of_sleep, hr.restart_at_wake, hr.sleep_of_restart⟩

theorem goldilocksOutputAgreement (H : Set (Fin sp.n)) (tr : SATrace sp FGP ro) :
    OutputAgreement (goldilocksFamily sp FGP ro) H tr := by
  constructor
  · intro x hx i ℓ C h
    exact ⟨tr.state x i, by rw [proj_goldilocks]; rfl, rfl, h.2.2⟩
  · intro x hx i ℓ d p h
    exact ⟨tr.state x i, by rw [proj_goldilocks]; rfl, rfl, h.2.2⟩

end Consensus.Goldilocks.SA

end
