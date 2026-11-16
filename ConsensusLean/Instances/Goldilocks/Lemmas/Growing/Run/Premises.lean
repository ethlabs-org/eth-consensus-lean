module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Premises

public section

/-! # Growing-fault premises: monotonicity

* `FaultBoundAt.mono_right`: a count charged at a later horizon is a stronger premise (the honest
  set only shrinks). -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Time → Set (Fin P.n)}

/-- **The count is antitone in its horizon.** -/
theorem FaultBoundAt.mono_right (hanti : Antitone H) {t d d' : Time} (hd : d' ≤ d)
    (h : tr.FaultBoundAt H t d) : tr.FaultBoundAt H t d' := by
  have hsub : H d ⊆ H d' := hanti hd
  calc (H d')ᶜ.ncard ≤ (H d)ᶜ.ncard :=
        Set.ncard_le_ncard (Set.compl_subset_compl.mpr hsub) (Set.toFinite _)
    _ < {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard := h
    _ ≤ {y | y ∈ H d' ∧ tr.awake y t ∧ tr.JoinedAt y t}.ncard :=
        Set.ncard_le_ncard (fun y hy => ⟨hsub hy.1, hy.2⟩) (Set.toFinite _)

end Consensus.Goldilocks.RunTrace

end
