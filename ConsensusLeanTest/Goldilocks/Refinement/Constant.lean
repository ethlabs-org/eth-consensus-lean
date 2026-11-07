module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Obligations.Constant

public section

/-! # The constant-fault headline from the certified one

(a) `goldilocksCorrectConstant_of_growing`: the certified headline `GoldilocksCorrect` (correctness
on every run, growing faults included) gives the former headline `GoldilocksCorrectConstant`
(correctness on the runs whose faults do not grow), with neither statement changed. Restricting the
valid runs only strengthens the premise of each property of the table, and adequacy and
realizability are those of the whole system in both. It pairs with
`Growing.meetsObligationsConstant_of_growing` for the endpoints. -/

namespace Consensus.Goldilocks.Obligations.Test.Constant

/-- **The certified headline gives the constant-fault headline**: `GoldilocksCorrect` implies
`GoldilocksCorrectConstant`, both unchanged. -/
theorem goldilocksCorrectConstant_of_growing (h : GoldilocksCorrect) :
    GoldilocksCorrectConstant := by
  intro S A V _ _
  obtain ⟨hb, ha, hr⟩ := h S A V
  refine ⟨?_, ha, hr⟩
  dsimp only [System.restrict, Progress.restrict]
  exact
    { laws := ⟨fun r hv => hb.laws.trace r hv.1, hb.laws.convicts_mono, hb.laws.view_mono⟩
      admissible := hb.admissible
      serves := hb.serves
      nonFraming := fun r hv => hb.nonFraming r hv.1
      nested := fun c₁ c₂ g₁ g₂ hlt h₁ h₂ r hv => hb.nested c₁ c₂ g₁ g₂ hlt h₁ h₂ r hv.1
      finalMonotone := fun g hg r hv => hb.finalMonotone g hg r hv.1
      finalAccountable := fun g hg r hv => hb.finalAccountable g hg r hv.1
      healthyLive := fun cap g hg i gst r hv => hb.healthyLive cap g hg i gst r hv.1
      sleepySafe := fun cap g hcap hg r hv => hb.sleepySafe cap g hcap hg r hv.1
      sleepyLive := fun cap g hcap hg i r hv => hb.sleepyLive cap g hcap hg i r hv.1
      healedSafe := fun cap g hcap hg i gst r hv => hb.healedSafe cap g hcap hg i gst r hv.1
      persists := fun g hg T b₀ b₁ r hv => hb.persists g hg T b₀ b₁ r hv.1 }

end Consensus.Goldilocks.Obligations.Test.Constant

end
