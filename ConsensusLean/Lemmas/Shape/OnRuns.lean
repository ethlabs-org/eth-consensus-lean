module
public import ConsensusLean.Spec.Shape.OnRuns

public section

/-! # Shape obligations restricted to a class of runs (L2)

The shape claims of every run hold on every class of runs: `ShapeClaimsAt.onAt` restricts each
field to the runs whose point satisfies `Q` (a stronger premise), and `ShapeObligations.toOn`,
`ShapeObligationsAs.toOnAs` do the same for the obligations. In particular the obligations on all
runs give the obligations on the constant-fault runs. -/

namespace Consensus.Shape

open Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {K : Contract ProgressReq}

/-- The shape claims of every run restrict to the runs whose point satisfies `Q`. -/
theorem ShapeClaimsAt.onAt {V : Type} [Fintype V] [DecidableEq V] (h : ShapeClaimsAt F K V)
    (Q : EnvPoint V → Prop) : ShapeClaimsOnAt F K V Q where
  outputValid := fun r hv _ => h.outputValid r hv
  nested := fun c₁ c₂ g₁ g₂ hr h₁ h₂ r hv _ => h.nested c₁ c₂ g₁ g₂ hr h₁ h₂ r hv
  finalMonotone := fun g hg r hv _ => h.finalMonotone g hg r hv
  finalAccountable := fun g hg r hv _ => h.finalAccountable g hg r hv trivial
  healthyLive := fun cap g hg i gst r hv hp => h.healthyLive cap g hg i gst r hv hp.2
  sleepySafe := fun cap g hcap hg r hv hp => h.sleepySafe cap g hcap hg r hv hp.2
  sleepyLive := fun cap g hcap hg i r hv hp => h.sleepyLive cap g hcap hg i r hv hp.2
  healedSafe := fun cap g hcap hg i gst r hv hp => h.healedSafe cap g hcap hg i gst r hv hp.2
  persists := fun g hg T b₀ b₁ r hv hp => h.persists g hg T b₀ b₁ r hv hp.2

/-- The shape obligations restrict to every class of runs. -/
theorem ShapeObligations.toOn (h : ShapeObligations F K) (Q : ∀ V : Type, EnvPoint V → Prop) :
    ShapeObligationsOn F K Q where
  claims := fun V _ _ => (h.claims V).onAt (Q V)
  admissible := h.admissible
  serves := h.serves
  progressFits := h.progressFits
  progressTolerant := h.progressTolerant

/-- The shape obligations under a profile label restrict to every class of runs. -/
theorem ShapeObligationsAs.toOnAs {p : Profile} (h : ShapeObligationsAs p F K)
    (Q : ∀ V : Type, EnvPoint V → Prop) : ShapeObligationsOnAs p F K Q :=
  ⟨h.1, h.2.toOn Q⟩

end Consensus.Shape

end
