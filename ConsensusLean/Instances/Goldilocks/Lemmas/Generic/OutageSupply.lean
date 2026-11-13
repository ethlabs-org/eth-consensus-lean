module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineTransport

public section

/-! # Outage participation from `System.Outage`

`OutageTransport.participation_of_outage`: for every shape family, a valid run in `Outage`
satisfies the `participation` conjunct of `OutageTransport` at its own point and selected
population, at the `System.Outage` endpoints (`outageStart`, `outageEnd`, `cohortAt`,
`bandStart`, `bandEnd`), with the contract's catch-up and look-aheads, when the contract's
participation threshold is `1/2`. These are the participation premises of L9
(`ACCorrectLocal.outageProtected`). -/

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks

variable {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E}

/-- `System.Outage` gives the `participation` conjunct of `OutageTransport` at the run's own
point and selected population, at the `System.Outage` endpoints. -/
theorem OutageTransport.participation_of_outage (K : Contract ProgressReq)
    (hθ : K.params.θ = 1 / 2) :
    rho.ExecutionValid → ∀ T b₀ b₁,
    (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
    rho.point.EtaSleepyOn (1 / 2) ((K.params.η : Time) * E.ΔAC) ((Sys F V).cDur K ⟨E, rho⟩)
      ((Sys F V).aheadDur K ⟨E, rho⟩) 0 rho.point.horizon ∧
    (rho.point.retain ((Sys F V).cohortAt K b₁ ⟨E, rho⟩)).NoSleepOn
      ((Sys F V).outageStart K b₀ ⟨E, rho⟩) ((Sys F V).outageEnd K b₁ ⟨E, rho⟩) ∧
    (rho.point.retain ((Sys F V).cohortAt K b₁ ⟨E, rho⟩)).CohortOn
      ((Sys F V).outageStart K b₀ ⟨E, rho⟩) ((Sys F V).outageEnd K b₁ ⟨E, rho⟩) ∧
    rho.point.CommitteeSleepyOn ((shapeProgress F V).selected E ((shapeProgress F V).ext ⟨E, rho⟩))
      (1 / 2) ((K.params.η : Time) * E.ΔAC) ((Sys F V).cDur K ⟨E, rho⟩)
      ((Sys F V).committeeAheadDur K ⟨E, rho⟩) 0 rho.point.horizon ∧
    (rho.point.retain ((Sys F V).cohortAt K b₁ ⟨E, rho⟩)).CommitteeCohortOn
      ((shapeProgress F V).selected E ((shapeProgress F V).ext ⟨E, rho⟩))
      ((Sys F V).outageStart K b₀ ⟨E, rho⟩) ((Sys F V).outageEnd K b₁ ⟨E, rho⟩)
      ((Sys F V).bandStart K b₀ ⟨E, rho⟩) ((Sys F V).bandEnd K b₀ ⟨E, rho⟩) := by
  intro _ T b₀ b₁ h
  rw [← hθ]
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2, h.2.2.2.2.2.1⟩

end Consensus.Goldilocks.Generic

end
