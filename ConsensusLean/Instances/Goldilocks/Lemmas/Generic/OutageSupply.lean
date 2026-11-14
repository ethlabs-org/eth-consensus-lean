module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineTransport

public section

/-! # Outage participation from `System.Outage`

`OutageTransport.participation_of_outage`: for every shape family, a valid run in `Outage`
satisfies the `participation` conjunct of `OutageTransport` at its own point and selected
population: the population and look-back committee η-sleepy clauses with the outage catch-up
`max cDur (η·ΔAC − 1)` and the contract's look-aheads, when the contract's participation
threshold is `1/2`. These are the participation premises of L9
(`ACCorrectLocal.outageProtected`). -/

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks

variable {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E}

/-- `System.Outage` gives the `participation` conjunct of `OutageTransport` at the run's own
point and selected population. -/
theorem OutageTransport.participation_of_outage (K : Contract ProgressReq)
    (hθ : K.params.θ = 1 / 2) :
    rho.ExecutionValid → ∀ T b₀ b₁,
    (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
    rho.point.EtaSleepyOn (1 / 2) ((K.params.η : Time) * E.ΔAC)
      (max ((Sys F V).cDur K ⟨E, rho⟩) ((K.params.η : Time) * E.ΔAC - 1))
      ((Sys F V).aheadDur K ⟨E, rho⟩) 0 rho.point.horizon ∧
    ∀ δ, 0 ≤ δ → δ ≤ (K.params.η : Time) * E.ΔAC →
      rho.point.CommitteeSleepyOn
        (fun t => (shapeProgress F V).selected E ((shapeProgress F V).ext ⟨E, rho⟩)
          (max 0 (t - δ)))
        (1 / 2) ((K.params.η : Time) * E.ΔAC)
        (max ((Sys F V).cDur K ⟨E, rho⟩) ((K.params.η : Time) * E.ΔAC - 1))
        ((Sys F V).committeeAheadDur K ⟨E, rho⟩) 0 rho.point.horizon := by
  intro _ T b₀ b₁ h
  rw [← hθ]
  exact ⟨h.2.2.1, h.2.2.2⟩

end Consensus.Goldilocks.Generic

end
