module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedRun

public section

/-! # Goldilocks Refinement: `HSSharedUpTo` from a final query (#136)

consensus-lean#136, route A. `FinalQuery.hsSharedUpTo` supplies the shared HS premises of
`anchorSteps_gap2` (AnchorStepsSupply.lean) through the engine horizon, from the query data
alone: GST `Q.gst`, forwarding delay `Δ_F = Δ` (the protocol delay), horizon `rho.horizon`.
It is the instance `Δ_F := Δ` of the run-level `hsSharedUpTo_of_healthy` (HSSharedRun), whose
docstring lists the source of each field; `timeoutDelay` is `7Δ ≤ 24Δ ≤ 4Δ·δt` from `6 ≤ δt`
(`AcceptanceAssumptions.timeout`).

`FinalQuery.deltaF_le` is the premise `Δ_F ≤ 2Δ` of `anchorSteps_gap2` at `Δ_F = Δ`. -/

namespace Consensus.Goldilocks.Refinement

open SA (gbar)

variable {S : Setup} {A : AcceptanceAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace FinalQuery

/-- Every honest node is awake on `[ḡ, horizon]` (`HealthyOn`). -/
theorem awake_all (Q : FinalQuery S A V) :
    ∀ y ∈ honestKeys S Q.run.2, ∀ t, gbar Q.gst ≤ t → t ≤ Q.run.2.horizon →
      Q.trace.awake y t := by
  intro y hy t hg hb
  exact ⟨Q.healthy.2.2 (Q.run.2.key y) hy t hg hb, le_trans (le_max_right _ _) hg, hb⟩

/-- `Δ_F = Δ` satisfies the premise `Δ_F ≤ 2Δ` of `anchorSteps_gap2`. -/
theorem deltaF_le (Q : FinalQuery S A V) : Q.params.Δ ≤ 2 * Q.params.Δ := by
  have := Q.params.toParams.hΔ
  linarith

/-- **The shared HS premises of a final query through its horizon**, at GST `Q.gst`,
`Δ_F = Δ`, and the digest of the run. -/
theorem hsSharedUpTo (Q : FinalQuery S A V) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      Q.params.Δ Q.run.2.horizon :=
  hsSharedUpTo_of_healthy S A V Q.run Q.hn Q.valid Q.noCollision Q.healthy le_rfl (by
    have hΔ := Q.params.toParams.hΔ
    have h6 : (6 : Time) ≤ (S.δt : Time) := by exact_mod_cast A.timeout
    change 6 * Q.params.Δ + Q.params.Δ ≤ 4 * Q.params.Δ * (S.δt : Time)
    nlinarith)

end FinalQuery

end Consensus.Goldilocks.Refinement

end
