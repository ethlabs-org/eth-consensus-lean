module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedRun

public section

/-! # Goldilocks Refinement: `HSSharedUpTo` from a final query (#136)

consensus-lean#136, route A. `FinalQuery.hsSharedUpTo_of_rows` supplies the shared HS premises
through the engine horizon at a parametric row delay `Δ_F`, from row service at `Δ_F`; it is the
query instance of the run-level `hsSharedUpTo_of_rows` (HSSharedRun), whose docstring lists the
source of each field. `FinalQuery.hsSharedUpTo` is its instance at `Δ_F = Δ`, with the row service
of `signed_row_service_psync`; `timeoutDelay` is then `7Δ ≤ 24Δ ≤ 4Δ·δt` from `6 ≤ δt`
(`AcceptanceAssumptions.timeout`). -/

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

/-- **The shared HS premises of a final query at a parametric `Δ_F`**, from row service at
`Δ_F` (`hrow`), `Δ ≤ Δ_F` (only the field `ResetService.deltaF`) and `6Δ + Δ_F ≤ 4Δ·δt`. -/
theorem hsSharedUpTo_of_rows (Q : FinalQuery S A V) (ΔF : Time)
    (hrow : PSyncFGRowTransport S Q.run.2 Q.trace (honestKeys S Q.run.2) ΔF)
    (hΔF : Q.params.Δ ≤ ΔF) (htd : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      ΔF Q.run.2.horizon :=
  Refinement.hsSharedUpTo_of_rows S A V Q.run Q.hn Q.valid Q.noCollision Q.healthy hrow hΔF htd

/-- **The shared HS premises of a final query through its horizon**, at GST `Q.gst`,
`Δ_F = Δ` with the network's row service at `Δ_p` (`signed_row_service_psync`), and the digest
of the run. -/
theorem hsSharedUpTo (Q : FinalQuery S A V) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      Q.params.Δ Q.run.2.horizon :=
  Q.hsSharedUpTo_of_rows _ (signed_row_service_psync S Q.run.2 Q.hn Q.valid) le_rfl (by
    have hΔ := Q.params.toParams.hΔ
    have h6 : (6 : Time) ≤ (S.δt : Time) := by exact_mod_cast A.timeout
    change 6 * Q.params.Δ + Q.params.Δ ≤ 4 * Q.params.Δ * (S.δt : Time)
    nlinarith)

end FinalQuery

end Consensus.Goldilocks.Refinement

end
