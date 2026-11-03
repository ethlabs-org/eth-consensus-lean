module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedRun

public section

/-! # Goldilocks Refinement: `HSSharedUpTo` from a final query (#136)

consensus-lean#136, route A. `FinalQuery.hsSharedUpTo_of_rows` supplies the shared HS premises
through the engine horizon at a parametric row delay `Δ_F`, from row service at `Δ_F`; it is the
query instance of the run-level `hsSharedUpTo_of_rows` (HSSharedRun), whose docstring lists the
source of each field. `FinalQuery.hsSharedUpTo` is its instance at the protocol row delay
`Δ_F = rowDelay`, with the row service of `signed_row_service_psync` there; `timeoutDelay` is then
`6Δ + Δ_F ≤ 4Δ·cF r ≤ 4Δ·δt` (`rowDelay_timeout_of_healthy`, from the healthy row ratio and
`3·cF r ≤ δt`). -/

namespace Consensus.Goldilocks.Refinement

open SA (gbar)

variable {S : Setup} {A : AcceptanceAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace FinalQuery

/-- **The shared HS premises of a final query at a parametric `Δ_F`**, from row service at
`Δ_F` (`hrow`), `0 < Δ_F` (only the field `ResetService.deltaF`) and `6Δ + Δ_F ≤ 4Δ·δt`. -/
theorem hsSharedUpTo_of_rows (Q : FinalQuery S A V) (ΔF : Time)
    (hrow : PSyncFGRowTransport S Q.run.2 Q.trace (honestKeys S Q.run.2) ΔF)
    (hΔF : 0 < ΔF) (htd : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      ΔF Q.run.2.horizon :=
  Refinement.hsSharedUpTo_of_rows S A V Q.run Q.hn Q.valid Q.noCollision Q.healthy hrow hΔF htd

/-- **The shared HS premises of a final query through its horizon**, at GST `Q.gst`, the
protocol row delay `Δ_F,p = rowDelay (pubOf E)` with the network's row service there
(`signed_row_service_psync`) and the rise timeout `rowDelay_timeout_of_healthy`, and the digest
of the run. This is the instantiation point of `Δ_F` for the final route. -/
theorem hsSharedUpTo (Q : FinalQuery S A V) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      (rowDelay (Model.pubOf Q.run.1)) Q.run.2.horizon :=
  Q.hsSharedUpTo_of_rows _ (signed_row_service_psync S Q.run.2 Q.hn Q.valid) (rowDelay_pos _)
    (rowDelay_timeout_of_healthy S A V Q.run Q.hn Q.healthy)

/-- **The row transport of a final query** at its row gap: `6Δ + Δ_F,p ≤ 4Δ·cF r`. -/
theorem rowDelay_delivery (Q : FinalQuery S A V) :
    6 * Q.params.Δ + rowDelay (Model.pubOf Q.run.1) ≤ 4 * Q.params.Δ * (cF A.rowRatio : Time) :=
  rowDelay_delivery_of_healthy S A V Q.run Q.hn Q.healthy

end FinalQuery

end Consensus.Goldilocks.Refinement

end
