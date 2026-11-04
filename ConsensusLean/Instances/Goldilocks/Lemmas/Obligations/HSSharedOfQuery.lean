module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun

public section

/-! # Goldilocks Obligations: `HSSharedUpTo` from a final query (#136)

consensus-lean#136, route A. `FinalQuery.hsSharedUpTo_of_rows` supplies the shared HS premises
through the engine horizon at a parametric row delay `Δ_F`, from row service at `Δ_F`; it is the
query instance of the run-level `hsSharedUpTo_of_rows` (HSSharedRun), whose docstring lists the
source of each field. `FinalQuery.hsSharedUpTo` is its instance at the protocol row delay
`Δ_F = protoFGDelay`, with the row service of `signed_row_service_psync` there; `timeoutDelay` is
then `6Δ + Δ_F ≤ 4Δ·fgSlots ≤ 4Δ·δt` (`protoFGDelay_timeout_of_healthy`, from the healthy FG delay
bound and `3·fgSlots ≤ δt`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open SA (gbar)

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace FinalQuery

/-- **The shared HS premises of a final query at a parametric `Δ_F`**, from row service at
`Δ_F` (`hrow`), `0 < Δ_F` (only the field `ResetService.deltaF`) and `6Δ + Δ_F ≤ 4Δ·δt`. -/
theorem hsSharedUpTo_of_rows (Q : FinalQuery S A V) (ΔF : Time)
    (hrow : PSyncFGAttTransport S Q.run.2 Q.trace (honestKeys S Q.run.2) ΔF)
    (hΔF : 0 < ΔF) (htd : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      ΔF Q.run.2.horizon :=
  Obligations.hsSharedUpTo_of_rows S A V Q.run Q.hn Q.valid Q.noCollision Q.healthy hrow hΔF htd

/-- **The shared HS premises of a final query through its horizon**, at GST `Q.gst`, the
protocol row delay `Δ_F,p = protoFGDelay (pubOf E)` with the network's row service there
(`signed_row_service_psync`) and the rise timeout `protoFGDelay_timeout_of_healthy`, and the digest
of the run. This is the instantiation point of `Δ_F` for the final route. -/
theorem hsSharedUpTo (Q : FinalQuery S A V) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      (protoFGDelay (Model.pubOf Q.run.1)) Q.run.2.horizon :=
  Q.hsSharedUpTo_of_rows _ (signed_row_service_psync S Q.run.2 Q.hn Q.valid) (protoFGDelay_pos _)
    (protoFGDelay_timeout_of_healthy S A V Q.run Q.hn Q.healthy)

/-- **The row transport of a final query** at its FG gap: `6Δ + Δ_F,p ≤ 4Δ·fgSlots`. -/
theorem protoFGDelay_delivery (Q : FinalQuery S A V) :
    6 * Q.params.Δ + protoFGDelay (Model.pubOf Q.run.1) ≤ 4 * Q.params.Δ * (A.fgSlots : Time) :=
  protoFGDelay_delivery_of_healthy S A V Q.run Q.hn Q.healthy

end FinalQuery

end Consensus.Goldilocks.Obligations

end
