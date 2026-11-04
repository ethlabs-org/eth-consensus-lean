module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun

public section

/-! # Goldilocks Obligations: `HSSharedUpTo` from a Healthy preparation query (#136)

`HealthyPreparationQuery.hsSharedUpTo_of_le`: the shared HS premises of a Healthy preparation
query through the engine horizon, at every `Δ_F ≥ Δ_F,p` (the protocol FG delay `protoFGDelay`)
with `6Δ + Δ_F ≤ 4Δ·δt`. It is the
instance of the run-level `hsSharedUpTo_of_healthy` (HSSharedRun) at the query's run data;
`Δ_F` and the timeout delay stay hypotheses. This module stays upstream of `FinalWindowDefs`
and `HealedSafety`, so the nonfinal reset envelope can use it. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **The shared HS premises of a Healthy preparation query at a parametric `Δ_F`**, for every
`Δ_F ≥ Δ_F,p` with `6Δ + Δ_F ≤ 4Δ·δt`, at GST `Q.gst` and the digest of the run. -/
theorem HealthyPreparationQuery.hsSharedUpTo_of_le (Q : HealthyPreparationQuery S A V)
    (ΔF : Time) (hΔF : protoFGDelay (Model.pubOf Q.run.1) ≤ ΔF)
    (htd : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      ΔF Q.run.2.horizon :=
  hsSharedUpTo_of_healthy S A V Q.run Q.hn Q.valid Q.noCollision Q.healthy hΔF htd

end Consensus.Goldilocks.Obligations

end
