module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedRun

public section

/-! # Goldilocks Refinement: the shared HS premises of a final query at a parametric `Δ_F` (#136)

Parametric-ΔF rule (team card `two_bound_network.md` §4). `FinalQuery.hsSharedUpTo_of_le` is the
monotone lift: the network's row service at `Δ_p` (`signed_row_service_psync`, the single
instantiation point of `Δ_F`) is row service at every `Δ_F ≥ Δ_p` (`PSyncFGRowTransport.mono`),
given to `FinalQuery.hsSharedUpTo_of_rows` (HSSharedOfQuery). A consumer with row service at its
own `Δ_F` calls `hsSharedUpTo_of_rows` directly, without the lift; that core still takes
`Δ_p ≤ Δ_F`, only to fill the field `ResetService.deltaF`, until the two-bound integration
changes that field. -/

namespace Consensus.Goldilocks.Refinement

variable {S : Setup} {A : AcceptanceAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace FinalQuery

/-- **The shared HS premises of a final query at every `Δ_F ≥ Δ`** with `6Δ + Δ_F ≤ 4Δ·δt`, by the
monotone lift of the row service at `Δ_p`. `hsSharedUpTo` is its instance `Δ_F := Δ`
(`hsSharedUpTo_of_le_self`). -/
theorem hsSharedUpTo_of_le (Q : FinalQuery S A V) (ΔF : Time) (hΔF : Q.params.Δ ≤ ΔF)
    (htd : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      ΔF Q.run.2.horizon :=
  Q.hsSharedUpTo_of_rows ΔF ((signed_row_service_psync S Q.run.2 Q.hn Q.valid).mono _ _ _ _ hΔF)
    hΔF htd

/-- `hsSharedUpTo` is the instance `Δ_F := Δ` of `hsSharedUpTo_of_le`. -/
theorem hsSharedUpTo_of_le_self (Q : FinalQuery S A V)
    (htd : 6 * Q.params.Δ + Q.params.Δ ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Q.hsSharedUpTo_of_le Q.params.Δ le_rfl htd = Q.hsSharedUpTo :=
  rfl

end FinalQuery

end Consensus.Goldilocks.Refinement

end
