module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedRun

public section

/-! # Goldilocks Refinement: the shared HS premises of a final query at a parametric `Δ_F` (#136)

Parametric-ΔF rule (team card `two_bound_network.md` §4). `FinalQuery.hsSharedUpTo_of_le` is the
monotone lift: the network's row service at the protocol row delay `Δ_F,p`
(`signed_row_service_psync`) is row service at every `Δ_F ≥ Δ_F,p` (`PSyncFGRowTransport.mono`),
given to
`FinalQuery.hsSharedUpTo_of_rows` (HSSharedOfQuery). A consumer with row service at its own `Δ_F`
calls `hsSharedUpTo_of_rows` directly, without the lift; that core takes only `0 < Δ_F`. -/

namespace Consensus.Goldilocks.Refinement

variable {S : Setup} {A : AcceptanceAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace FinalQuery

/-- **The shared HS premises of a final query at every `Δ_F ≥ Δ_F,p`** with
`6Δ + Δ_F ≤ 4Δ·δt`, by the monotone lift of the network's row service at the protocol row delay.
`hsSharedUpTo` is its instance `Δ_F := Δ_F,p` (`hsSharedUpTo_of_le_self`). -/
theorem hsSharedUpTo_of_le (Q : FinalQuery S A V) (ΔF : Time)
    (hΔF : rowDelay (Model.pubOf Q.run.1) ≤ ΔF)
    (htd : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      ΔF Q.run.2.horizon :=
  Q.hsSharedUpTo_of_rows ΔF ((signed_row_service_psync S Q.run.2 Q.hn Q.valid).mono _ _ _ _ hΔF)
    ((rowDelay_pos _).trans_le hΔF) htd

/-- `hsSharedUpTo` is the instance `Δ_F := Δ_F,p` of `hsSharedUpTo_of_le`. -/
theorem hsSharedUpTo_of_le_self (Q : FinalQuery S A V)
    (htd : 6 * Q.params.Δ + rowDelay (Model.pubOf Q.run.1) ≤
      4 * Q.params.Δ * (S.δt : Time)) :
    Q.hsSharedUpTo_of_le _ le_rfl htd = Q.hsSharedUpTo :=
  rfl

end FinalQuery

end Consensus.Goldilocks.Refinement

end
