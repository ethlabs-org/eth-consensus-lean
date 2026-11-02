module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedRun

public section

/-! # Goldilocks Refinement: the shared HS premises of a final query at a parametric `Δ_F` (#136)

Parametric-ΔF rule (team card `two_bound_network.md` §4, fixes 1 and 2). The delivery
deadline `max(τ, w) + Δ'` is monotone in `Δ'`, so a signed row that partial synchrony
serves before the protocol deadline (`Δ' = Δ_p`) is served before every `Δ_F ≥ Δ_p`.

* `FinalQuery.hsSharedUpTo_of_le`: the shared HS premises at any `Δ_F` with `Δ ≤ Δ_F`
  and `6Δ + Δ_F ≤ 4Δ·δt`.

`ResetService.mono` and the parametric row and reset service theorems
(`signed_row_service_psync_of_le`, `resetService_of_psync_of_le`) live in `HSSharedRun`, upstream
of the query modules, with the run-level `hsSharedUpTo_of_healthy`.
The theorems in `NetworkTransport` and `HSSharedOfQuery` at `Δ_F := Δ_p` stay unchanged;
they are the instances `Δ_F := Δ_p` (`hsSharedUpTo_of_le_self`). No field of `HSSharedUpTo`
needs `Δ_F = Δ_p`: `sync.deltaF` is `Δ ≤ Δ_F`, `sync.signedRow` is monotone in `Δ_F`, and
`timeoutDelay` is the new hypothesis. -/

namespace Consensus.Goldilocks.Refinement

variable {S : Setup} {A : AcceptanceAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace FinalQuery

/-- **The shared HS premises of a final query at a parametric `Δ_F`**, for every
`Δ_F ≥ Δ` with `6Δ + Δ_F ≤ 4Δ·δt`. `hsSharedUpTo` is its instance `Δ_F := Δ`
(`hsSharedUpTo_of_le_self`); that instance is the single instantiation point of `Δ_F`. -/
theorem hsSharedUpTo_of_le (Q : FinalQuery S A V) (ΔF : Time) (hΔF : Q.params.Δ ≤ ΔF)
    (htd : 6 * Q.params.Δ + ΔF ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      ΔF Q.run.2.horizon := by
  have h := Q.hsSharedUpTo
  exact ⟨h.noColl, h.genesisRoot, h.sync.mono hΔF, h.awake, h.faults, h.noRestart, htd⟩

/-- `hsSharedUpTo` is the instance `Δ_F := Δ` of `hsSharedUpTo_of_le`. -/
theorem hsSharedUpTo_of_le_self (Q : FinalQuery S A V)
    (htd : 6 * Q.params.Δ + Q.params.Δ ≤ 4 * Q.params.Δ * (S.δt : Time)) :
    Q.hsSharedUpTo_of_le Q.params.Δ le_rfl htd = Q.hsSharedUpTo :=
  rfl

end FinalQuery

end Consensus.Goldilocks.Refinement

end
