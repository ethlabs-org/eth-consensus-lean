module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HSSharedOfQuery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport

public section

/-! # Goldilocks Refinement: row service at a parametric `Δ_F` (#136)

Parametric-ΔF rule (team card `two_bound_network.md` §4, fixes 1 and 2). The delivery
deadline `max(τ, w) + Δ'` is monotone in `Δ'`, so a signed row that partial synchrony
serves before the protocol deadline (`Δ' = Δ_p`) is served before every `Δ_F ≥ Δ_p`.

* `ResetService.mono`: `ResetService` at `Δ₁` gives it at every `Δ₂ ≥ Δ₁`.
* `signed_row_service_psync_of_le`, `resetService_of_psync_of_le`: the partial-synchrony
  row service and reset service at any `Δ_F` with `Δ_p ≤ Δ_F`.
* `FinalQuery.hsSharedUpTo_of_le`: the shared HS premises at any `Δ_F` with `Δ ≤ Δ_F`
  and `6Δ + Δ_F ≤ 4Δ·δt`.

The theorems in `NetworkTransport` and `HSSharedOfQuery` at `Δ_F := Δ_p` stay unchanged;
they are the instances `Δ_F := Δ_p` (`hsSharedUpTo_of_le_self`). No field of `HSSharedUpTo`
needs `Δ_F = Δ_p`: `sync.deltaF` is `Δ ≤ Δ_F`, `sync.signedRow` is monotone in `Δ_F`, and
`timeoutDelay` is the new hypothesis. -/

namespace Consensus.Goldilocks

namespace RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- The delivery deadline is monotone in its delivery parameter. -/
theorem deadline_mono_delta (y : Fin P.n) (k : Nat) (τ : Time) {Δ₁ Δ₂ : Time}
    (h : Δ₁ ≤ Δ₂) : tr.deadline y k τ Δ₁ ≤ tr.deadline y k τ Δ₂ := by
  unfold deadline
  linarith

end RunTrace

namespace Healing

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

/-- Reset service at `Δ₁` is reset service at every `Δ₂ ≥ Δ₁`: only the signed-row field
uses the parameter, and its deadline is monotone in it. -/
theorem ResetService.mono {g Δ₁ Δ₂ b : Time} (h : ResetService tr H g Δ₁ b)
    (h12 : Δ₁ ≤ Δ₂) : ResetService tr H g Δ₂ b := by
  refine ⟨h.deltaF.trans h12, h.message, h.block, h.relay, ?_⟩
  intro x hx i att hs y hy j hj hb hd
  obtain ⟨k, hkj, hp, ht⟩ := h.signedRow x hx i att hs y hy j hj hb
    ((tr.deadline_mono_delta y j _ h12).trans hd)
  exact ⟨k, hkj, hp, ht.trans_le (tr.deadline_mono_delta y k _ h12)⟩

end Healing

namespace Refinement

open Shape Blocks

section

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (family S)) E)

/-- Partial synchrony serves signed rows before the deadline at every `Δ_F ≥ Δ_p`. At
`Δ_F := Δ_p` this is `signed_row_service_psync`. -/
theorem signed_row_service_psync_of_le (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {ΔF : Time} (hΔF : (S.params (Model.pubOf E) hn).Δ ≤ ΔF) :
    ∀ g, rho.log.PSync rho.point g →
      ∀ x ∈ honestKeys S rho, ∀ i a, (simTrace S rho hn).SignAt x i a →
        ∀ y ∈ honestKeys S rho, ∀ j, (simTrace S rho hn).IsCall y j →
          (simTrace S rho hn).time j ≤ rho.horizon →
          (simTrace S rho hn).deadline y j (max ((simTrace S rho hn).time i) g) ΔF ≤
            (simTrace S rho hn).time j →
          ∃ k ≤ j, (simTrace S rho hn).ProcessAttAt y k a ∧
            (simTrace S rho hn).time k <
              (simTrace S rho hn).deadline y k (max ((simTrace S rho hn).time i) g) ΔF := by
  intro g hnet x hx i a hs y hy j hj hb hd
  obtain ⟨k, hkj, hp, ht⟩ := (psyncFGRowTransport_iff S rho _ _).mp
    (signed_row_service_psync S rho hn hv) g hnet x hx i a hs y hy j hj hb
    (((simTrace S rho hn).deadline_mono_delta y j _ hΔF).trans hd)
  exact ⟨k, hkj, hp, ht.trans_le ((simTrace S rho hn).deadline_mono_delta y k _ hΔF)⟩

/-- The finite valid engine run supplies every reset-service field at every `Δ_F ≥ Δ_p`.
At `Δ_F := Δ_p` this is `resetService_of_psync`. -/
theorem resetService_of_psync_of_le (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTrace S rho hn))
    {g : Time} (hnet : rho.log.PSync rho.point g)
    {ΔF : Time} (hΔF : (S.params (Model.pubOf E) hn).Δ ≤ ΔF) :
    Healing.ResetService (simTrace S rho hn) (honestKeys S rho) g ΔF rho.horizon :=
  (resetService_of_psync S rho hn hv hnc hnet).mono hΔF

end

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

end Refinement

end Consensus.Goldilocks

end
