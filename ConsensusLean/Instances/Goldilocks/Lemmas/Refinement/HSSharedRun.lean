module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport

public section

/-! # Goldilocks Refinement: `HSSharedUpTo` from a healthy run, at a parametric `Δ_F` (#136)

The shared HS premises through the engine horizon, from the run data of a query alone (valid
execution, no observed collision, `Healthy` at GST `g`), at every `Δ_F ≥ Δ_p` with
`6Δ + Δ_F ≤ 4Δ·δt`. The query wrappers are thin instances: `FinalQuery.hsSharedUpTo`
(HSSharedOfQuery, `Δ_F := Δ`), `FinalQuery.hsSharedUpTo_of_le` (RowServiceParam) and
`HealthyPreparationQuery.hsSharedUpTo_of_le` (HealthyQueryShared). This module stays upstream
of `FinalWindowDefs` and `HealedSafety`.

* `noColl`, `genesisRoot`: `noCollTransport` and `simTrace_genesis_root_ok`.
* `sync`: `resetService_of_psync_of_le` at `PSync g` (from `Healthy`).
* `awake`: `HealthyOn`.
* `faults`: `|faulty| < n/3` (from `HealthyOn`, `β = 1/3`).
* `noRestart`: a restart at `t` has its node asleep at `t - 1` (`simTrace_asleep_before_restart`),
  so it is not after `ḡ`.
* `timeoutDelay`: the hypothesis `6Δ + Δ_F ≤ 4Δ·δt`.

`ResetService.mono` and the parametric row/reset service theorems moved here unchanged from
`RowServiceParam`. -/

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

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The shared HS premises of a healthy run through its horizon**, at GST `g`, every
`Δ_F ≥ Δ` with `6Δ + Δ_F ≤ 4Δ·δt`, and the digest of the run. Only the run data of a query
are used: valid execution, no observed collision and `Healthy` at `g`. -/
theorem hsSharedUpTo_of_healthy (run : (Sys (family S) V).Run) (hn : 1 ≤ Fintype.card V)
    (valid : (Sys (family S) V).Valid run) (noCollision : ¬ run.2.HashCollision) {g : Time}
    (healthy : (Sys (family S) V).Healthy (K S A) g run) {ΔF : Time}
    (hΔF : (S.params (Model.pubOf run.1) hn).Δ ≤ ΔF)
    (htd : 6 * (S.params (Model.pubOf run.1) hn).Δ + ΔF ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo (simTrace S run.2 hn) (honestKeys S run.2) (digestOf S run.2) g
      ΔF run.2.horizon := by
  have hnc := noCollTransport V S run.1 run.2 hn valid noCollision
  have hnet : run.2.log.PSync run.2.point g := by
    constructor
    · intro v hv o s hs w hw a hsa hc hh haw
      have h := healthy.1.msgs v hv ⟨run.1, o⟩ s ⟨o, rfl, hs⟩ w hw a hsa hc hh haw
      rcases h with ⟨u, hu, hsent | hrecv, hnowake⟩
      · obtain ⟨o', he, hs'⟩ := hsent
        cases he
        exact ⟨u, hu, Or.inl hs', hnowake⟩
      · obtain ⟨o', he, hr'⟩ := hrecv
        cases he
        exact ⟨u, hu, Or.inr hr', hnowake⟩
    · exact healthy.1.txs
  have hawake : ∀ y ∈ honestKeys S run.2, ∀ t, SA.gbar g ≤ t → t ≤ run.2.horizon →
      (simTrace S run.2 hn).awake y t := fun y hy t hg hb =>
    ⟨healthy.2.2 (run.2.key y) hy t hg hb, le_trans (le_max_right _ _) hg, hb⟩
  refine ⟨hnc, simTrace_genesis_root_ok S run.2 hn,
    resetService_of_psync_of_le S run.2 hn valid hnc hnet hΔF, hawake, ?_, ?_, htd⟩
  · have hpop := healthy.2.1
    change (run.2.point.faulty.card : ℚ) < (K S A).params.β * Fintype.card V at hpop
    rw [acceptanceContract_params_eq] at hpop
    change (run.2.point.faulty.card : ℚ) < 1 / 3 * Fintype.card V at hpop
    have hfault : (honestKeys S run.2)ᶜ.ncard = run.2.point.faulty.card := by
      have heq : (honestKeys S run.2)ᶜ = run.2.key ⁻¹' (↑run.2.point.faulty : Set V) := by
        ext k; simp [honestKeys, EnvPoint.faulty, Model.Run.point]
      rw [heq, Set.ncard_preimage_of_injective_subset_range run.2.key.injective
        (by simp [run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
    change 3 * (honestKeys S run.2)ᶜ.ncard ≤ Fintype.card V - 1
    rw [hfault]
    have hn3 : 3 * run.2.point.faulty.card < Fintype.card V := by
      exact_mod_cast (show (3 : ℚ) * run.2.point.faulty.card < Fintype.card V by linarith)
    omega
  · intro y hy k hk hkb
    by_contra hlt
    rw [not_le] at hlt
    exact simTrace_asleep_before_restart S run.2 hn valid y hy k hk
      (hawake y hy _ (Int.le_sub_one_of_lt hlt) (by linarith))

end Refinement

end Consensus.Goldilocks

end
