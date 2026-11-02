module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport

public section

/-! # Goldilocks Refinement: `HSSharedUpTo` from a healthy run, at a parametric `Δ_F` (#136)

The shared HS premises through the engine horizon, from the run data of a query alone (valid
execution, no observed collision, `Healthy` at GST `g`), at a parametric row delay `Δ_F`.

* `hsSharedUpTo_of_rows`: from row service at `Δ_F` (`PSyncFGRowTransport … Δ_F`) as a premise.
* `hsSharedUpTo_of_healthy`: the monotone lift, at every `Δ_F ≥ Δ_p`, from the row service at
  `Δ_p` of the single-bound network (`signed_row_service_psync`, the single instantiation point of
  `Δ_F`).

Fields: `noColl`, `genesisRoot` (`noCollTransport`, `simTrace_genesis_root_ok`); `sync`
(`resetService_of_psync` at `PSync g`, from `Healthy`, with the row service); `awake`
(`HealthyOn`); `faults` (`|faulty| < n/3`, `β = 1/3`); `noRestart` (a restart at `t` has its node
asleep at `t - 1`, `simTrace_asleep_before_restart`); `timeoutDelay` (the hypothesis
`6Δ + Δ_F ≤ 4Δ·δt`). The query wrappers are thin instances: `FinalQuery.hsSharedUpTo` and
`FinalQuery.hsSharedUpTo_of_rows` (HSSharedOfQuery), `FinalQuery.hsSharedUpTo_of_le`
(RowServiceParam) and `HealthyPreparationQuery.hsSharedUpTo_of_le` (HealthyQueryShared). This
module stays upstream of `FinalWindowDefs` and `HealedSafety`. -/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The shared HS premises of a healthy run through its horizon, from row service at `Δ_F`**,
at GST `g` and the digest of the run. Only the run data of a query are used (valid execution, no
observed collision, `Healthy` at `g`) plus three premises on `Δ_F`: row service at `Δ_F`
(`hrow`), `6Δ + Δ_F ≤ 4Δ·δt` (`htd`, the field `timeoutDelay`), and `Δ ≤ Δ_F` (`hΔF`), which
only fills the field `ResetService.deltaF`. -/
theorem hsSharedUpTo_of_rows (run : (Sys (family S) V).Run) (hn : 1 ≤ Fintype.card V)
    (valid : (Sys (family S) V).Valid run) (noCollision : ¬ run.2.HashCollision) {g : Time}
    (healthy : (Sys (family S) V).Healthy (K S A) g run) {ΔF : Time}
    (hrow : PSyncFGRowTransport S run.2 (simTrace S run.2 hn) (honestKeys S run.2) ΔF)
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
    resetService_of_psync S run.2 hn valid hnc hnet hrow hΔF, hawake, ?_, ?_, htd⟩
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

/-- **The monotone lift**: the shared HS premises of a healthy run at every `Δ_F ≥ Δ_p` with
`6Δ + Δ_F ≤ 4Δ·δt`, from the network's row service at `Δ_p` (`signed_row_service_psync`) lifted
by `PSyncFGRowTransport.mono`. -/
theorem hsSharedUpTo_of_healthy (run : (Sys (family S) V).Run) (hn : 1 ≤ Fintype.card V)
    (valid : (Sys (family S) V).Valid run) (noCollision : ¬ run.2.HashCollision) {g : Time}
    (healthy : (Sys (family S) V).Healthy (K S A) g run) {ΔF : Time}
    (hΔF : (S.params (Model.pubOf run.1) hn).Δ ≤ ΔF)
    (htd : 6 * (S.params (Model.pubOf run.1) hn).Δ + ΔF ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo (simTrace S run.2 hn) (honestKeys S run.2) (digestOf S run.2) g
      ΔF run.2.horizon :=
  hsSharedUpTo_of_rows S A V run hn valid noCollision healthy
    ((signed_row_service_psync S run.2 hn valid).mono _ _ _ _ hΔF) hΔF htd

end Consensus.Goldilocks.Refinement

end
