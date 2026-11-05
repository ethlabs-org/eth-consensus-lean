module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: `HSSharedUpTo` from a healthy run, at a parametric `Δ_F` (#136)

The shared HS premises through the engine horizon, from the run data of a query alone (valid
execution, no observed collision, `Healthy` at GST `g`), at a parametric FG delay `Δ_F`.

* `hsSharedUpTo_of_rows`: from attestation service at `Δ_F` (`PSyncFGAttTransport … Δ_F`) as a
  premise.
* `protoFGDelay_delivery_of_healthy`, `protoFGDelay_timeout_of_healthy`: the healthy regime of
  `K S A` bounds the engine FG delay by the contract's bound (`ΔFG ≤ (4·fgSlots − 6)·ΔAC`), so the
  protocol FG delay `Δ_F,p = protoFGDelay (pubOf E)` satisfies
  `6Δ_p + Δ_F,p ≤ 4Δ_p·fgSlots ≤ 4Δ_p·δ_t` (`fgDelay_bound_iff`, `3·fgSlots ≤ δ_t`). No order
  between `Δ` and `Δ_F` is used.
* `hsSharedUpTo_of_healthy`: the monotone lift, at every `Δ_F ≥ Δ_F,p`, from the network's
  attestation service at `Δ_F,p` (`signed_row_service_psync`). The lift (`PSyncFGAttTransport.mono`)
  exists, but the obligations proof uses it only at `le_rfl` (`Δ_F = Δ_F,p`).

Fields: `noColl`, `genesisRoot` (`noCollTransport`, `simTrace_genesis_root_ok`); `sync`
(`resetService_of_psync` at `PSync g`, from `Healthy`, with the attestation service); `awake`
(`HealthyOn`); `faults` (`|faulty| < n/3`, `β = 1/3`); `noRestart` (a restart at `t` has its node
asleep at `t - 1`, `simTrace_asleep_before_restart`); `timeoutDelay` (the hypothesis
`6Δ + Δ_F ≤ 4Δ·δt`). The query wrappers are thin instances: `FinalQuery.hsSharedUpTo` and
`FinalQuery.hsSharedUpTo_of_rows` (HSSharedOfQuery), `FinalQuery.hsSharedUpTo_of_le`
(RowServiceParam) and `HealthyPreparationQuery.hsSharedUpTo_of_le` (HealthyQueryShared). This
module stays upstream of `FinalWindowDefs` and `HealedSafety`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The shared HS premises of a healthy run through its horizon, from attestation service at
`Δ_F`**, at GST `g` and the digest of the run. Only the run data of a query are used (valid
execution, no observed collision, `Healthy` at `g`) plus three premises on `Δ_F`: attestation
service at `Δ_F` (`hrow`), `6Δ + Δ_F ≤ 4Δ·δt` (`htd`, the field `timeoutDelay`), and `0 < Δ_F`
(`hΔF`), which only fills the field `ResetService.deltaF`; no order between `Δ` and `Δ_F` is used.
-/
theorem hsSharedUpTo_of_rows (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (valid : (Sys (goldilocks S) V).Valid run) (noCollision : ¬ run.2.HashCollision) {g : Time}
    (healthy : (Sys (goldilocks S) V).Healthy (K S A) g run) {ΔF : Time}
    (hrow : PSyncFGAttTransport S run.2 (simTrace S run.2 hn) (honestKeys S run.2) ΔF)
    (hΔF : 0 < ΔF)
    (htd : 6 * (S.params (Model.pubOf run.1) hn).Δ + ΔF ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo (simTrace S run.2 hn) (honestKeys S run.2) (digestOf S run.2) g
      ΔF run.2.horizon := by
  have hnc := noCollRun_simTrace S run.2 hn valid noCollision
  have hnet : run.2.log.PSync run.2.point g := (Model.sysOf_delivers_iff _ _ _ _).mp healthy.1
  have hawake : ∀ y ∈ honestKeys S run.2, ∀ t, SA.gbar g ≤ t → t ≤ run.2.horizon →
      (simTrace S run.2 hn).awake y t := by
    intro y hy t hg hb
    rw [simTrace_awake_iff, awakeAt_iff]
    exact ⟨healthy.2.1.2 (run.2.key y) ((mem_honestKeys_iff S run.2 y).mp hy)
      t hg hb, le_trans (le_max_right _ _) hg, hb⟩
  refine ⟨hnc, simTrace_genesis_root_ok S run.2 hn,
    resetService_of_psync S run.2 hn valid hnc hnet hrow hΔF, hawake, ?_, ?_, htd⟩
  · have hpop := healthy.2.1.1
    change (run.2.point.faulty.card : ℚ) < (K S A).params.β * Fintype.card V at hpop
    rw [goldilocksContract_params_eq] at hpop
    change (run.2.point.faulty.card : ℚ) < 1 / 3 * Fintype.card V at hpop
    have hfault : (honestKeys S run.2)ᶜ.ncard = run.2.point.faulty.card := by
      have heq : (honestKeys S run.2)ᶜ = run.2.key ⁻¹' (↑run.2.point.faulty : Set V) := by
        ext k; simp [mem_honestKeys_iff, EnvPoint.faulty, Model.Run.point]
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

/-- The protocol FG delay is positive. -/
theorem protoFGDelay_pos (pub : Model.Public) : 0 < protoFGDelay pub := by
  rw [protoFGDelay_eq]
  exact pub.ΔFG_pos

/-- **The FG transport of a healthy run of `K S A`**: the healthy regime bounds the engine FG
delay by the contract's FG delay bound, `ΔFG ≤ (4·fgSlots − 6)·ΔAC`, so the protocol delays satisfy
`6Δ_p + Δ_F,p ≤ 4Δ_p·fgSlots` (`fgDelay_bound_iff`), with `Δ_F,p = protoFGDelay (pubOf E)`. -/
theorem protoFGDelay_delivery_of_healthy (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) {g : Time} (healthy : (Sys (goldilocks S) V).Healthy (K S A) g run) :
    6 * (S.params (Model.pubOf run.1) hn).Δ + protoFGDelay (Model.pubOf run.1) ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (A.fgSlots : Time) := by
  have h := healthy.2.2
  change run.1.ΔFG ≤ ((A.fgDelay : ℕ+) : Time) * run.1.ΔAC at h
  rw [protoFGDelay_eq]
  exact (fgDelay_bound_iff A run.1.ΔAC run.1.ΔFG).1 h

/-- **The rise timeout of a healthy run of `K S A`** at the protocol FG delay:
`6Δ_p + Δ_F,p ≤ 4Δ_p·fgSlots ≤ 4Δ_p·δ_t`, from `protoFGDelay_delivery_of_healthy` and
`3·fgSlots ≤ δ_t` (`ContractAssumptions.timeout`). -/
theorem protoFGDelay_timeout_of_healthy (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    {g : Time} (healthy : (Sys (goldilocks S) V).Healthy (K S A) g run) :
    6 * (S.params (Model.pubOf run.1) hn).Δ + protoFGDelay (Model.pubOf run.1) ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (S.δt : Time) := by
  have h := protoFGDelay_delivery_of_healthy S A V run hn healthy
  have hΔ := (S.params (Model.pubOf run.1) hn).toParams.hΔ
  have hc : (A.fgSlots : Time) ≤ (S.δt : Time) := by
    have := A.timeout
    exact_mod_cast (show A.fgSlots ≤ S.δt by omega)
  nlinarith

/-- **The monotone lift**: the shared HS premises of a healthy run at every `Δ_F ≥ Δ_F,p` with
`6Δ + Δ_F ≤ 4Δ·δt`, from the network's attestation service at the protocol FG delay
(`signed_row_service_psync`) lifted by `PSyncFGAttTransport.mono`. -/
theorem hsSharedUpTo_of_healthy (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (valid : (Sys (goldilocks S) V).Valid run) (noCollision : ¬ run.2.HashCollision) {g : Time}
    (healthy : (Sys (goldilocks S) V).Healthy (K S A) g run) {ΔF : Time}
    (hΔF : protoFGDelay (Model.pubOf run.1) ≤ ΔF)
    (htd : 6 * (S.params (Model.pubOf run.1) hn).Δ + ΔF ≤
      4 * (S.params (Model.pubOf run.1) hn).Δ * (S.δt : Time)) :
    Healing.HSSharedUpTo (simTrace S run.2 hn) (honestKeys S run.2) (digestOf S run.2) g
      ΔF run.2.horizon :=
  hsSharedUpTo_of_rows S A V run hn valid noCollision healthy
    ((signed_row_service_psync S run.2 hn valid).mono _ _ _ _ hΔF)
    ((protoFGDelay_pos _).trans_le hΔF) htd

end Consensus.Goldilocks.Obligations

end
