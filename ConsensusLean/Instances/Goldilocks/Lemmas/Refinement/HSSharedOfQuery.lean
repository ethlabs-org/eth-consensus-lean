module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Accepted
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeMatureUpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NetworkTransport

public section

/-! # Goldilocks Refinement: `HSSharedUpTo` from a final query (#136)

consensus-lean#136, route A. `FinalQuery.hsSharedUpTo` supplies the shared HS premises of
`anchorSteps_gap2` (AnchorStepsSupply.lean) through the engine horizon, from the query data
alone: GST `Q.gst`, forwarding delay `Δ_F = Δ` (the protocol delay), horizon `rho.horizon`.

* `noColl`, `genesisRoot`: `noCollTransport` and `simTrace_genesis_root_ok`.
* `sync`: `resetService_of_psync` at `PSync Q.gst` (from `Healthy`).
* `awake`: `FinalQuery.awake_all`, from `HealthyOn`.
* `faults`: `|faulty| < n/3` (from `HealthyOn`, `β = 1/3`).
* `noRestart`: a restart at `t` has its node asleep at `t - 1` (`simTrace_asleep_before_restart`),
  so it is not after `ḡ`.
* `timeoutDelay`: `7Δ ≤ 24Δ ≤ 4Δ·δt` from `6 ≤ δt` (`AcceptanceAssumptions.timeout`).

`FinalQuery.deltaF_le` is the premise `Δ_F ≤ 2Δ` of `anchorSteps_gap2` at `Δ_F = Δ`. -/

namespace Consensus.Goldilocks.Refinement

open SA (gbar)

variable {S : Setup} {A : AcceptanceAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace FinalQuery

/-- Every honest node is awake on `[ḡ, horizon]` (`HealthyOn`). -/
theorem awake_all (Q : FinalQuery S A V) :
    ∀ y ∈ honestKeys S Q.run.2, ∀ t, gbar Q.gst ≤ t → t ≤ Q.run.2.horizon →
      Q.trace.awake y t := by
  intro y hy t hg hb
  exact ⟨Q.healthy.2.2 (Q.run.2.key y) hy t hg hb, le_trans (le_max_right _ _) hg, hb⟩

/-- `Δ_F = Δ` satisfies the premise `Δ_F ≤ 2Δ` of `anchorSteps_gap2`. -/
theorem deltaF_le (Q : FinalQuery S A V) : Q.params.Δ ≤ 2 * Q.params.Δ := by
  have := Q.params.toParams.hΔ
  linarith

/-- **The shared HS premises of a final query through its horizon**, at GST `Q.gst`,
`Δ_F = Δ`, and the digest of the run. -/
theorem hsSharedUpTo (Q : FinalQuery S A V) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      Q.params.Δ Q.run.2.horizon := by
  have hnc := noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst := by
    constructor
    · intro v hv o s hs w hw a hsa hc hh haw
      have h := Q.healthy.1.msgs v hv ⟨Q.run.1, o⟩ s ⟨o, rfl, hs⟩ w hw a hsa hc hh haw
      rcases h with ⟨u, hu, hsent | hrecv, hnowake⟩
      · obtain ⟨o', he, hs'⟩ := hsent
        cases he
        exact ⟨u, hu, Or.inl hs', hnowake⟩
      · obtain ⟨o', he, hr'⟩ := hrecv
        cases he
        exact ⟨u, hu, Or.inr hr', hnowake⟩
    · exact Q.healthy.1.txs
  refine ⟨hnc, simTrace_genesis_root_ok S Q.run.2 Q.hn,
    resetService_of_psync S Q.run.2 Q.hn Q.valid hnc hnet, Q.awake_all, ?_, ?_, ?_⟩
  · have hpop := Q.healthy.2.1
    change (Q.run.2.point.faulty.card : ℚ) < (K S A).params.β * Fintype.card V at hpop
    rw [acceptanceContract_params_eq] at hpop
    change (Q.run.2.point.faulty.card : ℚ) < 1 / 3 * Fintype.card V at hpop
    have hfault : (honestKeys S Q.run.2)ᶜ.ncard = Q.run.2.point.faulty.card := by
      have heq : (honestKeys S Q.run.2)ᶜ = Q.run.2.key ⁻¹' (↑Q.run.2.point.faulty : Set V) := by
        ext k; simp [honestKeys, EnvPoint.faulty, Model.Run.point]
      rw [heq, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
        (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
    change 3 * (honestKeys S Q.run.2)ᶜ.ncard ≤ Fintype.card V - 1
    rw [hfault]
    have hn : 3 * Q.run.2.point.faulty.card < Fintype.card V := by
      exact_mod_cast (show (3 : ℚ) * Q.run.2.point.faulty.card < Fintype.card V by linarith)
    omega
  · intro y hy k hk hkb
    by_contra hlt
    rw [not_le] at hlt
    exact simTrace_asleep_before_restart S Q.run.2 Q.hn Q.valid y hy k hk
      (Q.awake_all y hy _ (Int.le_sub_one_of_lt hlt) (by linarith))
  · have hΔ := Q.params.toParams.hΔ
    have h6 : (6 : Time) ≤ (S.δt : Time) := by exact_mod_cast A.timeout
    change 6 * Q.params.Δ + Q.params.Δ ≤ 4 * Q.params.Δ * (S.δt : Time)
    nlinarith

end FinalQuery

end Consensus.Goldilocks.Refinement

end
