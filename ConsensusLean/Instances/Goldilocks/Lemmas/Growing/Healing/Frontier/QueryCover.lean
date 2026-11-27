module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.HealedCoverSupply
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The high-source cover of a healthy query

The cover supplier that the reset-record builders take (`resetPremisesUpTo_of_reset_cover_at`'s
`hcover`), for a healed-safety query `Q`: from a reset record up to `T ≤ Q.bound` inside the deep
quarantine with the drain `4Δ` before `T`, the high-source cover through `Q.bound`
(`healthy_query_cover_at`, by `healthy_high_source_cover_at` with the query's partial synchrony,
participation, faults and committee faults through its bound; conviction below a third through
the bound follows from the faults, `chainConvictedBelowUpTo_of_faults`).

The modules that discharge the builders' supplier import this one directly (it is below
Continuation, in `Healing/Frontier`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- **Conviction below a third of a query healthy through the horizon**: the honest keys at `t`
are those at `min t horizon` (`mem_honestKeysAt_iff`), where the healthy fault bound holds
(`healthy_preparation_faults_at`), so `chainConvictedBelow_of_faults` applies. -/
theorem healthy_query_convictedBelow_at (Q : HealthyPreparationQueryAt S A V)
    (hbh : Q.run.2.horizon ≤ Q.bound) :
    Compose.Growing.ChainConvictedBelow Q.trace Q.keys := by
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hf : ∀ t, 0 ≤ t → t ≤ Q.bound → 3 * (Q.keys t)ᶜ.ncard ≤ Q.params.n - 1 :=
    healthy_preparation_faults_at Q.run Q.hn
      (by rw [goldilocksContract_params_eq]; norm_num [Params.standard]) Q.bound_le Q.healthy.2.1
  refine Healing.Growing.chainConvictedBelow_of_faults hrun fun t ht => ?_
  have hkeys : Q.keys t = Q.keys (min t Q.run.2.horizon) := by
    ext y
    rw [mem_honestKeysAt_iff S Q.run.2, mem_honestKeysAt_iff S Q.run.2, min_assoc, min_self]
  rw [hkeys]
  exact hf _ (le_min ht (show Q.run.2.ExecutionValid from Q.valid).horizon_nonneg)
    ((min_le_right _ _).trans hbh)

/-- **The high-source cover supplier of a healthy query**: for every reset record up to
`T ≤ Q.bound` inside the deep quarantine, with the drain of its reset `4Δ` before `T`, the
high-source cover through `Q.bound` (`healthy_high_source_cover_at`). -/
theorem healthy_query_cover_at (Q : HealthyPreparationQueryAt S A V)
    {ΔF a T hold : Time}
    (hpT : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) Q.gst ΔF a T (runCommittee S Q.run.2 Q.hn) (K S A).params.βK hold)
    (hT : ∀ D, Q.params.deepDepth = some D →
      T ≤ Healing.cutZ Q.params.toParams Q.gst + 4 * D * Q.params.Δ)
    (hdrain : Healing.drainTime Q.params a + 4 * Q.params.Δ ≤ T) (hTb : T ≤ Q.bound) :
    Healing.Growing.HighSourceCover Q.trace Q.keys Q.gst a Q.bound := by
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hsvc := acResetService_of_psync_at S Q.run.2 Q.hn Q.valid hnc
    ((Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1)
    (Obligations.releaseGapAt_of_assumptions A _ Q.hn) hpT.sync.deltaF
  exact Healing.Growing.healthy_high_source_cover_at hpT hT hdrain hTb hsvc
    (healthy_preparation_awake_at Q.run Q.hn Q.bound_le Q.healthy.2.1)
    (healthy_preparation_faults_at Q.run Q.hn
      (by rw [goldilocksContract_params_eq]; norm_num [Params.standard]) Q.bound_le
      Q.healthy.2.1)
    (committeeFaultsUpTo_of_healthyOn S Q.run.2 Q.hn Q.valid Q.committeeHealthy)

/-- **The high-source cover supplier of a final query**, with the query's shared HS premises
through the horizon: for every reset record up to `T` within the horizon inside the deep
quarantine, with the drain of its reset `4Δ` before `T`, the high-source cover through the
horizon (`healthy_high_source_cover_at`). -/
theorem final_query_cover_at (Q : FinalQueryAt S A V) {ΔF hold : Time}
    (hs : Healing.Growing.HSSharedUpTo Q.trace Q.keys (digestOf S Q.run.2) Q.gst ΔF
      Q.run.2.horizon hold)
    {a T : Time}
    (hpT : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) Q.gst ΔF a T (runCommittee S Q.run.2 Q.hn) (K S A).params.βK hold)
    (hT : ∀ D, Q.params.deepDepth = some D →
      T ≤ Healing.cutZ Q.params.toParams Q.gst + 4 * D * Q.params.Δ)
    (hdrain : Healing.drainTime Q.params a + 4 * Q.params.Δ ≤ T) (hTb : T ≤ Q.run.2.horizon) :
    Healing.Growing.HighSourceCover Q.trace Q.keys Q.gst a Q.run.2.horizon := by
  exact Healing.Growing.healthy_high_source_cover_at hpT hT hdrain hTb hs.sync.toAC hs.awake
    hs.faults (committeeFaultsUpTo_of_healthyOn S Q.run.2 Q.hn Q.valid Q.healthy.2.2.2)

end Consensus.Goldilocks.Obligations.Growing

end
