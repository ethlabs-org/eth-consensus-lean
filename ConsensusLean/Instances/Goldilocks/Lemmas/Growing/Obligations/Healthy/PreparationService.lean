module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Preparation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Restart
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Healthy query service with honesty at each observation -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- Every validator honest at the current time is awake after GST, up to the query's bound. -/
theorem healthy_preparation_awake_at (Q : HealthyPreparationQueryAt S A V) :
    ∀ y t, y ∈ Q.keys t → SA.gbar Q.gst ≤ t → t ≤ Q.bound →
      Q.trace.awake y t := by
  intro y t hy hg hb
  have hh := hb.trans Q.bound_le
  rw [simTraceAt_awake_iff, awakeAt_iff]
  rw [mem_honestKeysAt_iff, min_eq_left hh] at hy
  exact ⟨Q.healthy.2.1.2 _ t hg hb hy, (le_max_right _ _).trans hg, hh⟩

/-- The healthy fault bound at the query's bound also bounds every earlier cut. -/
theorem healthy_preparation_faults_at (Q : HealthyPreparationQueryAt S A V) :
    ∀ t, 0 ≤ t → t ≤ Q.bound →
      3 * (Q.keys t)ᶜ.ncard ≤ Q.params.n - 1 := by
  intro t _ ht
  have hpop := Q.healthy.2.1.1
  change ((Q.run.2.faultyAt Q.bound).card : ℚ) <
    (K S A).params.β * Fintype.card V at hpop
  rw [goldilocksContract_params_eq] at hpop
  change ((Q.run.2.faultyAt Q.bound).card : ℚ) <
    1 / 3 * Fintype.card V at hpop
  have heq : (Q.keys t)ᶜ = Q.run.2.key ⁻¹' (↑(Q.run.2.faultyAt t) : Set V) := by
    ext y
    simp [mem_honestKeysAt_iff, min_eq_left (ht.trans Q.bound_le)]
  rw [heq, Set.ncard_preimage_of_injective_subset_range Q.run.2.key.injective
    (by simp [Q.run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
  have hcard := Finset.card_le_card (Q.run.2.faultyAt_mono ht)
  have hnat : 3 * (Q.run.2.faultyAt Q.bound).card < Fintype.card V := by
    exact_mod_cast (show (3 : ℚ) * (Q.run.2.faultyAt Q.bound).card <
      Fintype.card V by linarith)
  change 3 * (Q.run.2.faultyAt t).card ≤ Fintype.card V - 1
  omega

/-- Service follows the actual signed messages, even after their sender is compromised; signed
rows are consumed up to the query's bound. -/
theorem healthy_preparation_service_at (Q : HealthyPreparationQueryAt S A V) :
    Healing.Growing.ResetService Q.trace Q.keys Q.gst
      (protoFGDelay (Model.pubOf Q.run.1)) Q.bound := by
  have hs := resetService_of_psync_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision)
    ((Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1)
    (signed_row_service_psync_at S Q.run.2 Q.hn Q.valid) (protoFGDelay_pos _)
  exact ⟨hs.deltaF, hs.message, hs.block, hs.relay,
    fun x i att hx hsg y j hy hj hjb =>
      hs.signedRow x i att hx hsg y j hy hj (hjb.trans Q.bound_le)⟩

/-- An honest restart up to the query's bound cannot follow GST: its preceding sleep contradicts
healthy wakefulness. -/
theorem healthy_preparation_noRestart_at (Q : HealthyPreparationQueryAt S A V) :
    Healing.Growing.NoRestartUpTo Q.trace Q.keys (SA.gbar Q.gst) Q.bound := by
  rw [Healing.Growing.noRestartUpTo_iff]
  intro y i hy hr hib
  by_contra h
  have hgi : SA.gbar Q.gst < Q.trace.time i := lt_of_not_ge h
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hy0 : y ∈ honestKeys S Q.run.2 := by
    rw [mem_honestKeys_iff]
    have hz := hrun.antitone (hrun.time_nonneg i) hy
    rw [mem_honestKeysAt_iff, min_eq_left Q.valid.horizon_nonneg] at hz
    exact hz
  have hs := simTrace_asleep_before_restart S Q.run.2 Q.hn Q.valid y hy0 i
    (by simpa only [simTraceAt_eq] using hr)
  rw [← simTraceAt_eq] at hs
  exact hs (healthy_preparation_awake_at S A V Q y (Q.trace.time i - 1)
    (hrun.antitone (by linarith) hy) (Int.le_sub_one_of_lt hgi) (by linarith))

end Consensus.Goldilocks.Obligations.Growing

end
