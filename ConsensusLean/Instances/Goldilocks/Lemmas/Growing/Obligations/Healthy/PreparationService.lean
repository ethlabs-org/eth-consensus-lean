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

variable {S : Setup} {V : Type} [Fintype V] [DecidableEq V]

/-- Every validator honest at the current time is awake after GST, up to a healthy bound. -/
theorem healthy_preparation_awake_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) {β : ℚ} {g b : Time} (hb : b ≤ run.2.horizon)
    (hH : ((Sys (goldilocks S) V).pt run).HealthyOn β g b) :
    ∀ y t, y ∈ honestKeysAt S run.2 t → SA.gbar g ≤ t → t ≤ b →
      (simTraceAt S run.2 hn).awake y t := by
  intro y t hy hg htb
  have hh := htb.trans hb
  rw [simTraceAt_awake_iff S run.2 hn, awakeAt_iff S run.2 hn]
  rw [mem_honestKeysAt_iff S run.2, min_eq_left hh] at hy
  exact ⟨hH.2 _ t hg htb hy, (le_max_right _ _).trans hg, hh⟩

/-- A healthy fault bound at fraction `β ≤ 1/3`, charged at `b`, bounds every earlier cut. -/
theorem healthy_preparation_faults_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) {β : ℚ} {g b : Time} (hβ : β ≤ 1 / 3) (hb : b ≤ run.2.horizon)
    (hH : ((Sys (goldilocks S) V).pt run).HealthyOn β g b) :
    ∀ t, 0 ≤ t → t ≤ b →
      3 * (honestKeysAt S run.2 t)ᶜ.ncard ≤ (S.params (Model.pubOf run.1) hn).n - 1 := by
  intro t _ ht
  have hpop := hH.1
  change ((run.2.faultyAt b).card : ℚ) < β * Fintype.card V at hpop
  have heq : (honestKeysAt S run.2 t)ᶜ = run.2.key ⁻¹' (↑(run.2.faultyAt t) : Set V) := by
    ext y
    simp [mem_honestKeysAt_iff S run.2, min_eq_left (ht.trans hb)]
  rw [heq, Set.ncard_preimage_of_injective_subset_range run.2.key.injective
    (by simp [run.2.key.surjective.range_eq]), Set.ncard_coe_finset]
  have hcard := Finset.card_le_card (run.2.faultyAt_mono ht)
  have hV : (0 : ℚ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hnat : 3 * (run.2.faultyAt b).card < Fintype.card V := by
    exact_mod_cast (show (3 : ℚ) * (run.2.faultyAt b).card < Fintype.card V by nlinarith)
  change 3 * (run.2.faultyAt t).card ≤ Fintype.card V - 1
  omega

/-- Service follows the actual signed messages, even after their sender is compromised; signed
rows are consumed up to the bound `b ≤ horizon`. -/
theorem healthy_preparation_service_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) (hv : (Sys (goldilocks S) V).Valid run)
    (hnc : ¬ run.2.HashCollision) {g b : Time} (hb : b ≤ run.2.horizon)
    (hps : ((Sys (goldilocks S) V).log run).PSync ((Sys (goldilocks S) V).pt run) g) :
    Healing.Growing.ResetService (simTraceAt S run.2 hn) (honestKeysAt S run.2) g
      (protoFGDelay (Model.pubOf run.1)) b := by
  have hs := resetService_of_psync_at S run.2 hn hv
    (noCollRun_simTraceAt S run.2 hn hv hnc)
    ((Model.sysOf_delivers_iff _ _ _ _).mp hps)
    (signed_row_service_psync_at S run.2 hn hv) (protoFGDelay_pos _)
  exact ⟨hs.deltaF, hs.message, hs.block, hs.relay,
    fun x i att hx hsg y j hy hj hjb => hs.signedRow x i att hx hsg y j hy hj (hjb.trans hb)⟩

/-- An honest restart up to a healthy bound cannot follow GST: its preceding sleep contradicts
healthy wakefulness. -/
theorem healthy_preparation_noRestart_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) (hv : (Sys (goldilocks S) V).Valid run) {β : ℚ} {g b : Time}
    (hb : b ≤ run.2.horizon) (hH : ((Sys (goldilocks S) V).pt run).HealthyOn β g b) :
    Healing.Growing.NoRestartUpTo (simTraceAt S run.2 hn) (honestKeysAt S run.2) (SA.gbar g)
      b := by
  rw [Healing.Growing.noRestartUpTo_iff]
  intro y i hy hr hib
  by_contra h
  have hgi : SA.gbar g < (simTraceAt S run.2 hn).time i := lt_of_not_ge h
  have hrun := simTraceAt_goldilocksRun S run.2 hn hv
  have hy0 : y ∈ honestKeys S run.2 := by
    rw [mem_honestKeys_iff S run.2]
    have hz := hrun.antitone (hrun.time_nonneg i) hy
    rw [mem_honestKeysAt_iff S run.2, min_eq_left hv.horizon_nonneg] at hz
    exact hz
  have hs := simTrace_asleep_before_restart S run.2 hn hv y hy0 i
    (by simpa only [simTraceAt_eq S run.2 hn] using hr)
  rw [← simTraceAt_eq S run.2 hn] at hs
  exact hs (healthy_preparation_awake_at run hn hb hH y ((simTraceAt S run.2 hn).time i - 1)
    (hrun.antitone (by linarith) hy) (Int.le_sub_one_of_lt hgi) (by linarith))

end Consensus.Goldilocks.Obligations.Growing

end
