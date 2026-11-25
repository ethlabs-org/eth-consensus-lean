module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Preparation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMapFields
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Restart
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Healthy query service with honesty at each observation -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable {S : Setup} {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
private theorem healthy_awake_of_bindings {P : Params} {A : NodeAC P} {tr : RunTrace A}
    {H : Time → Set (Fin P.n)} {O : OutputSchema} {F : Model.ProtocolFamily O}
    {E : Env V} {rho : Model.Run F E} (key : Fin P.n ≃ V)
    (hH : ∀ y t, t ≤ rho.horizon → y ∈ H t → rho.point.HonestAt (key y) t)
    (hw : ∀ y t, E.awake (key y) t = true → 0 ≤ t → t ≤ rho.horizon → tr.awake y t)
    {β : ℚ} {g b : Time} (hb : b ≤ rho.horizon) (h : rho.point.HealthyOn β g b) :
    ∀ y t, y ∈ H t → max g 0 ≤ t → t ≤ b → tr.awake y t := by
  intro y t hy hg ht
  exact hw y t (h.2 _ t hg ht (hH y t (ht.trans hb) hy)) ((le_max_right _ _).trans hg)
    (ht.trans hb)

/-- Healthy participation makes every currently honest validator awake in the mapped window. -/
theorem _root_.Consensus.Goldilocks.Generic.RunMap.healthy_awake_at
    {P : Params} {A : NodeAC P} {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
    {F : ChainShapeFamily O I} {E : Env V} {rho : Model.Run (compiled F) E}
    {payload : A.Blk → Set Nat} (M : Generic.RunMap rho payload)
    {β : ℚ} {g b : Time} (hb : b ≤ rho.horizon) (h : rho.point.HealthyOn β g b) :
    ∀ y t, y ∈ M.honest t → max g 0 ≤ t → t ≤ b → M.trace.awake y t :=
  healthy_awake_of_bindings M.validator (fun _ _ ht => (M.honest_iff_of_le ht).mp)
    (fun y t hw h0 ht => (M.awake_eq y t).mpr ⟨hw, h0, ht⟩) hb h

/-- Every validator honest at the current time is awake after GST, up to a healthy bound. -/
theorem healthy_preparation_awake_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) {β : ℚ} {g b : Time} (hb : b ≤ run.2.horizon)
    (hH : ((Sys (goldilocks S) V).pt run).HealthyOn β g b) :
    ∀ y t, y ∈ honestKeysAt S run.2 t → AC.gbar g ≤ t → t ≤ b →
      (simTraceAt S run.2 hn).awake y t := by
  refine healthy_awake_of_bindings (tr := simTraceAt S run.2 hn)
    (H := honestKeysAt S run.2) run.2.key ?_ ?_ hb hH
  · intro y t ht hy
    rw [mem_honestKeysAt_iff S run.2, min_eq_left ht] at hy
    exact hy
  · intro y t hw h0 ht
    rw [simTraceAt_awake_iff S run.2 hn, awakeAt_iff S run.2 hn]
    exact ⟨hw, h0, ht⟩

/-- A healthy population bound at `b` also bounds the mapped faults at each earlier time. -/
theorem _root_.Consensus.Goldilocks.Generic.RunMap.healthy_population_at
    {P : Params} {A : NodeAC P} {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
    {F : ChainShapeFamily O I} {E : Env V} {rho : Model.Run (compiled F) E}
    {payload : A.Blk → Set Nat} (M : Generic.RunMap rho payload)
    {β : ℚ} {g b : Time} (hb : b ≤ rho.horizon) (h : rho.point.HealthyOn β g b)
    {t : Time} (ht : t ≤ b) : ((M.honest t)ᶜ.ncard : ℚ) < β * P.n := by
  rw [M.faulty_ncard (ht.trans hb), ← Fintype.card_fin P.n, Fintype.card_congr M.validator]
  exact (show ((rho.faultyAt t).card : ℚ) ≤ (rho.faultyAt b).card by
    exact_mod_cast Finset.card_le_card (rho.faultyAt_mono ht)).trans_lt h.1

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
    exact_mod_cast (show (3 : ℚ) * (run.2.faultyAt b).card < Fintype.card V by
      linarith [mul_le_mul_of_nonneg_right hβ hV])
  change 3 * (run.2.faultyAt t).card ≤ Fintype.card V - 1
  omega

/-- Service follows the actual signed messages, even after their sender is compromised; signed
rows at the release hold `hold` are consumed up to the bound `b ≤ horizon`, reading the run's
participation only through `b` (`hawake`, needed only when `hold ≠ 0`). -/
theorem healthy_preparation_service_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) (hv : (Sys (goldilocks S) V).Valid run)
    (hnc : ¬ run.2.HashCollision) {g b : Time} (hb : b ≤ run.2.horizon)
    (hps : ((Sys (goldilocks S) V).log run).PSync ((Sys (goldilocks S) V).pt run) g)
    {ΔF hold : Time}
    (hrow : PSyncFGAttTransportAt S run.2 (simTraceAt S run.2 hn) (honestKeysAt S run.2) ΔF hold)
    (hawake : hold ≠ 0 → ∀ v t, max g 0 ≤ t → t ≤ b → run.2.point.HonestAt v t →
      run.2.point.env.awake v t = true)
    (hΔF : 0 < ΔF) (hhold : hold ≤ ΔF) :
    Healing.Growing.ResetService (simTraceAt S run.2 hn) (honestKeysAt S run.2) g ΔF b hold :=
  resetService_of_psync_upTo S run.2 hn hv (noCollRun_simTraceAt S run.2 hn hv hnc)
    ((Model.sysOf_delivers_iff _ _ _ _).mp hps) hrow hb hawake hΔF hhold

/-- An honest restart up to a healthy bound cannot follow GST: its preceding sleep contradicts
healthy wakefulness. -/
theorem healthy_preparation_noRestart_at (run : (Sys (goldilocks S) V).Run)
    (hn : 1 ≤ Fintype.card V) (hv : (Sys (goldilocks S) V).Valid run) {β : ℚ} {g b : Time}
    (hb : b ≤ run.2.horizon) (hH : ((Sys (goldilocks S) V).pt run).HealthyOn β g b) :
    Healing.Growing.NoRestartUpTo (simTraceAt S run.2 hn) (honestKeysAt S run.2) (AC.gbar g)
      b := by
  rw [Healing.Growing.noRestartUpTo_iff]
  intro y i hy hr hib
  by_contra h
  have hgi : AC.gbar g < (simTraceAt S run.2 hn).time i := lt_of_not_ge h
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
