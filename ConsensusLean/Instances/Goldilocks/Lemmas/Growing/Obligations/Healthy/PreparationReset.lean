module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The finite reset envelope of a growing healthy query -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The parameter-only healing coefficient covers the reset envelope. -/
theorem healthy_preparation_reset_fit_at (Q : HealthyPreparationQueryAt S A V) :
    Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      (healthyResetSlack S Q.index : Time) ≤ Q.heal := by
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hready :
      Q.ready = max Q.gst 0 + ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC + 1 := by
    change max Q.gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * Q.run.1.ΔAC + 1 = _
    rw [contract_coefficients_catchUp]
  have hheal : Q.heal = max Q.gst 0 + (contract_heal S A Q.cap Q.index : Time) * Q.run.1.ΔAC := by
    change max Q.gst 0 + ((contract_coefficients S A).heal Q.cap Q.index : Time) * Q.run.1.ΔAC = _
    rw [contract_coefficients_heal]
  have hΔ : Q.params.Δ = Q.run.1.ΔAC := rfl
  have hH : ((contract_catchUp S A : Nat) : Time) + (healthyResetCoeff S Q.index : Time) +
      (healthyResetSlack S Q.index : Time) + 1 ≤ (contract_heal S A Q.cap Q.index : Time) := by
    have := contract_heal_ge_reset S A Q.cap Q.index
    exact_mod_cast (show _ ≤ _ by omega)
  have hr0 : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  rw [hready, hheal, hΔ]
  linarith only [mul_le_mul_of_nonneg_right hH (zero_le_one.trans hd),
    mul_nonneg hr0 (sub_nonneg.mpr hd), hd]

/-- Actual proposals from progress and finite healthy service supply a bounded reset. -/
theorem healthy_preparation_reset_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run) :
    ∃ ΔF a, Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.bound ∧
      a ≤ Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        (healthyResetSlack S Q.index : Time) := by
  classical
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hs := healthy_preparation_service_at S A V Q
  have haw := healthy_preparation_awake_at S A V Q
  have hf := healthy_preparation_faults_at S A V Q
  have hfit := healthy_preparation_reset_fit_at S A V Q
  have hready : Q.ready = max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 := rfl
  have hcDur : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run :=
    mul_nonneg (Int.natCast_nonneg _) Q.run.1.ΔAC_pos.le
  have hr0 : 0 ≤ Q.ready := by rw [hready]; linarith only [le_max_right Q.gst 0, hcDur]
  have hgr : SA.gbar Q.gst ≤ Q.ready := by
    change max Q.gst 0 ≤ Q.ready
    rw [hready]; linarith only [hcDur]
  have hcz := cutZ_fit_of_catchUp A V (contract_coefficients S A)
    (by rw [contract_coefficients_catchUp]; exact contract_catchUp_ge_sleepy S A) Q.run Q.hn Q.gst
  change Healing.cutZ Q.params.toParams Q.gst + Q.params.Δ + 1 ≤ max Q.ready 0 + 4 * Q.params.Δ
    at hcz
  rw [max_eq_left hr0] at hcz
  have hb0 : 0 ≤ Q.bound := by
    have := mul_nonneg (Nat.cast_nonneg (α := Time) (healthyResetCoeff S Q.index)) hΔ.le
    linarith only [this, hfit, hr0, hb, Nat.cast_nonneg (α := Time) (healthyResetSlack S Q.index)]
  have hH : (Q.keys Q.bound).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hh := hf _ hb0 le_rfl
    rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hh
    have hn := Q.params.toParams.hn
    change 0 < Q.params.n at hn
    change 3 * Q.params.n ≤ Q.params.n - 1 at hh
    omega
  have hBeq : resetBoundRounds Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) =
      Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ := by
    rw [resetBoundRounds_eq, healthyResetCoeff_val, hδeq]; push_cast; ring
  have hR : (24 : Time) ≤ healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith only [Nat.cast_nonneg (α := Time) (healthyDrainLen S Q.index)]
  have hr : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  have hBh : resetBoundRounds Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) ≤ Q.heal := by
    rw [hBeq]; linarith only [hfit, hr]
  have h4B : Q.ready + 4 * Q.params.Δ ≤ Q.heal := by
    have := mul_le_mul_of_nonneg_right hR hΔ.le
    linarith only [this, hfit, hr, hΔ]
  have hcatch := healthy_repair_catch_at S A V Q (by linarith only [hgr, h4B, hb, hΔ])
  have hnr := healthy_preparation_noRestart_at S A V Q
  have hdrain := Healing.Growing.drainOutputs_of_service_at hrun hnc hs haw hf hcatch
    (G := (Q.index : Nat)) (Ld := healthyDrainLen S Q.index)
    (by rw [healthyDrainLen_val]; change 2 * S.k + (Q.index : Nat) ≤ 2 * S.k + (Q.index : Nat) + 1
        omega)
  obtain ⟨a, ha, hab⟩ := Healing.Growing.exists_reset_of_drain_rounds_awake_at hrun hnc hf hs
    haw hcatch hnr hH (by rw [hδeq]; have := A.six_le_δt; omega)
    (protoFGDelay_timeout_of_fgDelay S A V Q.run Q.hn Q.healthy.2.2)
    hr0 hgr Q.index.pos hcz (hBh.trans hb) (fun s₀ N hs₀ hN => by
      apply Healing.Growing.proposalGap_iff.mpr
      intro c hc hcN
      obtain ⟨x, hxl, hxr, k, P, hx, hP, _, hPs⟩ := healthy_preparation_gap_at S A V Q
        (hb.trans Q.bound_le) hp
        (by rw [max_eq_left hr0]; exact hs₀) (by linarith only [hN, hBh, hΔ]) c hc hcN
      exact ⟨x, hxl, hxr, hx, k, P, hP, hPs⟩) hdrain
  have haw' : ∀ y ∈ Q.keys Q.bound, ∀ t, SA.gbar Q.gst ≤ t →
      t ≤ Q.bound → (Q.trace.upTo Q.bound).awake y t := by
    intro y hy t ht htb
    exact ⟨haw y t (hrun.antitone htb hy) ht htb, htb⟩
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake (hrun.upTo hb0) haw' hH
    (by linarith only [hcz, h4B, hb])
  refine ⟨_, a, Healing.Growing.resetPremisesUpTo_of_reset_at hrun hnc hs haw hf ha
    (hab.trans (hBh.trans hb)) ⟨j, hj, hjt⟩, ?_⟩
  rw [hBeq] at hab
  linarith only [hab, hr]

end Consensus.Goldilocks.Obligations.Growing

end
