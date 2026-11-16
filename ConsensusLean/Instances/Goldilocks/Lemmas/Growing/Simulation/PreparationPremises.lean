module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Preparation premises of a Goldilocks run

`goldilocks_preparation_premises_supply`: every `Premises` field of a healthy Goldilocks run at
its horizon, at any vote binding and contract, under two coefficient fits. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] (S : Setup) {E : Env V}
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Preparation premises of a healthy Goldilocks run, at any vote binding and contract.**
Under `HealthyBetaFit K`, a valid collision-free run healthy from `gst` with nonfinal progress up
to a heal point within the horizon meets every `Premises` field at the horizon, with the
environment's FG delay. The timeout fit is the coefficient bound `fgDelay + 6 ≤ 4·δt`; the snapshot
reserve is `13 ≤ heal`, since `c_z + Δ ≤ ḡ + 13Δ`. -/
theorem goldilocks_preparation_premises_supply (hv : rho.ExecutionValid) (K : Contract ProgressReq)
    (hfg : K.params.fgDelay + 6 ≤ 4 * S.δt)
    (hheal : ∀ cap idx, (cap = .available ∨ cap = .stable) → 13 ≤ K.params.heal cap idx) :
    Generic.PreparationPremisesSupply (goldilocksRunMap S rho hn hv) K := by
  classical
  intro hβ hv' hnc cap idx gst hcap hH _ hhb
  simp only [goldilocksRunMap_trace, goldilocksRunMap_honest, goldilocksRunMap_committee,
    goldilocksRunMap_digest]
  obtain ⟨hps, hon, hΔF, hcom⟩ := hH
  let sp := S.params (Model.pubOf E) hn
  have hhor : rho.horizon ≤ rho.horizon := le_rfl
  have hb0 : 0 ≤ rho.horizon := hv'.horizon_nonneg
  have hrun := simTraceAt_goldilocksRun S rho hn hv'
  have hncr := noCollRun_simTraceAt S rho hn hv' hnc
  have haw := Obligations.Growing.healthy_preparation_awake_at (S := S) ⟨E, rho⟩ hn hhor hon
  have hf := Obligations.Growing.healthy_preparation_faults_at (S := S) ⟨E, rho⟩ hn hβ hhor hon
  have hne : (honestKeysAt S rho rho.horizon).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hh := hf _ hb0 le_rfl
    rw [h, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hh
    have := sp.toParams.hn
    change 0 < sp.n at this
    change 3 * sp.n ≤ sp.n - 1 at hh
    omega
  have hgrid : ∀ s : Nat, sp.toParams.slotTime s = (s : Time) * (4 * sp.toParams.Δ) := fun s => by
    rw [sp.slotTime_eq]
    ring
  have hsnap : ∃ k, Healing.FirstCutAfter (simTraceAt S rho hn) k (Healing.cutZ sp.toParams gst) ∧
      (simTraceAt S rho hn).time k ≤ rho.horizon := by
    have haw' : ∀ y ∈ honestKeysAt S rho rho.horizon, ∀ t, SA.gbar gst ≤ t →
        t ≤ rho.horizon → ((simTraceAt S rho hn).upTo rho.horizon).awake y t :=
      fun y hy t ht htb => ⟨haw y t (hrun.antitone htb hy) ht htb, htb⟩
    have hcz := Healing.cutZ_le (sp := sp) gst
    have h13 : (13 : Time) ≤ (K.params.heal cap idx : Time) := by exact_mod_cast hheal cap idx hcap
    have hheal' : max gst 0 + (K.params.heal cap idx : Time) * E.ΔAC ≤ rho.horizon := hhb
    have hΔ0 : 0 < E.ΔAC := E.ΔAC_pos
    have h13Δ := mul_le_mul_of_nonneg_right h13 hΔ0.le
    exact Healing.snapshot_of_awake (hrun.upTo hb0).toLocalRun haw' hne (by
      unfold SA.gbar at hcz
      change _ ≤ max gst 0 + 12 * E.ΔAC at hcz
      change Healing.cutZ _ gst + E.ΔAC ≤ rho.horizon
      linarith)
  refine
    { committee := committeeFaultsUpTo_of_healthyOn S rho hn hv' hcom
      noColl := hncr
      sync := by
        have hs := Obligations.Growing.healthy_preparation_service_at (S := S) ⟨E, rho⟩ hn hv' hnc
          hhor hps
        rw [Obligations.protoFGDelay_eq] at hs
        exact Healing.Growing.ResetService.toService hs
      awake := haw
      faults := hf
      catchUp := Obligations.Growing.catchRun_of_psync_at S rho hn hv' hncr
        ((Model.sysOf_delivers_iff _ _ _ _).mp hps) fun v u hu hub _ hvf =>
          hon.2 v u hu hub hvf
      noRestart := fun y k hy hk => by
        have hnr := Obligations.Growing.healthy_preparation_noRestart_at (S := S) ⟨E, rho⟩ hn hv'
          hhor hon
        obtain ⟨ℓ, hc, _⟩ := hk
        exact Healing.Growing.noRestartUpTo_iff.mp hnr y k hy ⟨ℓ, hc, ‹_›⟩
          (Obligations.Growing.isCall_time_le_horizon S rho hn hv' ⟨_, hc⟩)
      timeoutDelay := (Generic.timeout_grid_equation _ hgrid).mpr (by
        have hfg' : ((K.params.fgDelay : Nat) + 6 : Time) ≤ 4 * (S.δt : Time) := by
          exact_mod_cast hfg
        have hΔ0 : 0 < E.ΔAC := E.ΔAC_pos
        have hm := mul_le_mul_of_nonneg_right hfg' hΔ0.le
        have hF : E.ΔFG ≤ (K.params.fgDelay : Time) * E.ΔAC := hΔF
        change 6 * E.ΔAC + E.ΔFG ≤ 4 * E.ΔAC * (S.δt : Time)
        linarith)
      slotLen := Generic.slotLen_of_grid hgrid
      snapshot := hsnap
      nonempty := hne }

end Consensus.Goldilocks.Simulation

end
