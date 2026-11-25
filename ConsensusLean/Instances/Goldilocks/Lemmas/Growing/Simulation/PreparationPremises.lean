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

/-! # Premises of a Goldilocks run at a bound

`goldilocks_premises_at`: every `Premises` field of a healthy Goldilocks run at any bound `b`
within its horizon that leaves the snapshot its `13·ΔAC` after `max gst 0`, at any vote binding and
contract, under two coefficient fits. Its two instances:

* `goldilocks_preparation_premises_supply`: at the horizon, the preparation row;
* `goldilocks_deadlinePremisesSupply`: at the exact final deadline, restricted to the honest sets
  truncated after it (`premises_restrict_truncH`), the deadline row. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] (S : Setup) {E : Env V}
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Premises of a healthy Goldilocks run at a bound within its horizon, at any vote binding and
contract.** Under `β ≤ 1/3`, a valid collision-free run healthy from `gst` meets every `Premises`
field at every `b ≤ horizon` with `max gst 0 + 13·ΔAC ≤ b`, for a release schedule of gap `R`
at the release hold `R·ΔAC` and the FG delay `ΔFG + R·ΔAC` (`R = 0` is the hold-0 form). The
service is the healthy service through `b`; wakefulness, faults and committee counts are the
horizon's restricted to `b`; restarts are bounded on the whole run, since every call is within
the horizon. The timeout fit is the coefficient bound `fgDelay + 6 + R ≤ 4·δt`; the snapshot reserve
is `13·ΔAC`, since `c_z + Δ ≤ ḡ + 13Δ`. -/
theorem goldilocks_premises_at (hv : rho.ExecutionValid) (K : Contract ProgressReq) {R : ℕ}
    (hgap : ReleaseGapAt (S.params (Model.pubOf E) hn).toParams (S.release (Model.pubOf E)) R 0)
    (hβ : K.params.β ≤ 1 / 3) (hfg : K.params.fgDelay + 6 + R ≤ 4 * S.δt)
    (hnc : ¬ rho.HashCollision) {gst b : Time}
    (hH : (Sys (goldilocks S) V).Healthy (shapeProgress (goldilocks S) V).toExternal K gst
      ⟨E, rho⟩)
    (hb : b ≤ rho.horizon) (hsnap : max gst 0 + 13 * E.ΔAC ≤ b) :
    Generic.Premises (goldilocksRunMap S rho hn hv).trace (goldilocksRunMap S rho hn hv).honest
      (goldilocksRunMap S rho hn hv).committee K.params.βK
      (goldilocksRunMap S rho hn hv).proposer (goldilocksRunMap S rho hn hv).digest
      (goldilocksRunMap S rho hn hv).signer gst (E.ΔFG + (R : Time) * E.ΔAC) b
      ((R : Time) * E.ΔAC) := by
  classical
  simp only [goldilocksRunMap_trace, goldilocksRunMap_honest, goldilocksRunMap_committee,
    goldilocksRunMap_digest]
  obtain ⟨hps, hon, hΔF, hcom⟩ := hH
  let sp := S.params (Model.pubOf E) hn
  have hΔ0 : 0 < E.ΔAC := E.ΔAC_pos
  have hb0 : 0 ≤ b := by linarith [le_max_right gst 0]
  have hR0 : (0 : Time) ≤ (R : Time) * E.ΔAC := mul_nonneg (Nat.cast_nonneg _) hΔ0.le
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hncr := noCollRun_simTraceAt S rho hn hv hnc
  have haw := Obligations.Growing.healthy_preparation_awake_at (S := S) ⟨E, rho⟩ hn le_rfl hon
  have hf := Obligations.Growing.healthy_preparation_faults_at (S := S) ⟨E, rho⟩ hn hβ le_rfl hon
  have hne : (honestKeysAt S rho b).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hh := hf _ hb0 hb
    rw [h, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hh
    have := sp.toParams.hn
    change 0 < sp.n at this
    change 3 * sp.n ≤ sp.n - 1 at hh
    omega
  have hgrid : ∀ s : Nat, sp.toParams.slotTime s = (s : Time) * (4 * sp.toParams.Δ) := fun s => by
    rw [sp.slotTime_eq]
    ring
  have hsnap' : ∃ k, Healing.FirstCutAfter (simTraceAt S rho hn) k (Healing.cutZ sp.toParams gst) ∧
      (simTraceAt S rho hn).time k ≤ b := by
    have haw' : ∀ y ∈ honestKeysAt S rho b, ∀ t, AC.gbar gst ≤ t →
        t ≤ b → ((simTraceAt S rho hn).upTo b).awake y t :=
      fun y hy t ht htb => ⟨haw y t (hrun.antitone htb hy) ht (htb.trans hb), htb⟩
    have hcz := Healing.cutZ_le (sp := sp) gst
    exact Healing.snapshot_of_awake (hrun.upTo hb0).toLocalRun haw' hne (by
      unfold AC.gbar at hcz
      change _ ≤ max gst 0 + 12 * E.ΔAC at hcz
      change Healing.cutZ _ gst + E.ΔAC ≤ b
      linarith)
  refine
    { committee := fun t d ht htb hd hdb hne =>
        committeeFaultsUpTo_of_healthyOn S rho hn hv hcom t d ht (htb.trans hb) hd
          (hdb.trans hb) hne
      noColl := hncr
      sync := by
        have hs := Obligations.Growing.healthy_preparation_service_at (S := S) ⟨E, rho⟩ hn hv hnc
          hb hps (Obligations.Growing.signed_row_service_psync_at S rho hn hv hgap)
          (fun _ v t h₁ h₂ h₃ => hon.2 v t h₁ (h₂.trans hb) h₃)
          (by rw [Obligations.protoFGDelay_eq]; exact add_pos_of_pos_of_nonneg E.ΔFG_pos hR0)
          (by rw [Obligations.protoFGDelay_eq]; exact le_add_of_nonneg_left E.ΔFG_pos.le)
        rw [Obligations.protoFGDelay_eq] at hs
        exact Healing.Growing.ResetService.toService hs
      awake := fun y t hy hg htb => haw y t hy hg (htb.trans hb)
      faults := fun t ht htb => hf t ht (htb.trans hb)
      catchUp := Obligations.Growing.catchRun_of_psync_at S rho hn hv hncr
        ((Model.sysOf_delivers_iff _ _ _ _).mp hps) fun v u hu hub _ hvf =>
          hon.2 v u hu hub hvf
      noRestart := fun y k hy hk => by
        have hnr := Obligations.Growing.healthy_preparation_noRestart_at (S := S) ⟨E, rho⟩ hn hv
          le_rfl hon
        obtain ⟨ℓ, hc, _⟩ := hk
        exact Healing.Growing.noRestartUpTo_iff.mp hnr y k hy ⟨ℓ, hc, ‹_›⟩
          (Obligations.Growing.isCall_time_le_horizon S rho hn hv ⟨_, hc⟩)
      timeoutDelay := (Generic.timeout_grid_equation _ hgrid).mpr (by
        have hfg' : ((K.params.fgDelay : Nat) + 6 + R : Time) ≤ 4 * (S.δt : Time) := by
          exact_mod_cast hfg
        have hm := mul_le_mul_of_nonneg_right hfg' hΔ0.le
        have hF : E.ΔFG ≤ (K.params.fgDelay : Time) * E.ΔAC := hΔF
        change 6 * E.ΔAC + (E.ΔFG + (R : Time) * E.ΔAC) ≤ 4 * E.ΔAC * (S.δt : Time)
        linarith)
      slotLen := Generic.slotLen_of_grid hgrid
      snapshot := hsnap'
      nonempty := hne }

/-- **Preparation premises of a healthy Goldilocks run, at any vote binding and contract.**
Under `HealthyBetaFit K`, a valid collision-free run healthy from `gst` with nonfinal progress up
to a heal point within the horizon meets every `Premises` field at the horizon
(`goldilocks_premises_at`). The snapshot reserve is `13 ≤ heal`. -/
theorem goldilocks_preparation_premises_supply (hv : rho.ExecutionValid) (K : Contract ProgressReq)
    {R : ℕ}
    (hgap : ReleaseGapAt (S.params (Model.pubOf E) hn).toParams (S.release (Model.pubOf E)) R 0)
    (hfg : K.params.fgDelay + 6 + R ≤ 4 * S.δt)
    (hheal : ∀ cap idx, (cap = .available ∨ cap = .stable) → 13 ≤ K.params.heal cap idx) :
    Generic.PreparationPremisesSupply (goldilocksRunMap S rho hn hv) K ((R : Time) * E.ΔAC)
      (E.ΔFG + (R : Time) * E.ΔAC) := by
  intro hβ _ hnc cap idx gst hcap hH _ hhb
  refine goldilocks_premises_at S rho hn hv K hgap hβ hfg hnc hH le_rfl ?_
  have h13 : (13 : Time) ≤ (K.params.heal cap idx : Time) := by exact_mod_cast hheal cap idx hcap
  have hheal' : max gst 0 + (K.params.heal cap idx : Time) * E.ΔAC ≤ rho.horizon := hhb
  have := mul_le_mul_of_nonneg_right h13 E.ΔAC_pos.le
  linarith

/-- **Deadline premises of a healthy Goldilocks run, at any vote binding and contract.** Under
`β ≤ 1/3` and the timeout fit, a valid collision-free healthy run meets every `Premises` field at
the exact final deadline `d = query + latency·ΔAC ≤ horizon` (`goldilocks_premises_at`), and so on
the honest sets truncated after `d` (`premises_restrict_truncH`). The service is at the release
hold `R·ΔAC` and the FG delay `E.ΔFG + R·ΔAC`; the snapshot is witnessed by `d`,
from `13 ≤ heal` and `heal ≤ query`. -/
theorem goldilocks_deadlinePremisesSupply (hv : rho.ExecutionValid) (K : Contract ProgressReq)
    {R : ℕ}
    (hgap : ReleaseGapAt (S.params (Model.pubOf E) hn).toParams (S.release (Model.pubOf E)) R 0)
    (hβ : K.params.β ≤ 1 / 3) (hfg : K.params.fgDelay + 6 + R ≤ 4 * S.δt)
    (hheal : ∀ idx, 13 ≤ K.params.heal .final idx) :
    Generic.DeadlinePremisesSupply (goldilocksRunMap S rho hn hv) K ((R : Time) * E.ΔAC)
      (E.ΔFG + (R : Time) * E.ΔAC) := by
  intro _ hnc idx gst query hH _ hq hd _
  refine Generic.premises_restrict_truncH
    (goldilocks_premises_at S rho hn hv K hgap hβ hfg hnc hH hd ?_)
  have h13 : (13 : Time) ≤ (K.params.heal .final idx : Time) := by exact_mod_cast hheal idx
  have hq' : max gst 0 + (K.params.heal .final idx : Time) * E.ΔAC ≤ query := hq
  have := mul_le_mul_of_nonneg_right h13 E.ΔAC_pos.le
  have : (0 : Time) ≤ (K.params.latency .final idx : Time) * E.ΔAC :=
    mul_nonneg (Nat.cast_nonneg _) E.ΔAC_pos.le
  linarith

end Consensus.Goldilocks.Simulation

end
