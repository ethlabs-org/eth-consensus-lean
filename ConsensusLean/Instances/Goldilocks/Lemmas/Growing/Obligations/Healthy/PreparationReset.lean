module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyPreparationTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Supply.Fields
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.BoundariesCover
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The finite reset envelope of a growing healthy query -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **A high-source cover supplier of a healthy query** (the `hcover` of
`resetPremisesUpTo_of_reset_cover_at` at the query's bound): from every reset record up to `T` at
most the bound, inside the deep quarantine, with the drain of its reset `4Δ` before `T`, the
high-source cover through the bound. Supplied above Continuation (`healthy_query_cover_at`). -/
abbrev HealthyQueryCover (Q : HealthyPreparationQueryAt S A V) : Prop :=
  ∀ a T, Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst
      (protoFGDelay (Model.pubOf Q.run.1) + (A.releaseGap : Time) * Q.params.Δ) a T
      (runCommittee S Q.run.2 Q.hn) (K S A).params.βK ((A.releaseGap : Time) * Q.params.Δ) →
    (∀ D, Q.params.deepDepth = some D →
      T ≤ Healing.cutZ Q.params.toParams Q.gst + 4 * D * Q.params.Δ) →
    Healing.drainTime Q.params a + 4 * Q.params.Δ ≤ T → T ≤ Q.bound →
    Healing.Growing.HighSourceCover Q.trace Q.keys Q.gst a Q.bound

/-- The parameter-only healing coefficient covers the reset envelope. -/
theorem healthy_preparation_reset_fit_at
    (Q : HealthyPreparationQueryAt S A V) :
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
theorem healthy_preparation_reset_at
    (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index Q.ready Q.heal Q.run)
    {sign : Fin Q.params.n → Time → Bool}
    (hcal : Q.trace.SignCalendarAt (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys sign)
    {Gs : Nat} (hgap : SignGapAt Q.params.toParams sign Gs 0)
    (hδG : 3 + (Gs + 3) / 4 ≤ Q.params.toParams.fg.δt)
    (hGs : (contract_catchUp S A : Nat) +
        (healthyResetCoeff S Q.index + 8 * S.k + 4 * (Q.index : Nat) + 34) + 3 + 5 * Gs ≤
      contract_heal S A Q.cap Q.index)
    (hGsT : 4 * A.fgSlots + A.releaseGap + Gs ≤ 4 * S.δt)
    (hcover : HealthyQueryCover S A V Q) :
    ∃ ΔF a, Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn)
        (digestOf S Q.run.2) Q.gst ΔF a Q.bound
        (runCommittee S Q.run.2 Q.hn) (K S A).params.βK
        ((A.releaseGap : Time) * Q.params.Δ) ∧
      a ≤ Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        (healthyResetSlack S Q.index : Time) + 5 * ((Gs : Time) * Q.params.Δ) := by
  classical
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hRΔ : (0 : Time) ≤ (A.releaseGap : Time) * Q.params.Δ :=
    mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have htimeoutG : 6 * Q.params.Δ + (Gs : Time) * Q.params.Δ +
      (protoFGDelay (Model.pubOf Q.run.1) + (A.releaseGap : Time) * Q.params.Δ) ≤
      4 * Q.params.Δ * (Q.params.toParams.fg.δt : Time) := by
    have hd := protoFGDelay_delivery_of_fgDelay S A V Q.run Q.hn Q.healthy.2.2
    have hc : (4 : Time) * A.fgSlots + A.releaseGap + Gs ≤ 4 * S.δt := by exact_mod_cast hGsT
    have hG : (0 : Time) ≤ (Gs : Time) * Q.params.Δ := mul_nonneg (Nat.cast_nonneg _) hΔ.le
    change 6 * Q.params.Δ + _ ≤ 4 * Q.params.Δ * (A.fgSlots : Time) at hd
    rw [hδeq]
    nlinarith only [hd, hc, hΔ, hG, hRΔ, mul_le_mul_of_nonneg_right hc hΔ.le]
  have htimeout : 6 * Q.params.Δ + (protoFGDelay (Model.pubOf Q.run.1) +
      (A.releaseGap : Time) * Q.params.Δ) ≤ 4 * Q.params.Δ * (Q.params.toParams.fg.δt : Time) := by
    have hG : (0 : Time) ≤ (Gs : Time) * Q.params.Δ := mul_nonneg (Nat.cast_nonneg _) hΔ.le
    linarith only [htimeoutG, hG]
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  have hstart := simIni_eq_runStart S Q.run.2 Q.hn Q.valid ▸ hrun
  have hcf := committeeFaultsUpTo_of_healthyOn S Q.run.2 Q.hn Q.valid Q.committeeHealthy
  have hβ : (K S A).params.βK ≤ 1 / 2 := by rw [goldilocksContract_params_eq]; exact le_rfl
  have hs := healthy_preparation_service_at Q.run Q.hn Q.valid Q.noCollision Q.bound_le
    Q.healthy.1 (signed_row_service_psync_at S Q.run.2 Q.hn Q.valid
      (Obligations.releaseGapAt_of_assumptions A _ Q.hn)) (fun _ => Q.healthy.2.1.2)
    (add_pos_of_pos_of_nonneg (protoFGDelay_pos _) hRΔ)
    (le_add_of_nonneg_left (protoFGDelay_pos _).le)
  have haw := healthy_preparation_awake_at Q.run Q.hn Q.bound_le Q.healthy.2.1
  have hf : ∀ t, 0 ≤ t → t ≤ Q.bound → 3 * (Q.keys t)ᶜ.ncard ≤ Q.params.n - 1 :=
    healthy_preparation_faults_at Q.run Q.hn
      (by rw [goldilocksContract_params_eq]; norm_num [Params.standard]) Q.bound_le Q.healthy.2.1
  have hfit := healthy_preparation_reset_fit_at S A V Q
  have hready : Q.ready =
      max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 := rfl
  have hcDur : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run :=
    mul_nonneg (Int.natCast_nonneg _) Q.run.1.ΔAC_pos.le
  have hr0 : 0 ≤ Q.ready := by rw [hready]; linarith only [le_max_right Q.gst 0, hcDur]
  have hgr : AC.gbar Q.gst ≤ Q.ready := by
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
  have hR : (24 : Time) ≤ healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith only [Nat.cast_nonneg (α := Time) (healthyDrainLen S Q.index)]
  have hr : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  have hGD : (0 : Time) ≤ (Gs : Time) * Q.params.Δ := mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hBGh : Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      5 * ((Gs : Time) * Q.params.Δ) ≤ Q.heal := by
    have hm := healthy_heal_margin S A V Q.run Q.hn Q.cap Q.index Q.gst
      (M := healthyResetCoeff S Q.index + 8 * S.k + 4 * (Q.index : Nat) + 34 + 5 * Gs)
      (by omega)
    have hk0 : (0 : Time) ≤ (S.k : Time) * Q.params.Δ := mul_nonneg (Nat.cast_nonneg _) hΔ.le
    have hX0 : (0 : Time) ≤ ((Q.index : Nat) : Time) * Q.params.Δ :=
      mul_nonneg (Nat.cast_nonneg _) hΔ.le
    change Q.ready + _ * Q.params.Δ + 2 ≤ Q.heal at hm
    push_cast at hm
    nlinarith only [hm, hk0, hX0, hΔ, hGD]
  have hBh : Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ ≤ Q.heal := by
    linarith only [hBGh, hGD]
  have h4B : Q.ready + 4 * Q.params.Δ ≤ Q.heal := by
    have := mul_le_mul_of_nonneg_right hR hΔ.le
    linarith only [this, hfit, hr, hΔ]
  have hcatch := healthy_repair_catch_at S A V Q
      (by linarith only [hgr, h4B, hb, hΔ])
  have hnr := healthy_preparation_noRestart_at Q.run Q.hn Q.valid Q.bound_le Q.healthy.2.1
  have haw' : ∀ y ∈ Q.keys Q.bound, ∀ t, AC.gbar Q.gst ≤ t →
      t ≤ Q.bound → (Q.trace.upTo Q.bound).awake y t := by
    intro y hy t ht htb
    exact ⟨haw y t (hrun.antitone htb hy) ht htb, htb⟩
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake (hrun.upTo hb0).toLocalRun haw' hH
    (by linarith only [hcz, h4B, hb])
  -- the reset of the healing supplier, under latency `0`
  have hgrid : ∀ s : Nat, Q.params.toParams.slotTime s = (s : Time) * (4 * Q.params.Δ) :=
    fun s => by rw [Q.params.slotTime_eq]; ring
  obtain ⟨R, O, hRd, hW, -, hG, -⟩ := Generic.goldilocks_ac_healing (sp := Q.params)
    (sign := sign) (G := Gs) (Rg := A.releaseGap) hδG
  have hRun : R.Run (runCommittee S Q.run.2 Q.hn) (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2) Q.keys Q.trace := by
    rw [hRd.1]
    exact ⟨hstart, S.committeeSize_pos _ Q.hn, runCommittee_ncard S Q.run.2 Q.hn Q.valid,
      runCommittee_facts S Q.run.2 Q.hn Q.valid, hcal, hgap⟩
  have hPr := Generic.premises_truncH (b := Q.bound)
    (sg := fun v : (goldilocksNode Q.params).Msg => v.val)
    (proposer := runProposer S Q.run.2 Q.hn) hcf hnc
    ⟨hs.deltaF, hs.message, hs.block, hs.relay, hs.signedRow, hs.hold_le⟩ haw hf hcatch
    (fun y k hy hr hk => Healing.Growing.noRestartUpTo_iff.mp hnr y k hy hr hk)
    ((Generic.timeout_grid_equation _ hgrid).mpr htimeout) (Generic.slotLen_of_grid hgrid)
    ⟨j, hj, hjt⟩ hH
  -- the supplier's four-attempt bound is within the reset coefficient
  have hB4 : Q.ready + (16 * (healthyDrainLen S Q.index : Time) +
      24 * ((Q.params.toParams.δt + (Q.index : Nat) - 1 : Nat) : Time) + 52) * Q.params.Δ +
      4 * (0 + (Gs : Time) * Q.params.Δ) ≤
      Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        4 * ((Gs : Time) * Q.params.Δ) := by
    have hX := Q.index.1.pos
    have hρ : ((Q.params.toParams.δt + (Q.index : Nat) - 1 : Nat) : Time) =
        (S.δt : Time) + ((Q.index : Nat) : Time) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; rfl
    have hL0 : (0 : Time) ≤ (healthyDrainLen S Q.index : Time) * Q.params.Δ := by positivity
    rw [hρ, healthyResetCoeff_val]
    push_cast
    nlinarith only [hL0, hΔ]
  obtain ⟨a, ha, hab⟩ := Generic.exists_reset_within O (Gp := (Q.index : Nat))
    (L := healthyDrainLen S Q.index) hβ hgrid hRun hPr
    (Generic.voteLatency_zero_from (R.run_local hRun)) le_rfl
    (by rw [hG, zero_add]; exact htimeoutG) Q.index.1.pos
    (by rw [hW, healthyDrainLen_val]; change 2 * S.k + _ ≤ 2 * S.k + _ + 1; omega) hgr hcz
    (fun s₀ N hs₀ hN => by
      rw [hG] at hN
      intro c hc hcN
      obtain ⟨x, hxl, hxr, k, P, hx, hP, _, hPs⟩ := healthy_preparation_gap_at S A V
        Q.run Q.hn Q.valid Q.noCollision Q.nonfinal
        (hb.trans Q.bound_le) hp
        (by rw [max_eq_left hr0]; exact hs₀)
        (by
          rw [Q.params.slotTime_eq] at hN
          simp only [AC.ACParams.ts]
          linarith only [hN, hB4, hBGh, hGD, hΔ]) c hc hcN
      exact ⟨x, hxl, hxr, hx, k, P, hP, hPs⟩)
    (by rw [hG]; linarith only [hB4, hBGh, hb, hGD])
  rw [hG] at hab
  replace hab : a ≤ Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      5 * ((Gs : Time) * Q.params.Δ) := by linarith only [hab, hB4, hGD]
  have ha0 : 0 ≤ a := by
    obtain ⟨⟨_, k, _, _, _, _, hka⟩, _⟩ := ha
    rw [← hka]; exact hrun.time_nonneg k
  -- the drain of the reset ends before the deep quarantine (`DeepAdmits` of the index)
  have hdrain : ∀ D, Q.params.deepDepth = some D →
      Healing.drainTime Q.params a + 4 * Q.params.Δ ≤
        Healing.cutZ Q.params.toParams Q.gst + 4 * D * Q.params.Δ := by
    intro D hD
    have hadm := Q.index.2 D hD
    rw [healMargin_val, healthyDrainLen_val] at hadm
    have hadm' : ((11 + (20 * (2 * S.k + (Q.index.1 : Nat)) + 8 * S.k + 28 * S.δt +
        28 * (Q.index.1 : Nat) + 56 + 5 * A.signGap) : Nat) : Time) ≤ ((4 * D : Nat) : Time) := by
      exact_mod_cast hadm
    push_cast at hadm'
    have hready' : Q.ready =
        max Q.gst 0 + ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC + 1 := by
      change max Q.gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * Q.run.1.ΔAC +
        1 = _
      rw [contract_coefficients_catchUp]
    rw [contract_catchUp_val] at hready'
    have hDe : Q.params.Δ = Q.run.1.ΔAC := rfl
    have hz := Healing.lt_cutZ Q.params Q.gst
    have hsa : Q.params.ts (Q.params.slot a : Int) ≤ a :=
      (AC.ts_le_iff_le_slot Q.params ha0 _).2 le_rfl
    have hdr : Healing.drainTime Q.params a =
        Q.params.ts (Q.params.slot a : Int) + 4 * Q.params.Δ * (2 * (Q.params.k : Time) + 5) := by
      rw [Healing.drainTime_eq]; simp only [AC.ACParams.ts]; push_cast; ring
    have hδ6 : (6 : Time) ≤ S.δt := by exact_mod_cast A.six_le_δt
    have hX1 : (1 : Time) ≤ (Q.index.1 : Nat) := by exact_mod_cast Q.index.1.pos
    have hΔ0 : (0 : Time) ≤ Q.params.Δ := hΔ.le
    have e1 := mul_le_mul_of_nonneg_right hadm' hΔ0
    have e2 := mul_le_mul_of_nonneg_right hδ6 hΔ0
    have e3 := mul_le_mul_of_nonneg_right hX1 hΔ0
    have hGΔ : (0 : Time) ≤ (A.signGap : Time) * Q.params.Δ :=
      mul_nonneg (Nat.cast_nonneg _) hΔ0
    -- the signing wait of the reset bound is paid by the heal coefficient (`hGs`)
    have hGs' := hGs
    rw [contract_heal_val, contract_catchUp_val, healthyResetCoeff_val, healMargin_val,
      healthyDrainLen_val] at hGs'
    have hGs'' : ((19 + (20 * (2 * S.k + (Q.index.1 : Nat)) + 24 * (S.δt + (Q.index.1 : Nat)) +
        40 + 8 * S.k + 4 * (Q.index.1 : Nat) + 34) + 3 + 5 * Gs : Nat) : Time) ≤
        ((19 + (20 * (2 * S.k + (Q.index.1 : Nat)) + 8 * S.k + 28 * S.δt +
          28 * (Q.index.1 : Nat) + 56 + 5 * A.signGap) : Nat) : Time) := by
      exact_mod_cast hGs'
    push_cast at hGs''
    have e4 := mul_le_mul_of_nonneg_right hGs'' hΔ0
    have hab' := hab
    rw [healthyResetCoeff_val, healthyDrainLen_val] at hab'
    rw [hdr]
    have hkk : (Q.params.k : Time) = S.k := rfl
    rw [hready', ← hDe] at hab'
    have hmax : max Q.gst 0 = AC.gbar Q.gst := rfl
    rw [hmax] at hab'
    rw [hkk]
    push_cast at hab'
    generalize Healing.cutZ Q.params.toParams Q.gst = z at hz ⊢
    generalize Q.params.ts (Q.params.slot a : Int) = w at hsa ⊢
    have h1 : (1 : Time) ≤ Q.params.Δ := Int.add_one_le_iff.2 hΔ
    ring_nf at hab' e1 e2 e3 e4 hz hGΔ ⊢
    linarith
  refine ⟨_, a, Healing.Growing.resetPremisesUpTo_of_reset_cover_at
    hstart hnc hs haw hf ha ha0
    (hab.trans (hBGh.trans hb)) ⟨j, hj, hjt⟩ hcatch hnr
    htimeout hH
    (runCommittee_facts S Q.run.2 Q.hn Q.valid hnc)
    hβ
    (S.committeeSize_pos (Model.pubOf Q.run.1) Q.hn) hcf hdrain (hcover a), ?_⟩
  linarith only [hab, hr]

end Consensus.Goldilocks.Obligations.Growing

end
