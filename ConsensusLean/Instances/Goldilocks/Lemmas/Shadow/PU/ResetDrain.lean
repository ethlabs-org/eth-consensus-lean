module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WindowRounds
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FullFrameWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.M1.FrameLag
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reset bound from finite service under P-U

The finite-service reset bound of the growing kernel (`exists_reset_of_drain_rounds_awake_at`
and its delayed form), with the callers' signatures, over the P-U window search
`Shadow.exists_reset` (four attempts on the shadow key `frameKey''`), and the warm-proposal
supplier `drainOutputs_of_service_at` on `FrameWindow'` windows. The core keeps the stock
prelude (the height-advance case split, the height range from the snapshot and the call lag)
and runs the four-attempt search at horizon `B - 1`, `B` the stock five-attempt bound: the
four-attempt budget is below the five-attempt one, and the reset is at most `B`. The bound
reads restarts only up to `b` (`NoRestartUpTo`) by truncating the honest sets after `b`. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

private theorem faults_lt_quorums {f n : Nat} (hn : 0 < n) (hf : 3 * f ≤ n - 1) :
    f < (2 * n + 2) / 3 ∧ f < 2 * ((2 * n + 2) / 3) - n := by
  omega

/-- A report of a node honest at its call is a block of its tree (the frame-tree half of the
stock `report_root_at`; under P-U the frame root is `Σ.F`, not the analysis root). -/
private theorem report_mem_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : AC.ToFGAt tr.projAC y i ell R) : R ∈ (tr.state y i).fg.tree := by
  have hret := hR.2.2
  change (AC.acToFG sp _ _ _).2 = some R at hret
  have hfr := (hrun.cutLaw y i (.ac ell) (Compose.projAC_callAt.mp hR.1) hy).1
  have hR' := (AC.toFG_source hret).1.1
  rw [hfr] at hR'
  exact hR'.1

/-- The reset service through `b` is one through every `T ≤ b`. -/
private theorem resetService_restrict {g ΔF b T : Time} (h : ResetService tr H g ΔF b hold)
    (hTb : T ≤ b) : ResetService tr H g ΔF T hold :=
  ⟨h.deltaF, h.message, h.block, h.relay,
    fun x i att hx hs hh y j hy hc hjT hd =>
      h.signedRow x i att hx hs hh y j hy hc (hjT.trans hTb) hd,
    h.hold_le⟩

/-- The committee half bound through `b` is one through every `T ≤ b`. -/
private theorem committeeHalf_restrict {K : AC.CommitteeDict sp.n} {g b T : Time}
    (h : CommitteeHalfUpTo tr H K g b) (hTb : T ≤ b) : CommitteeHalfUpTo tr H K g T :=
  ⟨h.facts, fun s hgs hsT d hd0 hdT => h.cs2 s hgs (hsT.trans hTb) d hd0 (hdT.trans hTb)⟩

/-- A warm-proposal supplier through `b` is one through every `T ≤ b`. -/
private theorem drainOutputs_restrict {g b T : Time} {G Ld : Nat}
    (h : Shadow.DrainOutputs tr proposer H g G Ld b) (hTb : T ≤ b) :
    Shadow.DrainOutputs tr proposer H g G Ld T where
  warm hw hm hN hNT hsig hgp := h.warm hw hm hN (hNT.trans hTb) hsig hgp

/-- Snapshot relay at the proposal call bounds a warm proposal's replay height. -/
theorem warm_proposal_height_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s₀ u : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hwarm : s₀ + 2 * sp.k ≤ u) (hub : sp.ts u ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt z kP P) (hPs : P.slot = u) :
    HZ tr H g ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + 1 := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [htime]; linarith) hz
  have hr := hrun.upTo (hrun.time_nonneg kP)
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  obtain ⟨_, ip, ell, d, pay, hc, hcall, hd, hti, hpar, _, _, _, ja, hja, hacc, hta⟩ :=
    Healing.honestProposalRun_of_proposesAt hr (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hc hd hacc
  have hip : tr.time ip = sp.ts u := hti
  have hipk : tr.time ip ≤ tr.time kP := by rw [hip, htime]
  have hzi : z ∈ H (tr.time ip) := hrun.antitone hipk hzk
  have hc' : tr.projAC.CallAt z ip ell := by
    rw [RunTrace.upTo_projAC] at hc
    exact ((Trace.upTo_callAt tr.projAC).mp hc).2
  have hframe : ell.frame = Node.frame (tr.state z ip) :=
    (hrun.cutLaw z ip (.ac ell) (Compose.projAC_callAt.mp hc') hzi).1
  have hfi : (H (tr.time ip))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf _ (hrun.time_nonneg ip) (hip ▸ hub)
    have hn := sp.toParams.hn
    change (H (tr.time ip))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨Q, hQ, hv, hroot⟩ := Healing.Growing.Shadow.full_frame_viable_witness_at hrun hnc hzi hfi
  rw [← hframe] at hQ hv hroot
  have hac := (Compose.goldilocks_ac_projection_from hr (hnc.upTo _)).localRun
  have hvd := Healing.proposal_head_viable hac hr.vstart hzk hc hcall
    (by rw [sp.slotTime_eq]; exact hti) hd
    ⟨(AC.frameIn_of_callAt hac hzk hc).1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩
  rw [hframe] at hvd
  have hfit : cutZ sp.toParams g + sp.Δ + 1 ≤ tr.time ip := by
    have hk := sp.two_le_k
    have h4 : sp.ts (s₀ + 4 : Nat) ≤ sp.ts u :=
      (AC.ts_le_iff sp).2 (by exact_mod_cast (show s₀ + 4 ≤ u by omega))
    have he : sp.ts (s₀ + 4 : Nat) = sp.ts s₀ + 16 * sp.Δ := by
      simp only [ACParams.ts]; push_cast; ring
    rw [he] at h4
    rw [hip]
    linarith [cutZ_le sp g]
  obtain ⟨hsnap, hcallZ⟩ :=
    Generic.snapshotCall_of_awake_at_from hrun.toLocalRun hawake hzi hfit (hip ▸ hub)
  have hcz : cutZ sp.toParams g ≤ tr.time ip := by linarith
  have hZ := Generic.HZ_le_hmax_at_from hrun.toLocalRun hnc hsvc.toService hcatch
    ⟨z, hrun.antitone hcz hzi⟩ hsnap hzi (by simpa only [max_eq_right hcz] using hfi)
    hcallZ (by
      have hsu : sp.ts s₀ ≤ sp.ts u := (AC.ts_le_iff sp).2 (by exact_mod_cast (by omega : s₀ ≤ u))
      rw [hip]; linarith)
  have hheight := Store.height_le_of_isViable hvd.2.2 hZ
  have hle : ∀ q < kP + 1, tr.time q ≤ tr.time kP := fun q hq => hrun.time_mono (by omega)
  have hs1 := Trace.upTo_state tr z hle
  obtain ⟨_, hPm, _⟩ := Healing.accept_of_proposesAt hr (hnc.upTo _) hzk hP'
  rw [hs1] at hPm
  have hDhist : d.head ∈ tr.HonestBlocksAt H :=
    ⟨z, ip, _, hrun.time_nonneg ip, fun q hq => hrun.time_mono hq.le, hzi, hvd.1⟩
  have hPhist : P ∈ tr.HonestBlocksAt H :=
    ⟨z, kP + 1, _, hrun.time_nonneg kP, hle, hzk, hPm⟩
  have hDP : Anc (tr.HonestBlocksAt H) d.head P := .single ⟨hDhist, hPhist, hpar⟩
  have hDpost := mem_of_honest_anc_at hrun hnc (hrun.time_nonneg kP) hle hzk hDP hPm
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg ip)
    (fun q hq => hrun.time_mono hq.le) hzi (hrun.time_nonneg kP) hle hzk hvd.1 hDpost
  rw [hσ] at hheight
  have hh := h_le_of_store_anc (fg_reachable_at hrun (hrun.time_nonneg kP) hle hzk)
    (.single ⟨hDpost, hPm, hpar⟩)
  omega

/-- Finite service supplies the frozen drain contract. The full proposal frame suffices;
no cast-time frame or signature-height restriction is needed for this lower bound. -/
theorem drainOutputs_of_service_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {G Ld : Nat} (hLd : 2 * sp.k + G ≤ Ld + 1) :
    Shadow.DrainOutputs tr proposer H g G Ld b where
  warm := by
    intro s₀ N M isTop J _ hm hN hb _ hgp
    obtain ⟨u, hlu, hhu, hz, kP, P, hP, hPs⟩ :=
      proposalGap_iff.mp hgp (s₀ + 2 * sp.k) (by omega) (by omega)
    have huN : u ≤ N := by omega
    have hts : sp.ts u ≤ sp.ts N := (AC.ts_le_iff sp).2 (by exact_mod_cast huN)
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    exact ⟨u, hlu, by omega, proposer u, kP, P, hz, rfl, hP, hPs,
      warm_proposal_height_at hrun hnc hsvc hawake hf hcatch hm hlu
        (by linarith) hz rfl hP hPs⟩

private theorem exists_reset_of_drain_rounds_noRestartAfter_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r latency t₀ : Time} {G Ld Gs : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hlat : Generic.VoteLatencyAt tr H latency) (hlat0 : 0 ≤ latency)
    (hΔF : 6 * sp.Δ + (latency + (Gs : Time) * sp.Δ) + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
      5 * (latency + (Gs : Time) * sp.Δ) ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
          5 * (latency + (Gs : Time) * sp.Δ) →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : Shadow.DrainOutputs tr proposer H g G Ld b)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ r)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
        5 * (latency + (Gs : Time) * sp.Δ) := by
  classical
  let D := sp.Δ
  let ρ : Nat := sp.toParams.fg.δt + G - 1
  let lo := r + 4 * D
  let d := 4 * D * ((Ld : Time) + 2)
  let rt := 4 * D * (ρ : Time)
  let B := Obligations.resetBoundRounds r D (2 * D) sp.toParams.fg.δt G Ld +
    5 * (latency + (Gs : Time) * sp.Δ)
  have hD : 1 ≤ D := sp.toParams.hΔ
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans sp.toParams.hΔ)
  have hρ : (ρ : Time) = (sp.toParams.fg.δt : Time) + G - 1 := by
    dsimp [ρ]
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hfq {t : Time} (ht : 0 ≤ t) (htb : t ≤ b) :
      (H t)ᶜ.ncard < sp.toParams.fg.q ∧
        (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    exact faults_lt_quorums sp.toParams.hn (hf t ht htb)
  have hczb : cutZ sp.toParams g ≤ b := by
    have hδ' : (3 : Time) ≤ sp.toParams.fg.δt := by exact_mod_cast hδ
    have hG' : (1 : Time) ≤ G := by exact_mod_cast hG
    have hLd' : (0 : Time) ≤ Ld := Nat.cast_nonneg _
    have hprod := mul_nonneg (show (0 : Time) ≤ 20 * Ld + 24 * (sp.toParams.fg.δt + G - 1) by
      linarith) (show (0 : Time) ≤ D by linarith)
    have hB : B = r + (20 * Ld + 24 * (sp.toParams.fg.δt + G - 1) + 54) * D + 5 * (2 * D)
        + 5 * (latency + (Gs : Time) * sp.Δ) := by dsimp [B]; rw [Obligations.resetBoundRounds_eq]
    linarith
  by_cases hadv : ∃ y k att, y ∈ H (max (cutZ sp.toParams g) (tr.time k)) ∧
      tr.SignAt y k att ∧ tr.time k ≤ B ∧ HZ tr H g + 1 ≤ att.h
  · obtain ⟨y, k, att, hy, hs, hk, hh⟩ := hadv
    obtain ⟨a, ha, hat⟩ := Generic.reset_of_height_advance_at_from hrun.toLocalRun
      (hfq ((hrun.time_nonneg k).trans (le_max_right _ _)) (max_le hczb (hk.trans hb))).1 hy hs hh
    exact ⟨a, ha, hat.trans hk⟩
  have hna : ∀ y k att, y ∈ H (max (cutZ sp.toParams g) (tr.time k)) → tr.SignAt y k att →
      tr.time k < B → att.h ≤ HZ tr H g := by
    intro y k att hy hs hk
    by_contra hh
    exact hadv ⟨y, k, att, hy, hs, hk.le, by omega⟩
  have hlo : gbar g + 2 * D ≤ lo := by dsimp [lo]; linarith
  have hrange : ∀ y i, y ∈ H (tr.time i) → lo ≤ tr.time i → tr.time i < B →
      HZ tr H g ≤ (tr.state y i).fg.hmax ∧
        (tr.state y i).fg.hmax ≤ HZ tr H g + 1 := by
    intro y i hy hi hiB
    have hib : tr.time i ≤ b := hiB.le.trans hb
    obtain ⟨hsnap, hcall⟩ := Generic.snapshotCall_of_awake_at_from hrun.toLocalRun hawake hy
      (hcz.trans hi) hib
    have hczle : cutZ sp.toParams g ≤ tr.time i := by
      have hDpos : 0 < D := lt_of_lt_of_le (by decide) hD
      dsimp [lo, D] at hi
      linarith
    have hmax : max (cutZ sp.toParams g) (tr.time i) = tr.time i := max_eq_right hczle
    refine ⟨Generic.HZ_le_hmax_at_from hrun.toLocalRun hnc hsvc.toService hcatch
      (hH.mono (hrun.antitone (hczle.trans hib))) hsnap hy ?_ hcall (hlo.trans hi),
      Generic.hmax_le_of_noAdvance_at_from hrun.toLocalRun hna hy
        (by rw [hmax]; exact (hfq (hrun.time_nonneg i) hib).1) hiB⟩
    rw [hmax]
    exact (hfq (hrun.time_nonneg i) hib).2
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hrt : 0 ≤ rt := by dsimp [rt]; positivity
  let slack := 2 * D - 1 + (latency + (Gs : Time) * sp.Δ)
  have hlen := riseLen_nonneg hd hrt (show 0 ≤ slack by dsimp [slack]; linarith) (HZ tr H g)
  have hsum : lo + ∑ j ∈ Finset.range 5,
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) = B - 5 := by
    rw [sum_riseLen]
    dsimp [lo, d, rt, slack, B]
    rw [Obligations.resetBoundRounds_eq, hρ]
    ring
  have hlam : (0 : Time) ≤ 2 * D := by linarith only [hD]
  have hsub4 : ∑ j ∈ Finset.range 4,
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) ≤
      ∑ j ∈ Finset.range 5,
      (riseLen d rt slack (HZ tr H g) (2 * HZ tr H g + j) + 2 * D) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => add_nonneg (hlen _) hlam)
  have hBb : B ≤ b := hb
  -- the four-attempt search at horizon `B - 1`: every premise read below `B`
  obtain ⟨a, ha, hab⟩ := Healing.Growing.Shadow.exists_reset (b := B - 1) hrun hnc
    (fun t ht htb => hf t ht (by linarith)) (resetService_restrict hsvc (by linarith))
    (fun y t hy hg ht => hawake y t hy hg (by linarith)) hcatch hnr
    (hH.mono fun _ hy => hrun.antitone (by linarith) hy) hδ hG hlat hlat0 hΔF
    (by dsimp [lo]; linarith) (by dsimp [lo, D]; linarith)
    (fun y i hy hi hiB => hrange y i hy hi (by linarith))
    (fun z i m hz hi him hm => Generic.callLag_of_awake_at_from hrun.toLocalRun hawake
      (by dsimp [lo, D]; linarith) hz hi him (by linarith))
    (by
      have h4 := hsub4
      dsimp only [d, rt, slack, D, ρ] at h4 hsum ⊢
      linarith)
    (fun w k att hw hs hk => hna w k att hw hs (by linarith))
    (fun s₀ N hs₀ hN => hgp s₀ N hs₀ (by dsimp [B] at hN ⊢; linarith))
    (drainOutputs_restrict hdrain (by linarith)) hcal hgap (by dsimp [lo]; linarith) hδG
    (committeeHalf_restrict hK (by linarith))
  exact ⟨a, ha, by linarith⟩

/-! ### Truncation after `b`

The honest sets truncated after `b` (`Generic.truncH`) keep every honesty read up to `b` and drop
every later one, so a restart honest on them is at a time `≤ b`, where `NoRestartUpTo` bounds it.
The run-independent facts are the generic ones (`Lemmas/Generic/HealingLeaves`). -/

open Generic (truncH truncH_eq_of_le honestBlocksAt_truncH_subset catchRun_truncH
  HZ_truncH isReset_truncH_iff)

/-- The local run laws transfer by `LocalRun.truncH`; the Goldilocks-specific laws preserve the
same starts and the genesis root. -/
theorem goldilocksRun_truncH {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (b : Time) :
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg (truncH H b) tr ini where
  toLocalRun := hrun.toLocalRun.truncH b
  vstart := hrun.vstart
  genesis_root_ok := hrun.genesis_root_ok

/-- Committee facts survive truncating honesty after `b`: the sizes do not read honesty, and P
and the gate read it only in hypotheses, where the truncation is a subset of `H`. -/
theorem _root_.Consensus.Goldilocks.Compose.Growing.CommitteeFacts.truncH
    {K : AC.CommitteeDict sp.n} (hK : Compose.Growing.CommitteeFacts tr H K) (b : Time) :
    Compose.Growing.CommitteeFacts tr (truncH H b) K where
  hsize := hK.hsize
  hP := ⟨fun t y hy i hi s v hv => hK.hP.1 t y hy.1 i hi s v hv,
    fun y i ℓ A hy hO s v hv => hK.hP.2 y i ℓ A hy.1 hO s v hv⟩
  hGate t ht x hx := hK.hGate t ht x hx.1

/-- The committee half bound through `b` survives truncating honesty after `b`: CS2 reads honesty
only at times `≤ b`, where the truncation is `H` itself. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.CommitteeHalfUpTo.truncH
    {K : AC.CommitteeDict sp.n} {g b : Time} (hK : CommitteeHalfUpTo tr H K g b) :
    CommitteeHalfUpTo tr (truncH H b) K g b :=
  ⟨hK.facts.truncH b, fun s hgs hsb d hd0 hdb => by
    rw [truncH_eq_of_le hdb]
    exact hK.cs2 s hgs hsb d hd0 hdb⟩

private theorem resetService_truncH {g ΔF b' hold : Time} (hs : ResetService tr H g ΔF b' hold)
    (b : Time) : ResetService tr (truncH H b) g ΔF b' hold where
  deltaF := hs.deltaF
  message x i m hx hm y j hy := hs.message x i m hx.1 hm y j hy.1
  block x i B hx hB y j hy := hs.block x i B hx.1 hB y j hy.1
  relay x i B hx hB hg y j hy hj hd hF :=
    hs.relay x i B hx.1 hB hg y j hy.1 hj hd (Anc.mono (honestBlocksAt_truncH_subset b) hF)
  signedRow x i att hx hsg hxh y j hy :=
    hs.signedRow x i att hx.1 hsg (fun k hk hs' ht h0 => (hxh k hk hs' ht h0).1) y j hy.1
  hold_le := hs.hold_le

private theorem proposalGap_truncH {G s₀ N : Nat} {b : Time}
    (hgp : ProposalGap tr H proposer G s₀ N) (hN : sp.ts N + sp.Δ ≤ b) :
    ProposalGap tr (truncH H b) proposer G s₀ N := by
  rw [proposalGap_iff] at hgp ⊢
  intro a ha haN
  obtain ⟨x, hax, hxa, hx, hP⟩ := hgp a ha haN
  have hts : sp.ts x ≤ sp.ts N := (AC.ts_le_iff sp).2 (by exact_mod_cast (show x ≤ N by omega))
  exact ⟨x, hax, hxa, ⟨hx, by linarith⟩, hP⟩

private theorem proposalGap_of_truncH {G s₀ N : Nat} {b : Time}
    (hgp : ProposalGap tr (truncH H b) proposer G s₀ N) : ProposalGap tr H proposer G s₀ N := by
  rw [proposalGap_iff] at hgp ⊢
  intro a ha haN
  obtain ⟨x, hax, hxa, hx, hP⟩ := hgp a ha haN
  exact ⟨x, hax, hxa, hx.1, hP⟩

private theorem frameWindow_of_truncH {lo hi b : Time} {M : Nat} {isTop : Prop}
    {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hw : FrameWindow' tr (truncH H b) lo hi M isTop J)
    (hhi : hi ≤ b) : FrameWindow' tr H lo hi M isTop J :=
  ⟨fun y i hy hl hh => hw.M_eq y i ⟨hy, hh.trans hhi⟩ hl hh,
    fun y i hy hl hh => hw.top_iff y i ⟨hy, hh.trans hhi⟩ hl hh,
    fun y i hy hl hh => hw.root_eq y i ⟨hy, hh.trans hhi⟩ hl hh⟩

private theorem drainOutputs_truncH {g b : Time} {G Ld : Nat}
    (hd : Shadow.DrainOutputs tr proposer H g G Ld b) (hcz : cutZ sp.toParams g ≤ b) :
    Shadow.DrainOutputs tr proposer (truncH H b) g G Ld b where
  warm := by
    intro s₀ N M isTop J hw hm hN hmb hsig hgp
    obtain ⟨u, hu, huL, z, kP, P, hz, hdes, hP, hPs, hh⟩ :=
      hd.warm (frameWindow_of_truncH hw hmb) hm hN hmb
        (fun v k att hv hs hk => by
          have h := hsig v k att ⟨hv, max_le hcz (hk.trans hmb)⟩ hs hk
          rwa [HZ_truncH hcz] at h)
        (proposalGap_of_truncH hgp)
    have hts : sp.ts u ≤ sp.ts N := (AC.ts_le_iff sp).2 (by exact_mod_cast (show u ≤ N by omega))
    have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
    refine ⟨u, hu, huL, z, kP, P, ⟨hz, by linarith⟩, hdes, hP, hPs, ?_⟩
    rwa [HZ_truncH hcz]

/-- **The delayed reset bound from finite service**, reading restarts only up to `b`: the rounds of
`exists_reset_of_drain_rounds_noRestartAfter_at` run on the honest sets truncated after `b`, where
the premises up to `b` are those for `H`, no restart is honest after `b`, and `H_z` and the reset
are those for `H` (`c_z` and the reset bound are `≤ b`). -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.exists_reset_of_drain_rounds_awake_within_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r latency t₀ : Time} {G Ld Gs : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hlat : Generic.VoteLatencyAt tr H latency) (hlat0 : 0 ≤ latency)
    (hΔF : 6 * sp.Δ + (latency + (Gs : Time) * sp.Δ) + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
      5 * (latency + (Gs : Time) * sp.Δ) ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
          5 * (latency + (Gs : Time) * sp.Δ) →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : Shadow.DrainOutputs tr proposer H g G Ld b)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ r)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
        5 * (latency + (Gs : Time) * sp.Δ) := by
  have hΔ : 1 ≤ sp.Δ := sp.toParams.hΔ
  have hlo : r + 4 * sp.Δ ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ)
      sp.toParams.fg.δt G Ld := by
    rw [Obligations.resetBoundRounds_eq]
    have hc : (0 : Time) ≤ 20 * (Ld : Time) + 24 * ((sp.toParams.fg.δt : Time) + G - 1) := by
      have h1 : (0 : Time) ≤ Ld := Nat.cast_nonneg _
      have h2 : (0 : Time) ≤ sp.toParams.fg.δt := Nat.cast_nonneg _
      have h3 : (1 : Time) ≤ G := by exact_mod_cast hG
      linarith
    linarith [mul_nonneg hc (show (0 : Time) ≤ sp.Δ by linarith)]
  have hGs0 : (0 : Time) ≤ (Gs : Time) * sp.Δ :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans sp.toParams.hΔ)
  have hczb : cutZ sp.toParams g ≤ b := by linarith
  have hlat' : Generic.VoteLatencyAt tr (truncH H b) latency := by
    refine ⟨fun y i R hR hy => ?_⟩
    obtain ⟨k, hik, hk, C, s, hc, hh, hRC, j, hij, hjk, ell, hcall, hto, hret⟩ :=
      hlat.attests y i R hR hy.1
    have hjb := (hrun.time_mono hjk).trans (hk.trans hy.2)
    have hyj := hrun.antitone (hrun.time_mono hjk |>.trans hk) hy.1
    have hC : AC.ToFGAt tr.projAC y j ell C :=
      ⟨Compose.projAC_callAt.mpr hcall, hto, by
        change (AC.acToFG sp (tr.projAC.state y j) ell.frame (tr.time j)).2 = some C
        rw [Compose.Growing.projAC_state_at hrun hyj]
        exact hret⟩
    have hle : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrun.time_mono hq.le
    have hj0 := hrun.time_nonneg j
    have hlocal := store_anc_of_honest_anc_at hrun hnc hj0 hle hyj hRC
      (report_mem_at hrun hyj hC)
    exact ⟨k, hik, hk, C, s, hc, hh,
      honest_anc_of_store_anc_at (H := truncH H b) hj0 hle ⟨hyj, hjb⟩ hlocal,
      j, hij, hjk, ell, hcall, hto, hret⟩
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_rounds_noRestartAfter_at
    (goldilocksRun_truncH hrun b) hnc
    (fun t ht htb => by rw [truncH_eq_of_le htb]; exact hf t ht htb)
    (resetService_truncH hsvc b) (fun y t hy => hawake y t hy.1) (catchRun_truncH hcatch b)
    (fun y k hy hk => noRestartUpTo_iff.mp hnr y k hy.1 hk hy.2)
    (hH.mono fun _ hy => ⟨hy, le_rfl⟩) hδ hlat' hlat0 hΔF hr hgr hG hcz hb
    (fun s₀ N hs₀ hN => proposalGap_truncH (hgp s₀ N hs₀ hN) (by linarith))
    (drainOutputs_truncH hdrain hczb)
    (sign := sign) (fun y j t x fgDue hy hg => hcal y j t x fgDue hy.1 hg)
    hgap ht₀ hδG hK.truncH
  exact ⟨a, (isReset_truncH_iff hczb (hab.trans hb)).mp ha, hab⟩

/-- Finite-service reset with same-tick vote latency: the bound keeps the five signing gaps. -/
theorem _root_.Consensus.Goldilocks.Healing.Growing.exists_reset_of_drain_rounds_awake_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b r t₀ : Time} {G Ld Gs : Nat}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    (hH : (H b).Nonempty) (hδ : 3 ≤ sp.toParams.fg.δt)
    (hΔF : 6 * sp.Δ + (Gs : Time) * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.fg.δt : Time))
    (hr : 0 ≤ r) (hgr : gbar g ≤ r) (hG : 1 ≤ G)
    (hcz : cutZ sp.toParams g + sp.Δ + 1 ≤ r + 4 * sp.Δ)
    (hb : Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
      5 * ((Gs : Time) * sp.Δ) ≤ b)
    (hgp : ∀ s₀ N : Nat, r + 4 * sp.Δ ≤ sp.ts s₀ →
      sp.ts N + 2 * sp.Δ <
        Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
          5 * ((Gs : Time) * sp.Δ) →
      ProposalGap tr H proposer G s₀ N)
    (hdrain : Shadow.DrainOutputs tr proposer H g G Ld b)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign Gs t₀) (ht₀ : t₀ ≤ r)
    (hδG : 3 + (Gs + 3) / 4 ≤ sp.toParams.fg.δt)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ a, IsReset tr H g a ∧
      a ≤ Obligations.resetBoundRounds r sp.Δ (2 * sp.Δ) sp.toParams.fg.δt G Ld +
        5 * ((Gs : Time) * sp.Δ) := by
  simpa only [zero_add] using exists_reset_of_drain_rounds_awake_within_at hrun hnc
    hf hsvc hawake hcatch hnr hH hδ (Generic.voteLatency_zero_from hrun.toLocalRun) le_rfl
    (by simpa only [zero_add] using hΔF) hr hgr hG hcz
    (by simpa only [zero_add] using hb)
    (by simpa only [zero_add] using hgp) hdrain hcal hgap ht₀ hδG hK

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
