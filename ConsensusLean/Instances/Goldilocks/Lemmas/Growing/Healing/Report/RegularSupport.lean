module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Historical counted supporters of regular writes -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A result has an earlier counted vote signed while its validator was honest, at the slot
committees `K` of a run from `K`'s committee start. The writer pool and participation bound
are read only at the update cut, where the honest members of the slot committee vote. -/
theorem result_honest_supporter_before_at
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x c s C CV) (hcb : tr.time c ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ z q, z ∈ H (tr.time q) ∧ q < c ∧ ∃ e, SA.VoteAt tr.projAC z q e ∧ e.msg ∈ CV ∧
      e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have hΔ := sp.toParams.hΔ
  have hd0 := hrun.time_nonneg c
  have hm' := hrun.time_mono
  have hpre := hrun.upTo hd0
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch hd0 hcb
  have hres' := (SA.upTo_resultAt hm').mpr ⟨le_rfl, hres⟩
  obtain ⟨ell, hu, hconf, hCV⟩ := hres'
  have ht : tr.time c = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsb : sp.ts s + sp.Δ ≤ tr.time c := by rw [ht]; linarith
  have hgs : gbar g ≤ sp.ts s := by linarith
  have hs0 : 0 < s := by
    by_contra hn
    have he : s = 0 := by omega
    rw [he] at hm
    simp only [SAParams.ts, Nat.cast_zero, mul_zero] at hm
    linarith [SA.gbar_nonneg g]
  have hsl : sp.slot (sp.ts s + sp.Δ) = s :=
    SA.slot_of_mem sp s (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  -- every honest member of the slot-`s` committee is a voter of the update's pool
  have hready : ∀ y ∈ H (tr.time c), (tr.upTo (tr.time c)).awake y (sp.ts s + sp.Δ) ∧
      (tr.upTo (tr.time c)).JoinedAt y (sp.ts s + sp.Δ) := by
    intro y hy
    refine ⟨(Trace.upTo_awake _ _ _).mpr
      ⟨hawake y _ (hrun.antitone hsb hy) (by linarith) (hsb.trans hcb), hsb⟩, ?_⟩
    intro k hk hkt
    have hk₀ := (RunTrace.upTo_restartAt tr).mp hk |>.2
    have hyt := hrun.antitone (hkt.trans hsb) hy
    change 0 < sp.slot (sp.ts s + sp.Δ) ∧
      tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s + sp.Δ) - 1)
    rw [hsl, sp.slotTime_eq]
    refine ⟨hs0, (hnr y k hyt hk₀).trans ?_⟩
    have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
    rw [hcast]
    simp only [SAParams.ts] at hm
    linarith
  have hparts := Compose.honest_participants_window_before hpre (hnc.upTo _) (K := K)
    (by rw [RunTrace.upTo_projAC]; exact SA.serviceWindowBefore_of_sync hS.sync)
    hgs hx (by rwa [RunTrace.upTo_projAC]) le_rfl hready
    (fun y hy hyK i => by
      rw [← Compose.projAC_state hpre.toLocalRun hy i]
      exact (SA.trace_mayVote_iff (Compose.goldilocks_ac_projection_from hpre
        (hnc.upTo _)).localRun hy i s).2 hyK)
    (fun v hv => hK.facts.hP.1 _ x hx c (fun _ hk => hm' hk.le) s v (by
      rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC x (fun _ hk => hm' hk.le)] at hv))
    (by
      rw [hK.facts.hsize s]
      exact hK.cs2 s hgs (by linarith) _ hd0 hcb)
  rw [RunTrace.upTo_projAC] at hparts
  obtain ⟨z, hz, q, hqc, e, he, hmem, hes, R, hR, hroot, hCR⟩ :=
    SA.result_honest_supporter_of_participants sp hS.run hx ⟨ell, hu, hconf, hCV⟩
      (B := C) .refl hparts.le
  obtain ⟨hqt, he⟩ := SA.upTo_voteAt.mp he
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg c)
  exact ⟨z, q, hrun.antitone hqt hz, hqc, e, he, hmem, hes,
    R, hsub hR, hroot, hCR.mono hsub⟩

/-- **CS at a slot committee from the service**: at a healthy observation `t ≤ b` whose previous
slot starts from `ḡ`, the faulty members of a slot committee from `ḡ` by `b` are fewer than its
members honest, awake and joined at `t`. Every validator honest at `t` is awake and joined then,
and the committee half bound leaves more than half of the committee honest at `t`. -/
theorem faultBoundK_of_service_at {K : SA.CommitteeDict sp.n} {g b : Time}
    (hK : CommitteeHalfUpTo tr H K g b) {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hnr : NoRestartAfter tr H (gbar g)) {s : Nat} (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b)
    {t : Time} (ht0 : 0 ≤ t) (hprev : gbar g ≤ sp.ts ((sp.slot t : Int) - 1)) (htb : t ≤ b) :
    SA.FaultBoundK K s tr.projAC (H t) t := by
  have hts : sp.ts ((sp.slot t : Int) - 1) ≤ t :=
    (SA.ts_le_iff_le_slot sp ht0 _).mpr (by omega)
  have hsub : K.committee s ∩ H t ⊆ K.committee s ∩
      {y | y ∈ H t ∧ tr.projAC.awake y t ∧ SA.JoinedAt tr.projAC y t} := by
    rintro y ⟨hyK, hy⟩
    refine ⟨hyK, hy, hawake y t hy (hprev.trans hts) htb, ?_⟩
    intro k hk hkt
    exact (hnr y k (hrun.antitone hkt hy) (Compose.projAC_restartAt.mp hk)).trans hprev
  have hf := hK.cs2 s hgs hsb t ht0 htb
  have hsplit : (K.committee s ∩ H t).ncard + (K.committee s ∩ (H t)ᶜ).ncard =
      sp.committeeSize := by
    rw [← hK.facts.hsize s]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
  unfold SA.FaultBoundK
  exact lt_of_lt_of_le (by omega) (Set.ncard_le_ncard hsub)

/-- The committee fault bound at `t` holds on every prefix through `d ≥ t`: the awake and joined
nodes at `t` read the same calls there. -/
theorem faultBoundK_upTo {K : SA.CommitteeDict sp.n} {s : Nat} {H' : Set (Fin sp.n)}
    {t d : Time} (htd : t ≤ d) (h : SA.FaultBoundK K s tr.projAC H' t) :
    SA.FaultBoundK K s (tr.projAC.upTo d) H' t := by
  unfold SA.FaultBoundK at h ⊢
  refine lt_of_lt_of_le h (Set.ncard_le_ncard ?_)
  rintro y ⟨hyK, hy, hw, hj⟩
  exact ⟨hyK, hy, (Trace.upTo_awake _ y t).mpr ⟨hw, htd⟩,
    fun k hk hkt => hj k ((ACTrace.upTo_restartAt (A := SA.goldilocksSA sp _ ro)).mp hk).2 hkt⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
