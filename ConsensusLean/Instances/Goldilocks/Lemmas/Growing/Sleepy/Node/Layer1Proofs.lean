module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Layer1
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Concrete sleepy provenance adapters

The confirmation events are actual results and optimistic locks of the composed
Goldilocks run. No unconditional generic event-safety supplier is constructed.
-/

namespace Consensus.Goldilocks.Generic.SleepyLayer1

open SA (SAParams ReplayOrder)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

private theorem anchored_of_chain {tr : GoldilocksTrace sp ro}
    {H : Time → Set (Fin sp.n)} {b t : Time} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : OnOriginChainWithin tr H B t) (ht : t ≤ b) :
    Anchored (goldilocksEvents sp ro) tr H b t B := by
  rcases onOriginChainWithin_iff.1 h with hg | ⟨C, s, hC, hBC⟩
  · exact Or.inl hg
  obtain ⟨x, i, CV, hx, hi, he⟩ := originWithin_iff.1 hC
  exact Or.inr ⟨C, ⟨x, i, s, hx, hi, hi.trans ht,
    goldilocksEvents_confirmedEvent_iff.2 ⟨CV, he⟩⟩, hBC⟩

theorem goldilocks_output_provenance : GoldilocksOutputProvenance (sp := sp) (ro := ro) := by
  rw [goldilocksOutputProvenance_iff]
  intro cm proposer dg H tr b hrun hnc y i t hread _
  obtain ⟨hrun, -⟩ := (goldilocksRunInterface_run_iff cm).1 hrun
  obtain ⟨hy, ⟨hi, -⟩, ht0, htb⟩ := hread
  have hr := hrun.upTo ht0
  have hs := Trace.upTo_state tr y hi
  have hΦ := (Store.frame_realization _ _ _ _ (Compose.fg_reachable hr.toLocalRun hy i)).1
  rw [hs] at hΦ
  have hsub : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, i, t, ht0, hi, hy, hX.1⟩
  have hcoh := Compose.Growing.honest_blocks_coherent_local hrun.toLocalRun hnc
  have htip := (Regimes.sa_tips (A := (tr.state y i).ac) hΦ t).1
  refine ⟨htip.1, ?_⟩
  obtain ⟨R, hR, hRr, hRc⟩ := record_origin_at hrun hnc ht0 hi le_rfl hy
  have hRa : Anchored (goldilocksEvents sp ro) tr H b t R :=
    anchored_of_chain (onOriginChainWithin_iff.2
      (hRc.imp_right fun ⟨s, h⟩ => ⟨R, s, h, .refl⟩)) htb
  change Anchored (goldilocksEvents sp ro) tr H b t (SA.acConfirmed sp (tr.state y i).ac
    (Node.frame (tr.state y i)) t) ∨ Anc (tr.HonestBlocksAt H)
      (SA.acConfirmed sp (tr.state y i).ac (Node.frame (tr.state y i)) t)
      (tr.state y i).fg.F
  unfold SA.acConfirmed
  dsimp only
  cases hX : SA.deepest (Node.frame (tr.state y i))
      {X | X ∈ (Node.frame (tr.state y i)).tree ∧
        (Node.frame (tr.state y i)).Anc X
          ((SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed).getD
            (Node.frame (tr.state y i)).F) ∧
        (Node.frame (tr.state y i)).Anc X
          (SA.acHead sp (tr.state y i).ac (Node.frame (tr.state y i)) t)} with
  | none => exact Or.inr .refl
  | some X =>
    obtain ⟨hXt, hXe, -⟩ := (SA.deepest_mem hX).1
    cases hl : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
    | none =>
      rw [hl, Option.getD_none] at hXe
      exact Or.inr (hXe.mono hsub)
    | some W =>
      rw [hl, Option.getD_some] at hXe
      obtain ⟨hW, hWr⟩ := SA.lookup_eq_some hl
      have hRU : R ∈ tr.HonestBlocksAt H := ⟨y, i, t, ht0, hi, hy, hR⟩
      have hWR : W = R := hcoh.1 (hsub hW) hRU (hWr.trans hRr.symm)
      rw [hWR] at hXe
      rcases hRa with hg | ⟨E, he, hRE⟩
      · have hgmem := (Compose.FrameGeometry.honest_genesis_anc hr.toLocalRun
          (show R ∈ (tr.upTo t).HonestBlocks (H t) from ⟨y, hy, i, hs.symm ▸ hR⟩)).1
        have hgU := RunTrace.honestBlocks_upTo_subset hrun.time_mono ht0 hgmem
        obtain rfl : R = sp.toParams.genesisBlock ([], []) :=
          hcoh.1 hRU hgU hg
        rcases Relation.ReflTransGen.cases_tail hXe with rfl | ⟨Z, _, hz⟩
        · exact Or.inl (Or.inl rfl)
        · cases hz.2.2
      · exact Or.inl (Or.inr ⟨E, he, (hXe.mono hsub).trans hRE⟩)

theorem goldilocks_source_provenance : GoldilocksSourceProvenance (sp := sp) (ro := ro) := by
  rw [goldilocksSourceProvenance_iff]
  intro cm proposer dg H tr b hrun hnc y i B hy hib hreport
  obtain ⟨hrun, -⟩ := (goldilocksRunInterface_run_iff cm).1 hrun
  obtain ⟨ℓ, hc, hto, hB⟩ := hreport
  have hd := hrun.time_nonneg i
  have hr := acRun_upTo hrun hnc hd
  have hcA := Compose.projAC_callAt.2 hc
  have htoA : SA.ToFGAt tr.projAC y i ℓ B := by
    refine ⟨hcA, hto, ?_⟩
    rw [projAC_state_at hrun hy]
    exact hB
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hcA
  obtain ⟨hCv, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩, hlC, hfast, -⟩ :=
    SA.toFG_candidate htoA.2.2
  have hCe : B = ℓ.frame.viableAncestor B₀ :=
    hΦ.coherent.1 hCv.1 (SA.viableAncestor_anc hΦ hB₀).1 hlC.symm
  have hstate := projAC_upTo_state hrun (y := y) (le_refl (tr.time i))
  obtain ⟨k, hki, D, CV, hlock, L, hL, hLr, hLD⟩ :=
    SA.fast_lock_provenance_from hr.localRun hr.vstart hy i l₀
      (hstate.symm ▸ hl₀) hfast
  obtain ⟨hkt, hlock⟩ := (SA.upTo_fastLockAt hrun.time_mono).1 hlock
  have hyk := hrun.antitone hkt hy
  obtain ⟨E, EV, hevent, hDE⟩ := lock_below_origin_at hrun hnc hyk (Or.inl ⟨CV, hlock⟩)
  have hLU := upTo_subset hrun hd hL
  obtain rfl : B₀ = L := (Compose.Growing.honest_blocks_coherent_local hrun.toLocalRun hnc).1
    (hΦU hB₀) hLU (hB₀r.trans hLr.symm)
  right
  refine ⟨k, l₀.slot, E, hki.le, hyk, hkt.trans hib,
    goldilocksEvents_confirmedEvent_iff.2 ⟨EV, hevent⟩, ?_⟩
  rw [hCe]
  exact ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU).trans
    ((hLD.mono (upTo_subset hrun hd)).trans hDE)

private theorem service_of_sync {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {ini ΔF b}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hs : tr.SyncRunAt H ΔF 0 (b - sp.Δ)) : SleepyServiceBefore tr H ΔF b := by
  have source_bound : ∀ y j τ, tr.deadline y j τ sp.Δ ≤ b → τ ≤ b - sp.Δ := by
    intro y j τ hb
    unfold RunTrace.deadline at hb
    cases hw : tr.lastWake y j with
    | bot =>
      rw [hw] at hb
      change τ + sp.Δ ≤ b at hb
      linarith
    | coe w =>
      rw [hw] at hb
      change max τ w + sp.Δ ≤ b at hb
      linarith [le_max_left τ w]
  have service := Obligations.Growing.sleepyServiceBefore_of_message_relay_at hrun
    (b := b) (fun x i v hx hv h0 y j ℓ hy hj hb hd => by
      apply (SA.messageServedBefore_iff ..).mpr
      left
      have hsrc : tr.SendOrAdmitAt x i v := by
        obtain ⟨ℓ₀, hc, hm⟩ := hv
        refine ⟨ℓ₀, Compose.projAC_callAt.mp hc, ?_⟩
        rw [projAC_state_at hrun hx] at hm
        exact hm
      obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x i v hx hsrc
        ⟨h0, source_bound y j _ (by rwa [Compose.projAC_deadline] at hb)⟩
        y j hy ⟨_, Compose.projAC_callAt.mp hj⟩
        (by rwa [Compose.projAC_deadline] at hd)
      refine ⟨k, hkj, htk, ?_, ?_⟩
      · rcases hp with ⟨ℓ', hc, hm⟩ | ⟨ℓ', hc, hm⟩
        · exact ⟨ℓ', Compose.projAC_callAt.mpr hc, Or.inl hm⟩
        · exact ⟨ℓ', Compose.projAC_callAt.mpr hc, Or.inr hm⟩
      · rwa [Compose.projAC_deadline])
    (fun x i B hx hi h0 y j hy hj hb hd hanc =>
      hs.relay x i B hx hi ⟨h0, source_bound y j _ hb⟩ y j hy hj hd hanc)
  exact ⟨hs.deltaF, service.message, service.acRelay, service.relay⟩

private theorem retained_count {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {p : EnvPoint (Fin sp.n)} (hbind : RunPointBinding tr H p)
    {c t d : Time} (hc : Regimes.catchUp sp ≤ c) (ht : 0 ≤ t) (htd : t ≤ d)
    (S : Finset (Fin sp.n))
    (h : (1 / 2 : ℚ) * ((((p.retain d).readyAt c t ∩ S).card +
      (p.faultyAt d ∩ S).card : Nat) : ℚ) < ((p.retain d).readyAt c t ∩ S).card) :
    ((S : Set (Fin sp.n)) ∩ (H d)ᶜ).ncard <
      ((S : Set (Fin sp.n)) ∩ {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}).ncard := by
  classical
  have hlt : (p.faultyAt d ∩ S).card < ((p.retain d).readyAt c t ∩ S).card := by
    have : ((p.faultyAt d ∩ S).card : ℚ) < ((p.retain d).readyAt c t ∩ S).card := by
      push_cast at h
      linarith
    exact_mod_cast this
  have hf : (S : Set (Fin sp.n)) ∩ (H d)ᶜ = ↑(p.faultyAt d ∩ S) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_inter]
    rw [hbind.2.1 y d]
    simp only [EnvPoint.HonestAt, not_not, and_comm]
  rw [hf, Set.ncard_coe_finset]
  apply hlt.trans_le
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard (ht := Set.toFinite _)
  intro y hy
  obtain ⟨hyr, hyS⟩ := Finset.mem_inter.mp hy
  have hyr := (Finset.mem_filter.mp hyr).2
  have hyd : y ∈ H d := (hbind.2.1 y d).mpr hyr.1
  have hyt := hrun.antitone htd hyd
  have hwindow : ∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u :=
    fun u hu hut => (hbind.2.2.1 y u).mpr (hyr.2 u hu hut)
  have hcatch : 8 * sp.Δ ≤ c + 1 := by
    dsimp only [Regimes.catchUp] at hc
    linarith [sp.toParams.hΔ]
  obtain ⟨hw, hj⟩ := Obligations.Growing.ready_implies_joined_at hrun hyt ht hcatch hwindow
  exact ⟨hyS, hyd, hw, hj⟩

/-- The finite service and independent population/committee bounds used by the sleepy
discharges. Positivity and slot sizes are explicit. -/
private theorem sleepy_service_and_bounds {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {cm : Time → Finset (Fin sp.n)} (hpos : 0 < sp.committeeSize)
    (hsize : ∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize)
    {p : EnvPoint (Fin sp.n)} {c look committeeLook ΔF b : Time}
    (hw : GoldilocksWindowPremises tr H p cm c look committeeLook ΔF b) :
    0 ≤ b ∧ SleepyServiceBefore tr H ΔF b ∧ SleepyBoundsFrom tr H 0 b ∧
      CommitteeBoundsFrom tr H (dictOfTime sp cm) 0 b := by
  classical
  obtain ⟨hbind, hbh, hc, hlook, hclook, hcm, hsleep, hcommittee, hpop⟩ :=
    goldilocksWindowPremises_iff.mp hw
  obtain ⟨hb, hsync, _⟩ := hsleep
  have hΔ := sp.toParams.hΔ
  have hpopulation : ∀ t d, 0 ≤ t → t ≤ d → d ≤ b → d ≤ t + look →
      tr.FaultBoundAt H t d := by
    intro t d ht htd hdb hdl
    have h := hpop t d ht htd (le_min hdb (le_min hdl (hdb.trans hbh)))
    have h' := retained_count hrun hbind hc ht htd Finset.univ
      (by simpa only [Finset.inter_univ, EnvPoint.ReadyAbove, EnvPoint.faultCount,
        EnvPoint.retain, Nat.cast_add] using h)
    simpa only [RunTrace.FaultBoundAt, Finset.coe_univ, Set.univ_inter] using h'
  have hB : SleepyBoundsFrom tr H 0 b := by
    apply Obligations.Growing.sleepyBoundsFrom_of_faultBoundAt hrun.antitone
      (a := 0) (add_nonneg (ts_natCast_nonneg (sp := sp) 0) hΔ.le) (le_max_right b 0)
    intro t ht _ htb
    exact hpopulation t (min (t + 5 * sp.Δ) b) ht
      (le_min (by linarith) htb) (min_le_right _ _) ((min_le_left _ _).trans (by linarith))
  have hslotNonempty : ∀ s : Nat, (cm (sp.ts s)).Nonempty := by
    intro s
    have hs : (cm (sp.ts s) : Set (Fin sp.n)).ncard = sp.committeeSize := by
      simpa only [dictOfTime, sp.slotTime_eq, SA.SAParams.ts] using hsize s
    exact Finset.card_pos.mp (by simpa using (hpos.trans_eq hs.symm))
  have hcommitteeCount : ∀ t d, (cm t).Nonempty →
      0 ≤ t → t ≤ d → d ≤ b → d ≤ t + committeeLook →
      ((cm t : Set (Fin sp.n)) ∩ (H d)ᶜ).ncard <
        ((cm t : Set (Fin sp.n)) ∩ {y | y ∈ H d ∧ tr.awake y t ∧ tr.JoinedAt y t}).ncard := by
    intro t d hne ht htd hdb hdl
    apply retained_count hrun hbind hc ht htd (cm t)
    exact hcommittee t d ht htd (le_min hdb (le_min hdl (hdb.trans hbh))) hne
  have hBK : CommitteeBoundsFrom tr H (dictOfTime sp cm) 0 b := by
    refine ⟨?_, ?_⟩
    · intro s d _ htd hdb h6
      have ht := ts_natCast_nonneg (sp := sp) s
      have hne : (cm (sp.ts s + sp.Δ)).Nonempty := by
        rw [hcm s]
        exact hslotNonempty s
      have h := hcommitteeCount (sp.ts s + sp.Δ) d hne
        (by linarith) htd hdb (by linarith)
      rw [hcm s] at h
      simp only [SA.FaultBoundK, dictOfTime, sp.slotTime_eq]
      apply h.trans_le
      apply Set.ncard_le_ncard (ht := Set.toFinite _)
      intro y hy
      exact ⟨hy.1, hy.2.1, (mem_awakeJoined_projAC hrun).mpr hy.2.2⟩
    · intro s d _ htd hdb h2
      have ht := ts_natCast_nonneg (sp := sp) s
      have h := hcommitteeCount (sp.ts s) d (hslotNonempty s) ht htd hdb (by linarith)
      have hle : ((cm (sp.ts s) : Set (Fin sp.n)) ∩
          {y | y ∈ H d ∧ tr.awake y (sp.ts s) ∧ tr.JoinedAt y (sp.ts s)}).ncard ≤
          ((cm (sp.ts s) : Set (Fin sp.n)) ∩ H d).ncard :=
        Set.ncard_le_ncard fun _ hy => ⟨hy.1, hy.2.1⟩
      have hn := Set.ncard_inter_add_ncard_sdiff_eq_ncard
        (cm (sp.ts s) : Set (Fin sp.n)) (H d)
      rw [Set.sdiff_eq] at hn
      simp only [dictOfTime, sp.slotTime_eq]
      simp only [SA.SAParams.ts, SA.SAParams.Δ] at h hle hn ⊢
      omega
  exact ⟨hb, service_of_sync hrun hsync, hB, hBK⟩

/-- The existing sleepy induction, with committee positivity explicit rather than
obtained from a particular supplier's run interface. -/
theorem sleepy_invariant_of_windows {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {ini}
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {cm : Time → Finset (Fin sp.n)} (hpos : 0 < sp.committeeSize)
    (hKB : CommitteeFacts tr H (dictOfTime sp cm))
    {p : EnvPoint (Fin sp.n)} {c look committeeLook ΔF b : Time}
    (hw : GoldilocksWindowPremises tr H p cm c look committeeLook ΔF b) :
    SleepyInvariantUpTo tr H b := by
  obtain ⟨hb, hservice, hB, hBK⟩ := sleepy_service_and_bounds hrun hpos hKB.hsize hw
  exact sleepy_invariant_at hrun hnc hKB hb hservice hB hBK

end Consensus.Goldilocks.Generic.SleepyLayer1

end
