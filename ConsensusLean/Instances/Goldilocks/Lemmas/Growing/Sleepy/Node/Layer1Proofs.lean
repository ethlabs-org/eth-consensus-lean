module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Layer1
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements

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

end Consensus.Goldilocks.Generic.SleepyLayer1

end
