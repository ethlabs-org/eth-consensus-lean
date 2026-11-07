module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.FrozenFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Frames of the suffix comparison, under growing faults

The frame suppliers of `reset_suffix_best_at` (static `Healing/Outcome/SupplierViews`,
`SupplierFrames`). The operational proposer is honest through `t_{s+1} + hold`, every voter at
its own cast, and every relayed acceptance at its own cut:

* `reset_winner_voter_tree_at`: an ancestor of a viable current proposal above the voter's
  anchor is in the voter's viable tree;
* `reset_competitor_reflect_at`: a voter's viable competitor of the proposal is in the
  proposer's viable tree (pre-freeze competitors by `reset_frozen_frame_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Any ancestor of a viable current proposal above the voter's anchor is in the voter's viable
tree, for a voter honest at its cast. -/
theorem reset_winner_voter_tree_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hy : y ∈ H (tr.time j))
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocksAt H) C P)
    (haC : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u) := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hPhi := Outcome.frame_realized hrun hy hc.1
  have hPhiU := Outcome.frame_tree_subset hrun hy hc.1
  have hfC := ((SA.fcRoot_anc_getAnchor hPhi e.readPoint (tr.time j)).mono hPhiU).trans haC
  have hFC := (hPhi.F_anc_fcRoot.mono hPhiU).trans hfC
  have hCt := SA.frame_mem_of_between sp hU hPhi hPhiU hP.1.1 hCP hFC
  have hCP' := SA.anc_tree_of_anc_U hU hPhi hPhiU hCt hCP hP.1.1
  have hfC' := SA.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem hfC hCt
  obtain ⟨W, hW, hWv, hPW⟩ := hP.2.2
  have hCs : C ∈ SA.voterBlockTree sp e.readPoint ell.frame u := by
    rw [← hes] at hP ⊢
    have hd := hrun.time_nonneg j
    have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
      (tr.upTo (tr.time j)) proposer (hrun.upTo hd) (hnc.upTo _)).localRun
    rw [RunTrace.upTo_projAC] at hr
    have hc' : SA.CastAt (tr.projAC.upTo (tr.time j)) y j ell e := SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
    exact SA.voterBlockTree_anc hr hy hc' P hP.1 C hCP'
  exact ⟨hCs, hfC', W, hW, hWv, hCP'.trans hPW⟩

/-- A viable competitor of the proposal at a slot-`(s+1)` voter honest at its cast, a child of a
viable head below the proposal's parent, is in the viable tree of the proposer, honest through
`t_{s+1} + hold`. -/
theorem reset_competitor_reflect_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts (s + 1 : Nat) + hold sp)) (hdesignated : p = proposer (s + 1))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hy : y ∈ H (tr.time j)) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {Q X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQt : Q ∈ ellp.frame.tree) (hPQ : P.parent = some Q.root)
    (hXQ : ellp.frame.Anc X Q) (hBP : B ≠ P)
    (hXv : X ∈ ellp.frame.viableHeads) (hBX : B.parent = some X.root)
    (hB : B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hΔ := sp.toParams.hΔ
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by
    rw [hti]
    change sp.ts (s + 1 : Nat) ≤ sp.ts (s + 1 : Nat) + sp.Δ
    linarith) hpH
  have hPhi := Outcome.frame_realized hrun hpi hci
  have hPhiU := Outcome.frame_tree_subset hrun hpi hci
  have hPsiU := Outcome.frame_tree_subset hrun hy hcy.1
  have hXt : X ∈ ellp.frame.tree := SA.mem_of_anc hXQ hQt
  have hXB : Anc (tr.HonestBlocksAt H) X B := .single ⟨hPhiU hXt, hPsiU hB.1.1, hBX⟩
  have hFB := ((hPhi.rooted.2 X hXt).mono hPhiU).trans hXB
  have hBt : B ∈ ellp.frame.tree := by
    rcases hB.1.2 with hfz | ⟨P', hP't, hP's, hBP'⟩
    · exact hp.reset_frozen_frame_at hc hpi hy hci hti hcy hib hg hjoin hB.1.1 hfz hFB
    · have hjt : tr.time j ≤ sp.ts (s + 1 : Nat) + hold sp := by
        have hd := hrun.time_nonneg j
        have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
          (tr.upTo (tr.time j)) proposer (hrun.upTo hd) (hnc.upTo _)).localRun
        rw [RunTrace.upTo_projAC] at hr
        have hc' : SA.CastAt (tr.projAC.upTo (tr.time j)) y j elly e :=
          SA.upTo_castAt.mpr ⟨le_rfl, hcy⟩
        have h := (Compose.cast_head_fcRoot hr hy hc').2
        rw [hes] at h
        exact h
      have hPP : P' = P := Outcome.proposal_unique_before_hold hrun hnc hpH hdesignated hactual
        hPs (by omega) hy hcy.1 hjt hP't hP's
      subst hPP
      have hBQ : Anc (tr.HonestBlocksAt H) B Q := by
        rcases Relation.ReflTransGen.cases_tail (hBP'.mono hPsiU) with heq | ⟨Y, hBY, hY⟩
        · exact absurd heq.symm hBP
        obtain rfl : Y = Q := hU.1 hY.1 (hPhiU hQt)
          (Option.some_injective _ (hY.2.2.symm.trans hPQ))
        exact hBY
      exact SA.frame_mem_of_between sp hU hPhi hPhiU hQt hBQ hFB
  have hfB := SA.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem
    (((hPhi.fcRoot_anc_viableHeads X hXv).mono hPhiU).trans hXB) hBt
  refine ⟨hBt, hfB, B, hBt, ?_, .refl⟩
  have hi0 := hrun.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  rw [Outcome.frame_of_call hrun hpi hci] at hXv hBt ⊢
  have hXBs := store_anc_of_honest_anc_at hrun hnc hi0 hle hpi hXB hBt.1
  exact ⟨hBt.1, hBt.2, hXv.2.2.1.trans hXBs,
    le_trans hXv.2.2.2 (Healing.σ_h_le_of_anc (fg_reachable_at hrun hi0 hle hpi) hXBs)⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
