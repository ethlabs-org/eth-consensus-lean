module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote

public section

/-! # Goldilocks under `Sleepy`: frame viability at a vote from frozen witnesses

The store geometry of S3 at a vote, with the relay of the honest heads left as premises: a block
compatible with the sources of the voter's honest rows lies between `Σ.F` and a frozen witness,
hence in the voter's frame, and the floor or a crossing source places it in the viable tree of the
voter block tree (`vote_frame_of_witnesses`). The sources are the blocks below compatible tips
(`below_tips_compatible`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **Sources below pairwise compatible tips.** In a coherent `U`, the blocks below tips `Q` that
are pairwise compatible are pairwise compatible, and compatible with a block compatible with every
tip. -/
theorem below_tips_compatible {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {Q : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hQQ : ∀ C C', Q C → Q C' → Compatible U C C')
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hQB : ∀ C, Q C → Compatible U B C) :
    (∀ D D', (∃ C, Q C ∧ Anc U D C) → (∃ C, Q C ∧ Anc U D' C) → Compatible U D D') ∧
      ∀ D, (∃ C, Q C ∧ Anc U D C) → Compatible U D B := by
  refine ⟨?_, ?_⟩
  · rintro D D' ⟨C, hC, hDC⟩ ⟨C', hC', hDC'⟩
    rcases hQQ C C' hC hC' with h | h
    · exact Anc.total hU (hDC.trans h) hDC'
    · exact Anc.total hU hDC (hDC'.trans h)
  · rintro D ⟨C, hC, hDC⟩
    rcases hQB C hC with h | h
    · exact Anc.total hU hDC h
    · exact Or.inl (hDC.trans h)

/-- **S3 at votes, over sources `G`, with the frozen witnesses given**: at an honest slot-`(s+1)`
vote, with the honest attestations at heights `≥ h_j` sourced by `G` (sources pairwise compatible
and compatible with `B`), a block `B` of the honest blocks is in the viable tree of the voter block
tree, or at or below `fc_root`, when `B` and every source above `Σ.F` have frozen witnesses (blocks
of the voter block tree above them). -/
theorem vote_frame_of_witnesses {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {s : Nat} {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    (hGW : ∀ D, G D → Anc (tr.HonestBlocks H) ℓ.frame.F D →
      ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocks H) D W)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocks H)
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hw : Anc (tr.HonestBlocks H) ℓ.frame.F B →
      ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1), Anc (tr.HonestBlocks H) B W) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hfr := frame_of_projAC hrun hy hc.1
  have hΦ : FrameOK ℓ.frame := by
    rw [hfr]; exact (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rw [hfr]; exact fun X hX => ⟨y, hy, i, hX.1⟩
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `Σ.J`, `Σ.F` and `fc_root` are compatible with `B`
  have hJ := J_compatible hrun hnc hf hy hsrc hGB hB
  have hF : Compatible (tr.HonestBlocks H) (tr.state y i).fg.F B := by
    have hFJ := ((Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).2.2.1).mono
      hsU
    rcases hJ with h | h
    · exact Or.inl (hFJ.trans h)
    · exact Anc.total hU hFJ h
  have hfc : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJ
    · exact hF
  have hv := vote_viable hrun hnc hy hc (B := B) ⟨hF, hJ⟩
  rw [hs] at hv
  apply hv
  rcases hfc with hfB | hBf
  swap
  · exact Or.inr hBf
  left
  have hFB : Anc (tr.HonestBlocks H) ℓ.frame.F B := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
  -- the relayed honest slot-`s` head extending `B`
  obtain ⟨W, hW, hBW⟩ := hw hFB
  have hWt : W ∈ (tr.state y i).fg.tree := by
    have := hW.1; rw [hfr] at this; exact this.1
  have hBW' := honest_held_anc hrun hnc hy hBW hWt
  have hBt := anc_mem hBW' hWt
  rcases floor_or_crossing_of hrun hnc hf hy hsrc hGG hGB hBt with hle | ⟨D, E, X, hD, hDs, hE,
    hBE, hEh, -⟩
  · exact ⟨W, hW, hBW, hle.trans (honest_held_height hrun hnc hy hBW').1⟩
  · -- the honest head of a vote extending the crossing source
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hE⟩ rfl
    have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx₀ k₀)
    have hFD : Anc (tr.HonestBlocks H) ℓ.frame.F D := hFB.trans ((hBE.mono hsU).trans hEDU)
    obtain ⟨W', hW', hDW'⟩ := hGW D hD hFD
    have hW't : W' ∈ (tr.state y i).fg.tree := by
      have := hW'.1; rw [hfr] at this; exact this.1
    have hEW' := honest_held_anc hrun hnc hy (hEDU.trans hDW') hW't
    refine ⟨W', hW', (hBE.mono hsU).trans (hEDU.trans hDW'), ?_⟩
    change (tr.state y i).fg.headHeightFloor ≤ _
    rw [← hEh]
    exact (honest_held_height hrun hnc hy hEW').1

end Consensus.Goldilocks.Compose

end
