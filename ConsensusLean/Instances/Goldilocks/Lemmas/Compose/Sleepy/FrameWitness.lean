module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote

public section

/-! # Goldilocks under `Sleepy`: frame viability at a vote from frozen witnesses

The store geometry of S3 at a vote, with the relay of the honest heads left as premises: a block
compatible with the sources of the voter's honest rows lies between `Σ.F` and a frozen witness,
hence in the voter's frame, and the floor or a crossing source places it in the viable tree of the
voter block tree (`vote_frame_of_witnesses`, the voter block tree's instance of the store geometry
over any AC, `FrameGeometry.viable_of_frozen_witnesses`). The sources are the blocks below
compatible tips (`below_tips_compatible`). -/

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
  have hfr := frame_of_projAC hrun hy hc.1
  have hTa := SA.voterBlockTree_anc (goldilocks_ac_projection_from hrun hnc).localRun hrun.vstart
    hy hc
  rw [hs] at hTa
  have hsrc' : FrameGeometry.RowsAbove tr H G y i (tr.state y i).fg.hj :=
    FrameGeometry.rowsAbove_iff.2 fun X hX a ha hav hE hh =>
      (rowsAbove_iff.1 hsrc X hX a ha hav hE hh).imp fun _ ⟨hD, hDs⟩ =>
        ⟨hD, FrameGeometry.isHonestSource_iff.2 (isHonestSource_iff.1 hDs)⟩
  have h := FrameGeometry.viable_of_frozen_witnesses hrun.toLocalRun (projFG_localRun hrun hnc) hf
    hy hsrc' hGG (T := SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1))
    (by rw [← hfr]; exact fun X hX => hX.1) (by rw [← hfr]; exact hTa) (by rw [← hfr]; exact hGW)
    hB hGB (by rw [← hfr]; exact hw)
  rwa [← hfr] at h

end Consensus.Goldilocks.Compose

end
