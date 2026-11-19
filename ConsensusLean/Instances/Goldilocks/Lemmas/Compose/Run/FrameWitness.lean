module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameViability
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry

public section

/-! # Frame viability from frozen witnesses over any AC

The store geometry of S3 at a vote with the voter block tree abstracted to any set `T` of the
node's frame tree closed under ancestors, on a run of any AC (`viable_of_frozen_witnesses`): a block
compatible with the sources of the node's honest rows lies between `Σ.F` and a witness of `T`,
hence in the frame, and the floor or a crossing source places it in the viable tree of `T`.
`Compose.vote_frame_of_witnesses` (`Lemmas/Compose/Sleepy/FrameWitness`) is the Goldilocks instance
at the voter block tree of a vote, whose cut frame is the node's frame. -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini}

/-- **S3 over sources `G`, with frozen witnesses in `T`**: a block `B` of the honest blocks,
compatible with every source of the node's honest rows at heights `≥ h_j` (sources pairwise
compatible), is in the viable tree of `T` or at or below `fc_root`, when `T` is a part of the
node's frame tree closed under ancestors and `B` and every source above `Σ.F` have witnesses in
`T` above them. -/
theorem viable_of_frozen_witnesses (hr : Node.LocalRun proposer dg H sg tr ini)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat} {G : A.Blk → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {T : Set A.Blk} (hTt : T ⊆ (Node.frame (tr.state y i)).tree)
    (hTa : ∀ W ∈ T, ∀ X, (Node.frame (tr.state y i)).Anc X W → X ∈ T)
    (hGW : ∀ D, G D → Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F D →
      ∃ W ∈ T, Anc (tr.HonestBlocks H) D W)
    {B : A.Blk} (hB : B ∈ tr.HonestBlocks H) (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hw : Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F B →
      ∃ W ∈ T, Anc (tr.HonestBlocks H) B W) :
    B ∈ (Node.frame (tr.state y i)).viableTree T ∨
      Anc (tr.HonestBlocks H) B (Node.frame (tr.state y i)).fcRoot := by
  have hU := hfg.coherent
  have hR := fg_reachable hr hy i
  have hΦ : FrameOK (Node.frame (tr.state y i)) := (Store.frame_realization _ _ _ _ hR).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  -- `Σ.J`, `Σ.F` and `fc_root` are compatible with `B`
  have hJ := J_compatible hr hfg hf hy hsrc hGB hB
  have hF : Compatible (tr.HonestBlocks H) (tr.state y i).fg.F B := by
    have hFJ := ((Store.cache_invariants _ _ _ _ hR).2.2.1).mono hsU
    rcases hJ with h | h
    · exact Or.inl (hFJ.trans h)
    · exact Anc.total hU hFJ h
  have hfc : Compatible (tr.HonestBlocks H) (tr.state y i).fg.fcRoot B := by
    unfold Store.fcRoot
    split_ifs
    · exact hJ
    · exact hF
  rcases hfc with hfB | hBf
  swap
  · exact Or.inr hBf
  left
  have hFB : Anc (tr.HonestBlocks H) (tr.state y i).fg.F B :=
    (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
  -- `B` lies between `Σ.F` and a witness, so it is in the frame
  obtain ⟨W, hW, hBW⟩ := hw hFB
  have hWt := hTt hW
  have hBW' := honest_held_anc hr hfg hy hBW hWt.1
  have hBt : B ∈ (tr.state y i).fg.tree := anc_mem hBW' hWt.1
  have hBΦ : B ∈ (Node.frame (tr.state y i)).tree := ⟨hBt, honest_held_anc hr hfg hy hFB hBt⟩
  have hΦBW : (Node.frame (tr.state y i)).Anc B W :=
    Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ hBW hWt
  have hΦfB : (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot B :=
    Frame.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBΦ
  refine ⟨hTa W hW B hΦBW, hΦfB, ?_⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  -- a witness of height at least the floor
  have head : ∀ W' ∈ T, (Node.frame (tr.state y i)).Anc B W' →
      (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ W'.root).h →
      ∃ W' ∈ T, W' ∈ (Node.frame (tr.state y i)).viableHeads ∧
        (Node.frame (tr.state y i)).Anc B W' := fun W' hW' hBW'' hh =>
    ⟨W', hW', ⟨(hTt hW').1, (hTt hW').2, Anc.mono hΦs (hΦfB.trans hBW''), hh⟩, hBW''⟩
  rcases floor_or_crossing_of hr hfg hf hy hsrc hGG hGB hBt with hle | ⟨D, E, X, hD, hDs, hE,
    hBE, hEh, -⟩
  · exact head W hW hΦBW (hle.trans (honest_held_height hr hfg hy (Anc.mono hΦs hΦBW)).1)
  · -- the witness above the crossing source
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry hr hfg hDs ⟨y, hy, i, hE⟩ rfl
    have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx₀ k₀)
    obtain ⟨W', hW', hDW'⟩ := hGW D hD (hFB.trans ((hBE.mono hsU).trans hEDU))
    have hW't := hTt hW'
    have hEW' := honest_held_anc hr hfg hy (hEDU.trans hDW') hW't.1
    refine head W' hW' (Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ
      ((hBE.mono hsU).trans (hEDU.trans hDW')) hW't) ?_
    rw [← hEh]
    exact (honest_held_height hr hfg hy hEW').1

end Consensus.Goldilocks.Compose.FrameGeometry

end
