module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameViability
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry

public section

/-! # Frame viability from frozen witnesses over any AC

The store geometry of S3 at a vote with the voter block tree abstracted to any set `T` of the
node's frame tree closed under ancestors, on a run of any AC (`viable_of_frozen_witnesses`): a block
compatible with the sources of the node's honest rows lies between `Σ.F` and a witness of `T`,
hence in the frame, and `h_max − 1`, a crossing source or `Σ.J` (in a top frame) places it in
the viable tree of `T`.
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
  obtain ⟨-, hJt, hFJ, ⟨Z, hZ, -, hZj⟩, hmax, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hjm : (tr.state y i).fg.hj < (tr.state y i).fg.hmax := by
    have := (honest_held_chain hr hy hZ).2.1
    have := hmax Z hZ
    omega
  have hJ := J_compatible hr hfg hf hy hsrc hGB hB
  set st := (tr.state y i).fg with hst
  -- `Σ.J` and `Σ.F` (the fork-choice root) are compatible with `B`
  have hF : Compatible (tr.HonestBlocks H) st.F B := by
    rcases hJ with h | h
    · exact Or.inl ((hFJ.mono hsU).trans h)
    · exact Anc.total hU (hFJ.mono hsU) h
  change _ ∨ Anc (tr.HonestBlocks H) B st.F
  rcases hF with hFB | hBf
  swap
  · exact Or.inr hBf
  left
  -- `B` lies between `Σ.F` and a witness, so it is in the frame
  obtain ⟨W, hW, hBW⟩ := hw hFB
  have hWt := hTt hW
  have hBW' := honest_held_anc hr hfg hy hBW hWt.1
  have hBt : B ∈ st.tree := anc_mem hBW' hWt.1
  have hBΦ : B ∈ (Node.frame (tr.state y i)).tree := ⟨hBt, honest_held_anc hr hfg hy hFB hBt⟩
  have hΦBW : (Node.frame (tr.state y i)).Anc B W :=
    Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ hBW hWt
  have hΦfB : (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot B :=
    Frame.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hFB hBΦ
  refine ⟨hTa W hW B hΦBW, hΦfB, ?_⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ st.tree := fun X hX => hX.1
  -- a viable witness above `B`
  have head : ∀ W' ∈ T, (Node.frame (tr.state y i)).Anc B W' → st.IsViable W' →
      ∃ W' ∈ T, W' ∈ (Node.frame (tr.state y i)).viableHeads ∧
        (Node.frame (tr.state y i)).Anc B W' := fun W' hW' hBW'' hv =>
    ⟨W', hW', ⟨(hTt hW').1, (hTt hW').2, hv⟩, hBW''⟩
  -- the top-frame case below `Σ.J`: `Σ.J` is a viable head with a witness in `T`
  by_cases hcase : st.hj + 1 < st.hmax ∨ Anc (tr.HonestBlocks H) st.J B
  swap
  · have htop : st.hmax = st.hj + 1 := by omega
    have hBJ : Anc (tr.HonestBlocks H) B st.J := hJ.resolve_left fun h => hcase (Or.inr h)
    have h1 : 1 ≤ st.hj := by
      by_contra h0
      have hJg := justified_genesis hr (show st.hj = 0 by omega) hy
      exact hcase (Or.inr (hJg ▸ (honest_genesis_anc hr hB).2))
    obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_of hr hfg hf hy hsrc h1
    obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hr hfg hDs ⟨y, hy, i, hJt⟩ rfl
    have hJDU : Anc (tr.HonestBlocks H) st.J D := hJD.mono (fg_tree_subset_honest hx k)
    obtain ⟨W', hW', hDW'⟩ := hGW D hD (hFB.trans (hBJ.trans hJDU))
    have hJΦ : st.J ∈ (Node.frame (tr.state y i)).tree := ⟨hJt, hFJ⟩
    have hJT : st.J ∈ T :=
      hTa W' hW' st.J (Frame.anc_tree_of_anc_U hU hΦ hΦU hJΦ (hJDU.trans hDW') (hTt hW'))
    exact ⟨st.J, hJT, ⟨hJt, hFJ, J_viable_of_top hr hfg hf hy hsrc htop⟩,
      Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ hBJ hJΦ⟩
  -- otherwise every witness above `B` at height `≥ h_max − 1` is viable
  have viab : ∀ W', W' ∈ st.tree → st.Anc B W' → st.hmax - 1 ≤ (st.σ W'.root).h →
      st.IsViable W' := by
    intro W' hW' hBW'' hh
    by_cases hm : st.hmax ≤ (st.σ W'.root).h
    · exact Or.inl hm
    refine Or.inr ⟨by omega, hcase.imp id fun hJB => ?_⟩
    exact honest_held_anc hr hfg hy (hJB.trans (hBW''.mono hsU)) hW'
  rcases floor_or_crossing_of hr hfg hf hy hsrc hGG hGB hBt with hle | ⟨D, E, -, hD, hDs, hE,
    hBE, hEh, -⟩
  · exact head W hW hΦBW (viab W hWt.1 (Anc.mono hΦs hΦBW)
      (hle.trans (honest_held_height hr hy (Anc.mono hΦs hΦBW)).1))
  · -- the witness above the crossing source
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry hr hfg hDs ⟨y, hy, i, hE⟩ rfl
    have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx₀ k₀)
    obtain ⟨W', hW', hDW'⟩ := hGW D hD (hFB.trans ((hBE.mono hsU).trans hEDU))
    have hW't := hTt hW'
    have hEW' := honest_held_anc hr hfg hy (hEDU.trans hDW') hW't.1
    have hΦBW' := Frame.anc_tree_of_anc_U hU hΦ hΦU hBΦ
      ((hBE.mono hsU).trans (hEDU.trans hDW')) hW't
    refine head W' hW' hΦBW' (viab W' hW't.1 (Anc.mono hΦs hΦBW') ?_)
    rw [← hEh]
    exact (honest_held_height hr hy hEW').1

end Consensus.Goldilocks.Compose.FrameGeometry

end
