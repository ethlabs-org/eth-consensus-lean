module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameViability
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry

public section

/-! # Viable-ancestor candidacy from honest FG rows

A held block compatible with the sources remains a candidate even when the sources are
not pairwise compatible. This is geometry of the actual FG stores over any AC. -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {proposer : Nat → Fin P.n}

private theorem entry_compatible {ini} (hr : Node.LocalRun proposer dg H sg tr ini)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {D E B : A.Blk}
    (hDs : IsHonestSource tr H D E.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hDB : Compatible (tr.HonestBlocks H) D B) : Compatible (tr.HonestBlocks H) E B := by
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hr hf hDs ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono fun _ hX => ⟨x, hx, k, hX⟩
  rcases hDB with h | h
  · exact Or.inl (hEDU.trans h)
  · exact Anc.total hf.coherent hEDU h

/-- **A held block compatible with every source stays a viable-ancestor candidate, over a frozen
tree `T`**, a part of the node's frame tree closed under ancestors with witnesses in `T` above `B`
and above every frame block below a source. The sources need not be pairwise compatible. `B` is at
or below `fc_root`, or in the viable tree of `T`, or there is a contest and every viable head in `T`
extends `B` (in a contest every block of the maximal height extends `B`, but `T` need hold none).
At `T` the whole frame tree the witnesses are the blocks themselves, and the contest's own block is
a viable head above `B` (`held_candidate_of_rows`). -/
theorem held_candidate_of_rows_within {ini} (hr : Node.LocalRun proposer dg H sg tr ini)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) (i : Nat)
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) {B : A.Blk}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree)
    {T : Set A.Blk} (hTt : T ⊆ (Node.frame (tr.state y i)).tree)
    (hTa : ∀ W ∈ T, ∀ X, (Node.frame (tr.state y i)).Anc X W → X ∈ T)
    (hw : ∃ W ∈ T, (Node.frame (tr.state y i)).Anc B W)
    (hGW : ∀ X ∈ (Node.frame (tr.state y i)).tree,
      (∃ D, G D ∧ Anc (tr.HonestBlocks H) X D) →
      ∃ W ∈ T, (Node.frame (tr.state y i)).Anc X W) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree T ∨
      ((tr.state y i).fg.Contest ∧ ∀ W ∈ T, W ∈ (Node.frame (tr.state y i)).viableHeads →
        (Node.frame (tr.state y i)).Anc B W) := by
  have hU := hfg.coherent
  have hR := fg_reachable hr hy i
  have hΦ : FrameOK (Node.frame (tr.state y i)) := (Store.frame_realization _ _ _ _ hR).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fg_tree_subset_honest hy i
  have hB := hBt.1
  have hJB := J_compatible hr hfg hf hy (hsrc.above _) hGB (hsU hB)
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJB
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (Frame.anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := Frame.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  obtain ⟨-, hJ, -, -, hZm, ⟨XM, hXM, hXMh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  -- the entry one height below a maximal block is compatible with `B` through its source
  have entry_below : ∀ W ∈ (tr.state y i).fg.tree,
      ((tr.state y i).fg.σ W.root).h = (tr.state y i).fg.hmax → 2 ≤ (tr.state y i).fg.hmax →
      ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
        ((tr.state y i).fg.Anc E B ∨ (tr.state y i).fg.Anc B E) ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.hmax - 1 ∧
        ((tr.state y i).fg.σ E.root).Th = E.root ∧
        ∃ D, G D ∧ Anc (tr.HonestBlocks H) E D := by
    intro W hW hWh hM
    obtain ⟨E, hE, hEW, hEh, hET, D, hD, hDs⟩ :=
      frame_crossing_source_before hr hfg hf hy hsrc hW (j := (tr.state y i).fg.hmax - 1)
        (by omega) (by omega)
    obtain ⟨x₀, hx₀, k₀, -, -, hED, -, -⟩ := honest_source_entry hr hfg hDs ⟨y, hy, i, hE⟩ rfl
    refine ⟨E, hE, hEW, ?_, hEh, hET, D, hD, hED.mono (fg_tree_subset_honest hx₀ k₀)⟩
    rcases entry_compatible hr hfg hy hDs hE (hGB D hD) with h | h
    · exact Or.inl (honest_held_anc hr hfg hy h hB)
    · exact Or.inr (honest_held_anc hr hfg hy h hE)
  by_cases hc : (tr.state y i).fg.Contest
  · -- in a contest every block of the maximal height extends `B`
    right
    refine ⟨hc, fun W hW hWv => ?_⟩
    obtain ⟨hmj, Y, hY, hFY, hYh, hJY⟩ := hc
    have hM2 : 2 ≤ (tr.state y i).fg.hmax := by
      by_cases h0 : (tr.state y i).fg.hj = 0
      · have hgen := (Store.accepted_tree _ _ _ _ hR).2.2.2
        exact absurd (by rw [justified_genesis hr h0 hy]; exact hgen Y hY) hJY
      · omega
    obtain ⟨hJh, hJT, -⟩ := justified_honest_source_before hr hfg hf hy hsrc (by omega)
    -- an entry of height `h_j` below `B` is `Σ.J`
    have entry_J : ∀ E, (tr.state y i).fg.Anc E B →
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.hmax - 1 →
        ((tr.state y i).fg.σ E.root).Th = E.root → (tr.state y i).fg.J = E := by
      intro E hEB hEh hET
      rcases hJB with h | h
      · exact held_entry_unique hr hfg hy hB (honest_held_anc hr hfg hy h hB) hEB
          (by rw [hJh, hEh]; omega) hJT hET
      · exact held_entry_unique hr hfg hy hJ .refl (hEB.trans (honest_held_anc hr hfg hy h hJ))
          (by rw [hJh, hEh]; omega) hJT hET
    have hBJ : (tr.state y i).fg.Anc B (tr.state y i).fg.J := by
      obtain ⟨EY, -, hEYY, hcmp, hEYh, hEYT, -⟩ := entry_below Y hY hYh hM2
      rcases hcmp with hEYB | hBEY
      · exact absurd (entry_J EY hEYB hEYh hEYT ▸ hEYY) hJY
      rcases hJB with h | h
      · exact absurd ((honest_held_anc hr hfg hy h hB).trans (hBEY.trans hEYY)) hJY
      · exact honest_held_anc hr hfg hy h hJ
    have hWt := hTt hW
    have hWh : ((tr.state y i).fg.σ W.root).h = (tr.state y i).fg.hmax := by
      have hv := hWv.2.2.2
      change (tr.state y i).fg.headHeightFloor ≤ _ at hv
      unfold Store.headHeightFloor at hv
      simp only [show (tr.state y i).fg.Contest from ⟨hmj, Y, hY, hFY, hYh, hJY⟩,
        ↓reduceIte] at hv
      exact le_antisymm (hZm W hWt.1) hv
    obtain ⟨EW, -, hEWW, hcmp, hEWh, hEWT, -⟩ := entry_below W hWt.1 hWh hM2
    have hBW : (tr.state y i).fg.Anc B W := by
      rcases hcmp with hEB | hBE
      · exact hBJ.trans (entry_J EW hEB hEWh hEWT ▸ hEWW)
      · exact hBE.trans hEWW
    exact Frame.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBW) hWt
  -- otherwise `B` is in the viable tree of `T`
  left
  obtain ⟨W₀, hW₀, hBW₀⟩ := hw
  refine ⟨hTa W₀ hW₀ B hBW₀, hΦfB, ?_⟩
  -- a witness above a frame block of height at least the floor above `B` is a viable head
  have head : ∀ X W, W ∈ T → (Node.frame (tr.state y i)).Anc B X →
      (Node.frame (tr.state y i)).Anc X W →
      (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ X.root).h →
      ∃ W ∈ T, W ∈ (Node.frame (tr.state y i)).viableHeads ∧
        (Node.frame (tr.state y i)).Anc B W := fun X W hW hBX hXW hX =>
    ⟨W, hW, ⟨(hTt hW).1, (hTt hW).2, Anc.mono hΦs (hΦfB.trans (hBX.trans hXW)),
      hX.trans (honest_held_height hr hfg hy (Anc.mono hΦs hXW)).1⟩, hBX.trans hXW⟩
  by_cases hBfl : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
  · exact head B W₀ hW₀ .refl hBW₀ hBfl
  have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
    unfold Store.headHeightFloor; simp only [hc, ite_false]
  obtain ⟨E, hE, -, hcmp, hEh, -, hsE⟩ := entry_below XM hXM hXMh (by omega)
  have hBE : (tr.state y i).fg.Anc B E := hcmp.resolve_left fun h => by
    have := (honest_held_height hr hfg hy h).1
    omega
  have hEΦ : E ∈ (Node.frame (tr.state y i)).tree := ⟨hE, hBt.2.trans hBE⟩
  obtain ⟨W, hW, hEW⟩ := hGW E hEΦ hsE
  exact head E W hW (Frame.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBE) hEΦ) hEW
    (by rw [hfl, hEh])

/-- A held block compatible with every source stays a viable-ancestor candidate. -/
theorem held_candidate_of_rows {ini} (hr : Node.LocalRun proposer dg H sg tr ini)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) (i : Nat)
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) {B : A.Blk}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  rcases held_candidate_of_rows_within hr hfg hf hy i hsrc hGB hBt subset_rfl
    (fun _ hW _ hXW => anc_mem hXW hW) ⟨B, hBt, .refl⟩ (fun X hX _ => ⟨X, hX, .refl⟩) with
    h | h | ⟨⟨hmj, Y, hY, hFY, hYh, hJY⟩, h⟩
  · exact Or.inl h
  · exact Or.inr h
  -- in a contest the contest's own block is a viable head above `B`
  have hc : (tr.state y i).fg.Contest := ⟨hmj, Y, hY, hFY, hYh, hJY⟩
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hr hy i)).1
  have hfc : (tr.state y i).fg.fcRoot = (tr.state y i).fg.F := by
    unfold Store.fcRoot
    simp only [hc, not_true_eq_false, and_false, ↓reduceIte]
  have hYv : Y ∈ (Node.frame (tr.state y i)).viableHeads := by
    refine ⟨hY, hFY, hfc ▸ hFY, ?_⟩
    change (tr.state y i).fg.headHeightFloor ≤ _
    unfold Store.headHeightFloor
    simp only [hc, ↓reduceIte, hYh, le_refl]
  refine Or.inr ⟨hBt, ?_, Y, ⟨hY, hFY⟩, hYv, h Y ⟨hY, hFY⟩ hYv⟩
  change (Node.frame (tr.state y i)).Anc (tr.state y i).fg.fcRoot B
  rw [hfc]
  exact hΦ.rooted.2 B hBt

end Consensus.Goldilocks.Compose.FrameGeometry

end
