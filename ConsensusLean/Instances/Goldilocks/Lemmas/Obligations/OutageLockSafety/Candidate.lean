module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Outage lock safety: a held block stays a viable-ancestor candidate without pairwise sources

Outage lock-safety card (workbench `outage_lock_safety.md` §6.3, read-back fix F4).
`held_viable_of` (`Sleepy/FrameLabels.lean`) excludes every contest through pairwise compatible
sources. In the outage two honest sources can be siblings above the protected block, so a contest
can occur; `held_candidate_of_rows` shows that a contest never removes the candidacy of a held
block `B` compatible with every source: `B` is at or below `fc_root`, or in the full viable
tree. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The entry an honest source names is compatible with a block compatible with the source. -/
private theorem entry_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {D E B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDs : IsHonestSource tr H D E.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hDB : Compatible (tr.HonestBlocks H) D B) : Compatible (tr.HonestBlocks H) E B := by
  have hU := (projFG_localRun hrun hnc).coherent
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx k)
  rcases hDB with h | h
  · exact Or.inl (hEDU.trans h)
  · exact Anc.total hU hEDU h

/-- **A held block compatible with every honest source stays a candidate** (card §6.3): with
`f < n/2` and the honest attestations of `y`'s tree sourced by `G`, a block `B` of the frame's tree
compatible with every `G`-source is at or below `fc_root` or in the full viable tree. No pairwise
premise on the sources. -/
theorem held_candidate_of_rows (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hR := fg_reachable hrun.toLocalRun hy i
  have hΦ : FrameOK (Node.frame (tr.state y i)) := (Store.frame_realization _ _ _ _ hR).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  have hJB := J_compatible_before hrun hnc hf hy hsrc hGB (hsU hBt.1)
  -- `fc_root` (`Σ.J` or `Σ.F`) is compatible with `B`
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJB
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  by_cases hA : ∃ X ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc B X ∧
      (tr.state y i).fg.IsViable X
  · -- Case A: a viable block above `B` is a viable head
    obtain ⟨X, hX, hBX, hXv⟩ := hA
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hBt.2.trans hBX⟩
    exact ⟨hBt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, (Anc.mono hΦs hΦfB).trans hBX, hXv⟩,
      SA.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBX) hXΦ⟩
  -- Case B: every block above `B` is below the floor; impossible
  exfalso
  push Not at hA
  have hB := hBt.1
  obtain ⟨-, hJ, -, ⟨Z, hZ, -, hZj⟩, hZm, ⟨XM, hXM, hXMh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hgen := (Store.accepted_tree _ _ _ _ hR).2.2.2
  have hB1 := (honest_held_chain hrun hy hB).1
  have hBfl : ((tr.state y i).fg.σ B.root).h < (tr.state y i).fg.headHeightFloor :=
    lt_of_not_ge (hA B hB .refl)
  have hflM : (tr.state y i).fg.headHeightFloor ≤ (tr.state y i).fg.hmax := by
    unfold Store.headHeightFloor; split_ifs <;> omega
  -- a block of height `h_max` with no ancestry from `B` has an entry `⪯ B` of height `h_max − 1`
  have entry_below : ∀ W ∈ (tr.state y i).fg.tree,
      ((tr.state y i).fg.σ W.root).h = (tr.state y i).fg.hmax → 2 ≤ (tr.state y i).fg.hmax →
      ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧ (tr.state y i).fg.Anc E B ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.hmax - 1 ∧
        ((tr.state y i).fg.σ E.root).Th = E.root := by
    intro W hW hWh hM
    obtain ⟨E, hE, hEW, hEh, hET, D, hD, hDs⟩ :=
      frame_crossing_source_before hrun hnc hf hy hsrc hW (j := (tr.state y i).fg.hmax - 1)
        (by omega)
        (by omega)
    refine ⟨E, hE, hEW, ?_, hEh, hET⟩
    rcases entry_compatible hrun hnc hy hDs hE (hGB D hD) with h | h
    · exact honest_held_anc hrun hnc hy h hB
    · have hBW : (tr.state y i).fg.Anc B W :=
        honest_held_anc hrun hnc hy (h.trans (hEW.mono hsU)) hW
      have := hA W hW hBW
      unfold Store.IsViable at this
      omega
  -- `h_max ≥ 2`
  have hM2 : 2 ≤ (tr.state y i).fg.hmax := by
    by_cases hc : (tr.state y i).fg.Contest
    · obtain ⟨hmj, Y, hY, -, -, hJY⟩ := hc
      by_cases h0 : (tr.state y i).fg.hj = 0
      · exact absurd (by rw [justified_genesis hrun h0 hy]; exact hgen Y hY) hJY
      · omega
    · have : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
        unfold Store.headHeightFloor; simp only [hc, ite_false]
      omega
  obtain ⟨E, -, -, hEB, hEh, -⟩ := entry_below XM hXM hXMh hM2
  have hEBh := (honest_held_height hrun hnc hy hEB).1
  -- so `y` is in a contest, `B` at height `h_max − 1`
  have hc : (tr.state y i).fg.Contest := by
    by_contra hc
    have : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
      unfold Store.headHeightFloor; simp only [hc, ite_false]
    omega
  obtain ⟨hmj, Y, hY, -, hYh, hJY⟩ := hc
  obtain ⟨EY, -, hEYY, hEYB, hEYh, hEYT⟩ := entry_below Y hY hYh hM2
  obtain ⟨hJh, hJT, -⟩ := justified_honest_source_before hrun hnc hf hy hsrc (by omega)
  have hJEY : (tr.state y i).fg.J = EY := by
    rcases hJB with h | h
    · exact held_entry_unique hrun hnc hy hB (honest_held_anc hrun hnc hy h hB) hEYB
        (by rw [hJh, hEYh]; omega) hJT hEYT
    · have hBJ := honest_held_anc hrun hnc hy h hJ
      exact held_entry_unique hrun hnc hy hJ .refl (hEYB.trans hBJ)
        (by rw [hJh, hEYh]; omega) hJT hEYT
  exact hJY (hJEY ▸ hEYY)

end Consensus.Goldilocks.Compose

end
