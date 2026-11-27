module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameSourceGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry

public section

/-! # Frame viability from compatible honest FG sources over any AC -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini}
  (hr : Node.LocalRun proposer dg H sg tr ini)
  (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
  (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
  {G : A.Blk → Prop}

include hr hfg hy

private theorem held_σ_eq {z : Fin P.n} (hz : z ∈ H) {j : Nat} {B : A.Blk}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root := by
  rw [← store_eq hr hy i] at hBy ⊢
  rw [← store_eq hr hz j] at hBz ⊢
  exact Store.σ_eq_of_held hfg hy hz hBy hBz

private theorem below_entry {B D E : A.Blk}
    (hB : B ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    (hD : IsHonestSource tr H D E.root) (hDB : Compatible (tr.HonestBlocks H) D B)
    (hlt : ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ E.root).h) :
    (tr.state y i).fg.Anc B E := by
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hr hfg hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr.HonestBlocks H) E B := fun h => by
    have := (honest_held_height hr hfg hy (honest_held_anc hr hfg hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hfg.coherent h hEDU with h' | h'
    · exact honest_held_anc hr hfg hy h' hE
    · exact absurd h' no

include hf

/-- Compatibility with all relevant row sources implies compatibility with the justification. -/
theorem J_compatible (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ tr.HonestBlocks H) :
    Compatible (tr.HonestBlocks H) (tr.state y i).fg.J B := by
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hr h0 hy]
    exact Or.inl (honest_genesis_anc hr hB).2
  obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source_of hr hfg hf hy hsrc (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ (fg_reachable hr hy i)).2.1
  obtain ⟨x, hx, k, -, -, hJD, -, -⟩ := honest_source_entry hr hfg hDs ⟨y, hy, i, hJ⟩ rfl
  have hJDU : Anc (tr.HonestBlocks H) (tr.state y i).fg.J D :=
    hJD.mono (fg_tree_subset_honest hx k)
  rcases hGB D hD with h | h
  · exact Or.inl (hJDU.trans h)
  · exact Anc.total hfg.coherent hJDU h

/-- A held block reaches `h_max − 1` or lies below a source entry at `h_max − 1` with a carrier of
height `h_max`, which is viable. -/
theorem floor_or_crossing_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (_hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.hmax - 1 ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧ (tr.state y i).fg.IsViable X := by
  by_cases hle : (tr.state y i).fg.hmax - 1 ≤ ((tr.state y i).fg.σ B.root).h
  · exact Or.inl hle
  right
  obtain ⟨-, -, -, ⟨Z, hZ, -, hZj⟩, hZm, ⟨X, hX, hXh⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ (fg_reachable hr hy i)
  have hB1 := (honest_held_chain hr hy hB).1
  have hZ1 := (honest_held_chain hr hy hZ).2.1
  have hZ2 := hZm Z hZ
  obtain ⟨E, hE, hEX, hEh, -, D, hD, hDs⟩ :=
    frame_crossing_source_of hr hfg hf hy hsrc hX (j := (tr.state y i).fg.hmax - 1) (by omega)
      (by omega) (by omega)
  exact ⟨D, E, X, hD, hDs, hE, below_entry hr hfg hy hB hE hDs (hGB D hD) (by omega), hEh, hX,
    hEX, Or.inl hXh.ge⟩

/-- Compatible source geometry makes a held block of the frame a member of its viable tree. A
block below `h_max − 1` is below a viable carrier; a block at `h_max − 1` is viable, or in a top
frame compatible with `Σ.J` and strictly below it, where `Σ.J` is viable. -/
theorem held_viable_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := hfg.coherent
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hr hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU := fg_tree_subset_honest (tr := tr) hy i
  have hR := fg_reachable hr hy i
  obtain ⟨-, hJm, -, ⟨Z, hZ, -, hZj⟩, hmax, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hjm : (tr.state y i).fg.hj < (tr.state y i).fg.hmax := by
    have := (honest_held_chain hr hy hZ).2.1
    have := hmax Z hZ
    omega
  -- a viable held descendant of `B`
  have hW : ∃ W ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc B W ∧
      (tr.state y i).fg.IsViable W := by
    rcases floor_or_crossing_of hr hfg hf hy hsrc hGG hGB hBt.1 with hpred |
        ⟨-, E, X, -, -, -, hBE, -, hX, hEX, hXv⟩
    swap
    · exact ⟨X, hX, hBE.trans hEX, hXv⟩
    by_cases hv : (tr.state y i).fg.IsViable B
    · exact ⟨B, hBt.1, .refl, hv⟩
    have hBm := hmax B hBt.1
    have hlt : ¬ (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ B.root).h := fun hh => hv (Or.inl hh)
    have htop : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 := by
      by_contra hn
      exact hv (by
        by_cases hh : (tr.state y i).fg.hmax ≤ ((tr.state y i).fg.σ B.root).h
        · exact Or.inl hh
        · exact Or.inr ⟨by omega, Or.inl (by omega)⟩)
    have hJv : (tr.state y i).fg.IsViable (tr.state y i).fg.J := by
      by_cases h0 : (tr.state y i).fg.hj = 0
      · have hg := justified_genesis hr h0 hy
        have h1 := (honest_held_chain hr hy hJm).1
        exact Or.inl (by omega)
      obtain ⟨hJh, -, -⟩ := justified_honest_source_of hr hfg hf hy hsrc (by omega)
      exact Or.inr ⟨by omega, Or.inr .refl⟩
    rcases J_compatible hr hfg hf hy hsrc hGB (hsU hBt.1) with h | h
    · exact absurd (Or.inr ⟨by omega, Or.inr (honest_held_anc hr hfg hy h hBt.1)⟩) hv
    · exact ⟨_, hJm, honest_held_anc hr hfg hy h hJm, hJv⟩
  obtain ⟨W, hWs, hBW, hWv⟩ := hW
  have hΦfB : (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot B :=
    Frame.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem (hBt.2.mono hsU) hBt
  have hWΦ : W ∈ (Node.frame (tr.state y i)).tree := ⟨hWs, hBt.2.trans hBW⟩
  exact Or.inr ⟨hBt, hΦfB, W, hWΦ, ⟨hWs, hWΦ.2, hWv⟩,
    Frame.anc_tree_of_anc_U hU hΦ hΦU hBt (hBW.mono hsU) hWΦ⟩

end Consensus.Goldilocks.Compose.FrameGeometry

end
