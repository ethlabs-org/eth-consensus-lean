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

private theorem source_entry_eq {D D' E E' : A.Blk}
    (hDD' : Compatible (tr.HonestBlocks H) D D') (hD : IsHonestSource tr H D E.root)
    (hD' : IsHonestSource tr H D' E'.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hE' : E' ∈ (tr.state y i).fg.tree)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h) : E = E' := by
  have key : ∀ {D D' E E' : A.Blk}, Anc (tr.HonestBlocks H) D D' →
      IsHonestSource tr H D E.root → IsHonestSource tr H D' E'.root → E ∈ (tr.state y i).fg.tree →
      E' ∈ (tr.state y i).fg.tree →
      ((tr.state y i).fg.σ E.root).h = ((tr.state y i).fg.σ E'.root).h → E = E' := by
    intro D D' E E' hDD hD hD' hE hE' hh
    obtain ⟨x, hx, k, -, hEt, hED, -, hET⟩ := honest_source_entry hr hfg hD ⟨y, hy, i, hE⟩ rfl
    obtain ⟨x', hx', k', hD't, hE't, hE'D', -, hE'T⟩ :=
      honest_source_entry hr hfg hD' ⟨y, hy, i, hE'⟩ rfl
    have hED' : (tr.state x' k').fg.Anc E D' :=
      honest_held_anc hr hfg hx' ((hED.mono (fg_tree_subset_honest hx k)).trans hDD) hD't
    have hEt' := anc_mem hED' hD't
    refine held_entry_unique hr hfg hx' hD't hED' hE'D' ?_ ?_ hE'T
    · rw [held_σ_eq hr hfg hx' hy hEt' hE, held_σ_eq hr hfg hx' hy hE't hE']
      exact hh
    · rw [held_σ_eq hr hfg hx' hx hEt' hEt]
      exact hET
  rcases hDD' with h | h
  · exact key h hD hD' hE hE' hh
  · exact (key h hD' hD hE' hE hh.symm).symm

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

private theorem frame_no_contest_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D') :
    ¬ (tr.state y i).fg.Contest := by
  rintro ⟨hm, X, hX, -, hXh, hJX⟩
  have hR := fg_reachable hr hy i
  by_cases h0 : (tr.state y i).fg.hj = 0
  · rw [justified_genesis hr h0 hy] at hJX
    exact hJX ((Store.accepted_tree _ _ _ _ hR).2.2.2 X hX)
  obtain ⟨hJh, hJT, D, hD, hDs⟩ := justified_honest_source_of hr hfg hf hy hsrc (by omega)
  obtain ⟨E, hE, hEX, hEh, hET, D', hD', hD's⟩ :=
    frame_crossing_source_of hr hfg hf hy hsrc hX (j := (tr.state y i).fg.hj) le_rfl (by omega)
      (by omega)
  have hJ := (Store.cache_invariants _ _ _ _ hR).2.1
  rw [source_entry_eq hr hfg hy (hGG D D' hD hD') hDs hD's hJ hE (hJh.trans hEh.symm)] at hJX
  exact hJX hEX

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

/-- A held block reaches the floor or a source entry at the floor with a viable carrier. -/
theorem floor_or_crossing_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : A.Blk} (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧ (tr.state y i).fg.IsViable X := by
  have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    split_ifs with h
    · exact absurd h (frame_no_contest_of hr hfg hf hy hsrc hGG)
    · rfl
  by_cases hle : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
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
  refine ⟨D, E, X, hD, hDs, hE, below_entry hr hfg hy hB hE hDs (hGB D hD) (by omega),
    hEh.trans hfl.symm, hX, hEX, ?_⟩
  change (tr.state y i).fg.headHeightFloor ≤ _
  omega

/-- Compatible source geometry makes a held block an ancestor of the floor or fully viable. -/
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
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact J_compatible hr hfg hf hy hsrc hGB (hsU hBt.1)
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (Frame.anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := Frame.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  rcases floor_or_crossing_of hr hfg hf hy hsrc hGG hGB hBt.1 with hle | ⟨-, E, X, -, -, -, hBE,
    -, hX, hEX, hXv⟩
  · exact ⟨hBt, hΦfB, B, hBt, ⟨hBt.1, hBt.2, Anc.mono hΦs hΦfB, hle⟩, .refl⟩
  · have hBX := hBE.trans hEX
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hBt.2.trans hBX⟩
    exact ⟨hBt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, (Anc.mono hΦs hΦfB).trans hBX, hXv⟩,
      Frame.anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBX) hXΦ⟩

end Consensus.Goldilocks.Compose.FrameGeometry

end
