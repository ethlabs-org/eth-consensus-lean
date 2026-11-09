module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameSourceGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Viable-ancestor candidacy from honest FG rows

A held block compatible with the sources remains a candidate even when the sources are
not pairwise compatible. This is geometry of the actual FG stores over any AC. -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {proposer : Nat → Fin P.n}

private theorem entry_compatible (hr : Node.LocalRun proposer dg H sg tr)
    (hf : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat} {D E B : A.Blk}
    (hDs : IsHonestSource tr H D E.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hDB : Compatible (tr.HonestBlocks H) D B) : Compatible (tr.HonestBlocks H) E B := by
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hr hf hDs ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono fun _ hX => ⟨x, hx, k, hX⟩
  rcases hDB with h | h
  · exact Or.inl (hEDU.trans h)
  · exact Anc.total hf.coherent hEDU h

/-- Ancestry in a coherent universe restricts to a rooted frame containing both endpoints,
for arbitrary FG and AC payloads. -/
theorem anc_tree_of_anc_U {n : Nat} {FGP ACP : Type} {U : Set (Block n FGP ACP)}
    (hU : Coherent U) {Φ : Frame n FGP ACP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {B C : Block n FGP ACP} (hB : B ∈ Φ.tree) (h : Anc U B C) : C ∈ Φ.tree → Φ.Anc B C := by
  induction h with
  | refl => exact fun _ => Relation.ReflTransGen.refl
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      have := Anc.antisymm hU (hBc.tail e) ((hΦ.rooted.2 B hB).mono hΦU)
      exact this ▸ Relation.ReflTransGen.refl
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    subst hpc
    exact (ih hp.1).tail hp

/-- A held block compatible with every source stays a viable-ancestor candidate. -/
theorem held_candidate_of_rows (hr : Node.LocalRun proposer dg H sg tr)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) (i : Nat)
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) {B : A.Blk}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := hfg.coherent
  have hR := fg_reachable hr hy i
  have hΦ : FrameOK (Node.frame (tr.state y i)) := (Store.frame_realization _ _ _ _ hR).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hΦs : (Node.frame (tr.state y i)).tree ⊆ (tr.state y i).fg.tree := fun X hX => hX.1
  have hsU : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fg_tree_subset_honest hy i
  have hJB := J_compatible_before hr hfg hf hy hsrc hGB (hsU hBt.1)
  have hfc : Compatible (tr.HonestBlocks H) (Node.frame (tr.state y i)).fcRoot B := by
    change Compatible _ (tr.state y i).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hJB
    · exact Or.inl (hBt.2.mono hsU)
  rcases hfc with hfB | hBf
  swap
  · exact Or.inl (anc_tree_of_anc_U hU hΦ hΦU hBt hBf hΦ.fcRoot_mem)
  have hΦfB := anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  right
  by_cases hA : ∃ X ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc B X ∧
      (tr.state y i).fg.IsViable X
  · obtain ⟨X, hX, hBX, hXv⟩ := hA
    have hXΦ : X ∈ (Node.frame (tr.state y i)).tree := ⟨hX, hBt.2.trans hBX⟩
    exact ⟨hBt, hΦfB, X, hXΦ, ⟨hX, hXΦ.2, (Anc.mono hΦs hΦfB).trans hBX, hXv⟩,
      anc_tree_of_anc_U hU hΦ hΦU hBt (Anc.mono hsU hBX) hXΦ⟩
  exfalso
  push Not at hA
  have hB := hBt.1
  obtain ⟨-, hJ, -, ⟨Z, hZ, -, hZj⟩, hZm, ⟨XM, hXM, hXMh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hgen := (Store.accepted_tree _ _ _ _ hR).2.2.2
  have hB1 := (honest_held_chain hr hy hB).1
  have hBfl : ((tr.state y i).fg.σ B.root).h < (tr.state y i).fg.headHeightFloor :=
    lt_of_not_ge (hA B hB .refl)
  have hflM : (tr.state y i).fg.headHeightFloor ≤ (tr.state y i).fg.hmax := by
    unfold Store.headHeightFloor; split_ifs <;> omega
  have entry_below : ∀ W ∈ (tr.state y i).fg.tree,
      ((tr.state y i).fg.σ W.root).h = (tr.state y i).fg.hmax → 2 ≤ (tr.state y i).fg.hmax →
      ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧ (tr.state y i).fg.Anc E B ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.hmax - 1 ∧
        ((tr.state y i).fg.σ E.root).Th = E.root := by
    intro W hW hWh hM
    obtain ⟨E, hE, hEW, hEh, hET, D, hD, hDs⟩ :=
      frame_crossing_source_before hr hfg hf hy hsrc hW (j := (tr.state y i).fg.hmax - 1)
        (by omega) (by omega)
    refine ⟨E, hE, hEW, ?_, hEh, hET⟩
    rcases entry_compatible hr hfg hy hDs hE (hGB D hD) with h | h
    · exact honest_held_anc hr hfg hy h hB
    · have hBW : (tr.state y i).fg.Anc B W :=
        honest_held_anc hr hfg hy (h.trans (hEW.mono hsU)) hW
      have := hA W hW hBW
      unfold Store.IsViable at this
      omega
  have hM2 : 2 ≤ (tr.state y i).fg.hmax := by
    by_cases hc : (tr.state y i).fg.Contest
    · obtain ⟨hmj, Y, hY, -, -, hJY⟩ := hc
      by_cases h0 : (tr.state y i).fg.hj = 0
      · exact absurd (by rw [justified_genesis hr h0 hy]; exact hgen Y hY) hJY
      · omega
    · have : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
        unfold Store.headHeightFloor; simp only [hc, ite_false]
      omega
  obtain ⟨E, -, -, hEB, hEh, -⟩ := entry_below XM hXM hXMh hM2
  have hEBh := (honest_held_height hr hfg hy hEB).1
  have hc : (tr.state y i).fg.Contest := by
    by_contra hc
    have : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
      unfold Store.headHeightFloor; simp only [hc, ite_false]
    omega
  obtain ⟨hmj, Y, hY, -, hYh, hJY⟩ := hc
  obtain ⟨EY, -, hEYY, hEYB, hEYh, hEYT⟩ := entry_below Y hY hYh hM2
  obtain ⟨hJh, hJT, -⟩ := justified_honest_source_before hr hfg hf hy hsrc (by omega)
  have hJEY : (tr.state y i).fg.J = EY := by
    rcases hJB with h | h
    · exact held_entry_unique hr hfg hy hB (honest_held_anc hr hfg hy h hB) hEYB
        (by rw [hJh, hEYh]; omega) hJT hEYT
    · have hBJ := honest_held_anc hr hfg hy h hJ
      exact held_entry_unique hr hfg hy hJ .refl (hEYB.trans hBJ)
        (by rw [hJh, hEYh]; omega) hJT hEYT
  exact hJY (hJEY ▸ hEYY)

end Consensus.Goldilocks.Compose.FrameGeometry

end
