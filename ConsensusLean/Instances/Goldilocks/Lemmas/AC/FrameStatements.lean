module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FrameClaims
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks: the frame statements, assembled (G0.3, G0.4 (frame))

`FrameStatements` (`Lemmas/AC/FrameClaims`):

* G0.4 (frame): the viable ancestor exists and is unique (`viableAncestor_spec` and antisymmetry),
  a candidate is its own (`viableAncestor_self`), the viable tree is closed under ancestors down
  to `fc_root` (from its definition), and the tree is parent-closed down to `Φ.F` (rootedness and
  coherence).
* G0.3 (frame): a step adds exactly its block (`FrameStep.tree_eq`). Along a frame sequence in a
  coherent `U`, every frame is rooted (a step keeps the blocks that extend the new tip, and their
  paths), and the finalized tip only moves forward in `U`. So a block of an earlier tree that
  extends a later tip is in the later tree (retention, by induction over the steps: ancestry in
  `U` between blocks of a rooted tree inside `U` is ancestry in that tree); a block that left
  never returns (its return would extend the later tip, so by retention it never left); and a
  block enters at most once (a second entry would be a return). -/

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type}

/-! ## G0.4 (frame) -/

theorem viable_ancestor_exists : ViableAncestorExists := by
  rw [viableAncestorExists_iff]
  intro n FGP ACP Φ B hΦ hB
  have hs := SA.viableAncestor_spec hΦ hB
  refine ⟨hs, fun A hA => ?_⟩
  exact Anc.antisymm hΦ.coherent (hs.2.2 A hA.1 hA.2.1) (hA.2.2 _ hs.1 hs.2.1)

theorem viable_ancestor_self : ViableAncestorSelf := by
  rw [viableAncestorSelf_iff]
  intro n FGP ACP Φ B hΦ hc
  have hB : B ∈ Φ.tree := by
    rcases hc with h | h
    · exact h.1
    · exact SA.mem_of_anc h hΦ.fcRoot_mem
  exact SA.viableAncestor_self hΦ hB hc

theorem viable_tree_ancestor_closed : ViableTreeAncestorClosed := by
  rw [viableTreeAncestorClosed_iff]
  rintro n FGP ACP Φ S A B ⟨-, -, W, hW, hWh, hBW⟩ hA hFA hAB
  exact ⟨hA, hFA, W, hW, hWh, hAB.trans hBW⟩

theorem frame_parent_closed : FrameParentClosed := by
  rw [frameParentClosed_iff]
  intro n FGP ACP Φ C hΦ hC hne
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 C hC) with h | ⟨P, -, hP⟩
  · exact absurd h hne
  · exact ⟨P, hP.1, hP.2.2, hΦ.coherent.2 P hP.1 C hP.2.1 hP.2.2⟩

/-! ## G0.3 (frame) -/

theorem frame_step_adds_block : FrameStepAddsBlock := by
  rw [frameStepAddsBlock_iff]
  intro n FGP ACP Φ Φ' B h
  rw [h.tree_eq]
  exact ⟨⟨Set.mem_insert _ _, h.F'_anc_B⟩, fun X hX => hX.1⟩

/-- Ancestry inside a coherent `U` between blocks of a set `S ⊆ U` rooted at `F` (every block
of `S` extends `F` inside `S`) is ancestry inside `S`. -/
private theorem anc_of_anc_U {U S : Set (Block n FGP ACP)} (hU : Coherent U) (hSU : S ⊆ U)
    {F : Block n FGP ACP} (hroot : ∀ C ∈ S, Anc S F C) {B C : Block n FGP ACP} (hB : B ∈ S)
    (h : Anc U B C) : C ∈ S → Anc S B C := by
  induction h with
  | refl => exact fun _ => .refl
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = F
    · subst hdF
      have := Anc.antisymm hU (hBc.tail e) ((hroot B hB).mono hSU)
      exact this ▸ .refl
    obtain rfl | ⟨p, -, hp⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hroot d hd)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hSU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    subst hpc
    exact (ih hp.1).tail hp

/-- A step's new tree is rooted at its new tip (and its blocks keep their paths). -/
private theorem FrameStep.rooted' {Φ Φ' : Frame n FGP ACP} {B : Block n FGP ACP}
    (h : FrameStep Φ B Φ') : Φ'.Rooted := by
  have hF' : Φ'.F ∈ insert B Φ.tree := by
    by_cases he : Φ'.F = B
    · exact he ▸ Set.mem_insert _ _
    · exact (Anc.mem h.F'_anc_B he).1
  refine ⟨by rw [h.tree_eq]; exact ⟨hF', .refl⟩, fun C hC => ?_⟩
  change Anc Φ'.tree Φ'.F C
  rw [h.tree_eq] at hC ⊢
  exact Anc.restrict .refl hC.2

section Seq

variable {Φ : Nat → Frame n FGP ACP} {U : Set (Block n FGP ACP)}

/-- The new block of a step of a sequence inside `U` is in `U`, and so is `insert B` of the
previous tree. -/
private theorem insert_subset (h : FrameSeqIn Φ U) {i : Nat} {B : Block n FGP ACP}
    (hs : FrameStep (Φ i) B (Φ (i + 1))) : insert B (Φ i).tree ⊆ U := by
  have hB : B ∈ (Φ (i + 1)).tree := (frameStepAddsBlock_iff.mp frame_step_adds_block
    n FGP ACP _ _ B hs).1
  exact Set.insert_subset (h.subset _ hB) (h.subset i)

/-- Every frame of a sequence inside `U` is rooted. -/
private theorem rooted (h : FrameSeqIn Φ U) (i : Nat) : (Φ i).Rooted := by
  induction i with
  | zero => exact h.rooted
  | succ i ih =>
    rcases frameSeq_iff.mp h.seq i with he | ⟨B, hs⟩
    · exact he ▸ ih
    · exact hs.rooted'

/-- The finalized tip moves forward inside `U`. -/
private theorem F_mono (h : FrameSeqIn Φ U) {i j : Nat} (hij : i ≤ j) :
    Anc U (Φ i).F (Φ j).F := by
  induction hij with
  | refl => exact .refl
  | @step j _ ih =>
    rcases frameSeq_iff.mp h.seq j with he | ⟨B, hs⟩
    · exact he ▸ ih
    · exact ih.trans (hs.F_anc_F'.mono (insert_subset h hs))

theorem frame_retention : FrameRetention := by
  rw [frameRetention_iff]
  intro n FGP ACP Φ U h i j hij X hX hFX
  induction hij with
  | refl => exact hX
  | @step j hij ih =>
    rcases frameSeq_iff.mp h.seq j with he | ⟨B, hs⟩
    · rw [he] at hFX ⊢
      exact ih hFX
    · have hIU := insert_subset h hs
      have hXj : X ∈ (Φ j).tree := ih ((F_mono h (Nat.le_succ j)).trans hFX)
      -- `insert B (Φ j).tree` is rooted at `(Φ j).F`
      have hroot : ∀ C ∈ insert B (Φ j).tree, Anc (insert B (Φ j).tree) (Φ j).F C := by
        rintro C (rfl | hC)
        · obtain ⟨P, hP, hPr⟩ := hs.parent_mem
          exact (((rooted h j).2 P hP).mono (Set.subset_insert _ _)).tail
            ⟨Set.mem_insert_of_mem _ hP, Set.mem_insert _ _, hPr⟩
        · exact ((rooted h j).2 C hC).mono (Set.subset_insert _ _)
      have hF'm : (Φ (j + 1)).F ∈ insert B (Φ j).tree := by
        by_cases he : (Φ (j + 1)).F = B
        · exact he ▸ Set.mem_insert _ _
        · exact (Anc.mem hs.F'_anc_B he).1
      rw [hs.tree_eq]
      exact ⟨Set.mem_insert_of_mem _ hXj,
        anc_of_anc_U h.coherent hIU hroot hF'm hFX (Set.mem_insert_of_mem _ hXj)⟩

theorem frame_never_returns : FrameNeverReturns := by
  rw [frameNeverReturns_iff]
  intro n FGP ACP Φ U h i j k hij hjk X hX hXj hXk
  have hFk : Anc U (Φ k).F X := ((rooted h k).2 X hXk).mono (h.subset k)
  exact hXj (frameRetention_iff.mp frame_retention
    n FGP ACP Φ U h i j hij X hX ((F_mono h hjk).trans hFk))

theorem frame_enters_once : FrameEntersOnce := by
  rw [frameEntersOnce_iff]
  intro n FGP ACP Φ U h i j B hi hj
  have key : ∀ {a b}, a < b → FrameStep (Φ a) B (Φ (a + 1)) → FrameStep (Φ b) B (Φ (b + 1)) →
      False := fun {a b} hab ha hb =>
    frameNeverReturns_iff.mp frame_never_returns
      n FGP ACP Φ U h (a + 1) b (b + 1) hab (Nat.le_succ b) B
      (frameStepAddsBlock_iff.mp frame_step_adds_block n FGP ACP _ _ B ha).1 hb.new
      (frameStepAddsBlock_iff.mp frame_step_adds_block n FGP ACP _ _ B hb).1
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact (key hlt hi hj).elim
  · exact heq
  · exact (key hgt hj hi).elim

end Seq

/-- **The frame statements.** -/
theorem frame_statements : FrameStatements where
  viableAncestorExists := viable_ancestor_exists
  viableAncestorSelf := viable_ancestor_self
  viableTreeAncestorClosed := viable_tree_ancestor_closed
  parentClosed := frame_parent_closed
  stepAddsBlock := frame_step_adds_block
  retention := frame_retention
  neverReturns := frame_never_returns
  entersOnce := frame_enters_once

end Consensus.Goldilocks

end
