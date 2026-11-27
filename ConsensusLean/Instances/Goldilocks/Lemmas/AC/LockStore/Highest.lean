module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Inv

public section

/-! # Characterising the anchor and live-lock conflicts -/

namespace Consensus.Goldilocks.AC

variable {sp : ACParams} {FGP : Type} {Φ : Frm sp.n FGP} {L : Set Lock} {t : Time}
  {C : Blk sp.n FGP}

/-- The anchor is the deepest live lock block or finalised root, on a well-formed frame. -/
theorem getAnchor_eq_deepest_union (_hΦ : FrameOK Φ) (A : ACState sp.n) (t : Time) :
    getAnchor sp A Φ t =
      (deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot})).getD Φ.fcRoot := by
  rfl

/-- A conflict has a live lock block as a witness. -/
theorem exists_of_conflictsWithLock (h : conflictsWithLock sp L Φ t C) :
    ∃ B ∈ liveLockBlocks sp L Φ t, ¬ Compatible Φ.tree C B := h

/-- Compatibility with every live lock block rules out a conflict. -/
theorem not_conflictsWithLock_of_forall
    (h : ∀ B ∈ liveLockBlocks sp L Φ t, Compatible Φ.tree C B) :
    ¬ conflictsWithLock sp L Φ t C := by
  intro hc
  obtain ⟨B, hB, hCB⟩ := exists_of_conflictsWithLock hc
  exact hCB (h B hB)

/-- An ancestor of a block that conflicts with no live lock conflicts with no live lock. -/
theorem not_conflictsWithLock_of_anc (hΦ : FrameOK Φ) {D : Blk sp.n FGP}
    (hCD : Φ.Anc C D) (hnv : ¬ conflictsWithLock sp L Φ t D) :
    ¬ conflictsWithLock sp L Φ t C := by
  apply not_conflictsWithLock_of_forall
  intro W hW
  have hDW : Compatible Φ.tree D W := by
    by_contra h
    exact hnv ⟨W, hW, h⟩
  rcases hDW with h | h
  · exact Or.inl (hCD.trans h)
  · exact anc_total hΦ.coherent hCD h

end Consensus.Goldilocks.AC

end
