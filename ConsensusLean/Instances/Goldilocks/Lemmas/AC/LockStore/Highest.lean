module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Inv

public section

/-! # Characterising the anchor and live-lock conflicts -/

namespace Consensus.Goldilocks.AC

variable {sp : ACParams} {FGP : Type} {Φ : Frm sp.n FGP} {L : Set Lock} {t : Time}
  {C : Blk sp.n FGP}

private theorem deepest_eq_of_isDeepest {S : Set (Blk sp.n FGP)} {B : Blk sp.n FGP}
    (hB : IsDeepest Φ S B) : deepest Φ S = some B := by
  classical
  unfold deepest
  have he : ∃ D, IsDeepest Φ S D := ⟨B, hB⟩
  rw [dite_eq_left he]
  congr 1
  by_contra hn
  have hd := he.choose_spec
  rcases hd.2 B hB.1 (Ne.symm hn) with h | ⟨h, hr⟩ <;>
    rcases hB.2 he.choose hd.1 hn with h' | ⟨h', hr'⟩ <;> omega

/-- The anchor is the deepest live lock block or finalised root, on a well-formed frame. -/
theorem getAnchor_eq_deepest_union (hΦ : FrameOK Φ) (A : ACState sp.n) (t : Time) :
    getAnchor sp A Φ t =
      (deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot})).getD Φ.fcRoot := by
  classical
  have hfc : ∀ B ∈ liveLockBlocks sp A.locks Φ t, Compatible Φ.tree B Φ.fcRoot := by
    rintro B ⟨hBt, l', ⟨l, hl, B₀, hB₀, hBr, ht, rfl⟩, hr⟩
    have he : B = Φ.viableAncestor B₀ :=
      hΦ.coherent.1 hBt (viableAncestor_anc hΦ hB₀).1 hr.symm
    subst B
    exact (viableAncestor_spec hΦ hB₀).2.1.elim Or.inl (fun h => Or.inr h.2.1)
  unfold getAnchor
  cases hh : highestLiveLock sp A.locks Φ t with
  | none =>
    have hempty : liveLockBlocks sp A.locks Φ t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨D, hd⟩ := exists_deepest hΦ (fun _ h => h.1) ⟨B, hB⟩
      rw [show deepest Φ (liveLockBlocks sp A.locks Φ t) = none from hh] at hd
      cases hd
    have hd := deepest_eq_of_isDeepest (Φ := Φ)
      (S := liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot})
      (B := Φ.fcRoot) ⟨Or.inr rfl, by simp [hempty]⟩
    rw [hd]; rfl
  | some H =>
    have hH := deepest_mem hh
    dsimp only
    split_ifs with hlt
    · have hd : IsDeepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) H := by
        refine ⟨Or.inl hH.1, ?_⟩
        rintro B (hB | hB) hn
        · exact hH.2 B hB hn
        · obtain rfl := Set.mem_singleton_iff.mp hB
          exact Or.inl hlt
      rw [deepest_eq_of_isDeepest hd]; rfl
    · have hd : IsDeepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) Φ.fcRoot := by
        refine ⟨Or.inr rfl, ?_⟩
        rintro B (hB | hB) hn
        · have hdep : depth Φ B ≤ depth Φ H := by
            by_cases he : B = H
            · exact he ▸ le_rfl
            · rcases hH.2 B hB he with h | ⟨h, -⟩ <;> omega
          rcases hfc B hB with h | h
          · exact Or.inl (depth_lt_of_anc hΦ h hn hΦ.fcRoot_mem)
          · have := depth_lt_of_anc hΦ h (Ne.symm hn) hB.1
            omega
        · exact False.elim (hn (Set.mem_singleton_iff.mp hB))
      rw [deepest_eq_of_isDeepest hd]; rfl

/-- A conflict has a live lock block as a witness. -/
theorem exists_of_conflictsWithLock (h : conflictsWithLock sp L Φ t C) :
    ∃ B ∈ liveLockBlocks sp L Φ t, ¬ Compatible Φ.tree C B := by
  obtain ⟨B, hB, hn⟩ := h
  exact ⟨B, (deepest_mem hB).1, hn⟩

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
  rintro ⟨W, hW, hCW⟩
  have hDW : Compatible Φ.tree D W := by
    by_contra h
    exact hnv ⟨W, hW, h⟩
  apply hCW
  rcases hDW with h | h
  · exact Or.inl (hCD.trans h)
  · exact anc_total hΦ.coherent hCD h

end Consensus.Goldilocks.AC

end
