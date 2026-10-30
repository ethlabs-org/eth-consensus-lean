module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views

public section

/-! # Goldilocks SA: lock functions (A0.4 (c)–(e))

Facts about `live_locks`, `add_locks` and `unlock` in any well-formed frame: locks only move
back and keep their slot and fast bit, unlocking is idempotent, and with fewer than `n/2`
equivocators `Φ.F` has fewer than half of the committee as opponents. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- `live_locks` moves each lock to an ancestor in the tree, with its slot and fast bit. -/
theorem liveLocks_movesBack {FGP : Type} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set Lock)
    (t : Time) : MovesBack sp Φ L (liveLocks sp L Φ t) := by
  rintro l' ⟨l, hl, B, hB, hr, -, rfl⟩
  exact ⟨l, hl, rfl, rfl, B, hB, hr, _, (viableAncestor_anc hΦ hB).1, rfl,
    (viableAncestor_anc hΦ hB).2⟩

/-- Where `unlock` moves a lock is an ancestor of the lock's block, in the tree. -/
theorem unlockTarget_anc {FGP : Type} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n)
    (s : Int) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) :
    unlockTarget sp Φ V s B ∈ Φ.tree ∧ Φ.Anc (unlockTarget sp Φ V s B) B := by
  unfold unlockTarget
  cases h : deepest Φ _ with
  | none => exact ⟨hΦ.rooted.1, hΦ.rooted.2 B hB⟩
  | some D => exact ⟨(deepest_mem h).1.1, (deepest_mem h).1.2.1⟩

/-- **A0.4 (c).** -/
theorem locks_move_back : LocksMoveBack sp := by
  intro FGP Φ L t hΦ
  refine ⟨liveLocks_movesBack sp hΦ L t, fun s N => liveLocks_movesBack sp hΦ _ t, fun s V => ?_⟩
  rintro l' ⟨l, hl, B, hB, hr, rfl⟩
  obtain ⟨l₀, hl₀, hs, hf, B₀, hB₀, hr₀, B₁, hB₁, hr₁, hB₁B₀⟩ := liveLocks_movesBack sp hΦ L t l hl
  have hBB₁ : B = B₁ := hΦ.coherent.1 hB hB₁ (hr.trans hr₁.symm)
  subst hBB₁
  split_ifs
  · exact ⟨l₀, hl₀, hs, hf, B₀, hB₀, hr₀, _, (unlockTarget_anc sp hΦ V s hB).1, rfl,
      (unlockTarget_anc sp hΦ V s hB).2.trans hB₁B₀⟩
  · exact ⟨l₀, hl₀, hs, hf, B₀, hB₀, hr₀, B, hB, hr, hB₁B₀⟩

/-- **A0.4 (d).** -/
theorem unlock_idempotent : UnlockIdempotent sp := by
  sorry

/-- **A0.4 (e).** -/
theorem unlock_no_fallback : UnlockNoFallback sp := by
  intro FGP Φ V s hΦ he
  rwa [opponents_F sp hΦ]

end Consensus.Goldilocks.SA

end
