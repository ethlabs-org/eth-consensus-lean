module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: unlocking is idempotent (A0.4 (d))

Every lock that `unlock` returns is live and on a block that is its own viable ancestor (a lock
block moved back to a candidate of `viable_ancestor` is moved to an ancestor that is again a
candidate) and, for a slot below `s`, its own unlock target (the deepest block below it with few
opponents is itself; when there is none, the target is `Φ.F`, whose own target is `Φ.F`). So a
second `unlock` returns each lock unchanged. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- A block below a candidate of `viable_ancestor` is a candidate. -/
private theorem candidate_of_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {X B : Blk sp.n FGP}
    (hXB : Φ.Anc X B) (hB : Φ.AncestorCandidate B) : Φ.AncestorCandidate X := by
  rcases hB with hB | ⟨hBt, hfB, W, hW, hWv, hBW⟩
  · exact Or.inl (hXB.trans hB)
  · rcases anc_total hΦ.coherent hXB hfB with h | h
    · exact Or.inl h
    · exact Or.inr ⟨mem_of_anc hXB hBt, h, W, hW, hWv, hXB.trans hBW⟩

/-- The set of blocks that `unlock` reads below `X`. -/
private abbrev Few (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (X : Blk sp.n FGP) :
    Set (Blk sp.n FGP) :=
  {B' | B' ∈ Φ.tree ∧ Φ.Anc B' X ∧ 2 * (opponents sp Φ V s B').ncard < sp.n}

/-- The unlock target of an unlock target is itself. -/
private theorem unlockTarget_idem {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) :
    unlockTarget sp Φ V s (unlockTarget sp Φ V s B) = unlockTarget sp Φ V s B := by
  have hsub : ∀ {X}, Φ.Anc X B → Few Φ V s X ⊆ Few Φ V s B :=
    fun hXB B' hB' => ⟨hB'.1, hB'.2.1.trans hXB, hB'.2.2⟩
  unfold unlockTarget
  rcases hd : deepest Φ (Few Φ V s B) with _ | D
  · -- no block below `B` has few opponents: the target is `Φ.F`, and so is its target
    have hempty : Few Φ V s B = ∅ := by
      by_contra hne
      obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X hX => hX.1) (Set.nonempty_iff_ne_empty.2 hne)
      rw [hd] at hD
      cases hD
    have hF : deepest Φ (Few Φ V s Φ.F) = none := by
      rcases hd' : deepest Φ (Few Φ V s Φ.F) with _ | D
      · rfl
      · have := hsub (hΦ.rooted.2 B hB) (deepest_mem hd').1
        rw [hempty] at this
        exact absurd this (Set.notMem_empty _)
    simp only [Option.getD_none]
    rw [hF]
    rfl
  · obtain ⟨⟨hDt, hDB, hDf⟩, -⟩ := deepest_mem hd
    simp only [Option.getD_some]
    rcases hd' : deepest Φ (Few Φ V s D) with _ | D'
    · obtain ⟨D'', hD''⟩ := exists_deepest hΦ (S := Few Φ V s D) (fun X hX => hX.1)
        ⟨D, hDt, .refl, hDf⟩
      rw [hd'] at hD''
      cases hD''
    · obtain ⟨⟨hD't, hD'D, -⟩, hmax⟩ := deepest_mem hd'
      simp only [Option.getD_some]
      by_contra hne
      rcases hmax D ⟨hDt, .refl, hDf⟩ (Ne.symm hne) with h | ⟨h, -⟩ <;>
        have := depth_lt_of_anc hΦ hD'D hne hDt <;> omega

/-- Every lock that `unlock` returns is live, on a block that is its own viable ancestor and,
for a slot below `s`, its own unlock target. -/
private theorem unlock_fixed {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set Lock) (t : Time)
    (s : Int) (V : View sp.n) :
    ∀ l ∈ unlock sp L Φ t s V, ∃ B ∈ Φ.tree, B.root = l.block ∧ sp.slot t ≤ l.slot + sp.k ∧
      Φ.viableAncestor B = B ∧ ((l.slot : Int) < s → unlockTarget sp Φ V s B = B) := by
  sorry

variable (sp)

/-- **A0.4 (d).** -/
theorem unlock_idempotent : UnlockIdempotent sp := by
  sorry

end Consensus.Goldilocks.SA

end
