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
    ∀ l ∈ unlock sp L Φ t s V, ∃ B ∈ Φ.tree, B.root = l.block ∧ l.LiveAt sp t ∧
      Φ.viableAncestor B = B ∧ ((l.slot : Int) < s → unlockTarget sp Φ V s B = B) := by
  rintro _ ⟨_, ⟨l₀, -, B₀, hB₀, -, hlive, rfl⟩, B, hB, hBr, rfl⟩
  obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB₀
  obtain rfl : B = Φ.viableAncestor B₀ := hΦ.coherent.1 hB hvt hBr
  have hcand := (viableAncestor_spec hΦ hB₀).2.1
  dsimp only at hlive ⊢
  split_ifs with hlt
  · obtain ⟨hTt, hTB⟩ := unlockTarget_anc sp hΦ V s hB
    refine ⟨_, hTt, rfl, hlive, viableAncestor_self hΦ hTt ?_, fun _ => unlockTarget_idem hΦ V s hB⟩
    exact (candidate_of_anc hΦ hTB hcand).symm
  · exact ⟨_, hB, rfl, hlive, viableAncestor_self hΦ hB hcand.symm, fun h => absurd h hlt⟩

variable (sp)

/-- **A0.4 (d).** -/
theorem unlock_idempotent : UnlockIdempotent sp := by
  intro FGP Φ L t s V hΦ
  have hfix := unlock_fixed hΦ L t s V
  -- the second unlocking returns each lock of the first unchanged
  have hid : ∀ l ∈ unlock sp L Φ t s V, ∀ B ∈ Φ.tree, B.root = l.block →
      (if (l.slot : Int) < s then
        (⟨(unlockTarget sp Φ V s B).root, l.slot, l.fast, l.expiry⟩ : Lock) else l) = l := by
    intro l hl B hB hBr
    obtain ⟨B₁, hB₁, hB₁r, -, -, hT⟩ := hfix l hl
    obtain rfl : B = B₁ := hΦ.coherent.1 hB hB₁ (hBr.trans hB₁r.symm)
    split_ifs with h
    · rw [hT h, hBr]
    · rfl
  have hlive : ∀ l ∈ unlock sp L Φ t s V,
      ∃ B ∈ Φ.tree, B.root = l.block ∧ l.LiveAt sp t ∧
        l = ⟨(Φ.viableAncestor B).root, l.slot, l.fast, l.expiry⟩ := by
    intro l hl
    obtain ⟨B, hB, hBr, hk, hva, -⟩ := hfix l hl
    exact ⟨B, hB, hBr, hk, by rw [hva, hBr]⟩
  ext l
  constructor
  · rintro ⟨l', ⟨l₁, hl₁, B₁, hB₁, hB₁r, -, rfl⟩, B, hB, hBr, rfl⟩
    obtain ⟨B₂, hB₂, hB₂r, -, hva, -⟩ := hfix l₁ hl₁
    obtain rfl : B₁ = B₂ := hΦ.coherent.1 hB₁ hB₂ (hB₁r.trans hB₂r.symm)
    have he : (⟨(Φ.viableAncestor B₁).root, l₁.slot, l₁.fast, l₁.expiry⟩ : Lock) = l₁ := by
      rw [hva, hB₁r]
    rw [he] at hBr ⊢
    rw [hid l₁ hl₁ B hB hBr]
    exact hl₁
  · intro hl
    obtain ⟨B, hB, hBr, hk, he⟩ := hlive l hl
    exact ⟨l, ⟨l, hl, B, hB, hBr, hk, he⟩, B, hB, hBr, (hid l hl B hB hBr).symm⟩

end Consensus.Goldilocks.SA

end
