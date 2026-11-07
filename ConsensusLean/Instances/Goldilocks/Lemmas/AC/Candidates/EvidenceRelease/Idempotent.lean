module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Unlock

public section

/-! # Candidate `evidence-release`: the weighted unlock is idempotent

Two idempotent stages need not compose to an idempotent map; here the composition `E ∘ unlock` is
idempotent by an absorption argument. Let `Y` be the block of a lock of `unlockW`, `T` its parent
target:

* the parent fixes `Y`: `Y` is its own viable ancestor (a block below a candidate is a candidate),
  and either `T` has few opponents, and then so does `Y ⪯ T` (an opponent of `Y` is an opponent
  of `T`, `opponents_anc`), or `T = Φ.F`, and then `Y = Φ.F`, whose target is `Φ.F`;
* the evidence stage fixes `Y`: it reads the same view and the same weight, and either `Y` was
  chosen as the deepest keepable block below `T`, so it is the deepest keepable block below
  itself, or `Y = Φ.F` by the fallback, and no block below `Φ.F` is keepable either. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-- A block below a candidate of `viable_ancestor` is a candidate. -/
private theorem candidate_of_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {X B : Blk sp.n FGP}
    (hXB : Φ.Anc X B) (hB : Φ.AncestorCandidate B) : Φ.AncestorCandidate X := by
  rcases hB with hB | ⟨hBt, hfB, W, hW, hWv, hBW⟩
  · exact Or.inl (hXB.trans hB)
  · rcases anc_total hΦ.coherent hXB hfB with h | h
    · exact Or.inl h
    · exact Or.inr ⟨mem_of_anc hXB hBt, h, W, hW, hWv, hXB.trans hBW⟩

/-- An opponent of a block is an opponent of every descendant: a head incompatible with `Y` is
incompatible with every `D ⪰ Y`. -/
theorem opponents_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    {Y D : Blk sp.n FGP} (hYD : Φ.Anc Y D) : opponents sp Φ V s Y ⊆ opponents sp Φ V s D := by
  rintro i (hi | ⟨x, hx, hxi, hs, H, hH, hHr, hc⟩)
  · exact Or.inl hi
  · refine Or.inr ⟨x, hx, hxi, hs, H, hH, hHr, fun hHD => hc ?_⟩
    rcases hHD with h | h
    · exact anc_total hΦ.coherent h hYD
    · exact Or.inr (hYD.trans h)

/-- The block of `Φ.F` is the only block of the tree at or below `Φ.F`. -/
private theorem eq_F_of_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {Y : Blk sp.n FGP}
    (hY : Y ∈ Φ.tree) (h : Φ.Anc Y Φ.F) : Y = Φ.F :=
  Anc.antisymm hΦ.coherent h (hΦ.rooted.2 Y hY)

/-- The parent's target of its own target, or of any block at or below it in the tree, when that
block is the evidence stage's choice: the parent leaves it in place. -/
private theorem unlockTarget_fix {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    {B Y : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hY : Y ∈ Φ.tree)
    (hYT : Φ.Anc Y (unlockTarget sp Φ V s B)) : unlockTarget sp Φ V s Y = Y := by
  have hsub : ∀ {X}, Φ.Anc X B →
      {B' | B' ∈ Φ.tree ∧ Φ.Anc B' X ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} ⊆
      {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} :=
    fun hXB B' hB' => ⟨hB'.1, hB'.2.1.trans hXB, hB'.2.2⟩
  have hT : unlockTarget sp Φ V s B = _ := rfl
  unfold unlockTarget at hYT hT
  rcases hd : deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n}
    with _ | D
  · rw [hd, Option.getD_none] at hYT
    obtain rfl := eq_F_of_anc hΦ hY hYT
    have hempty :
        {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} = ∅ := by
      by_contra hne
      obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X hX => hX.1) (Set.nonempty_iff_ne_empty.2 hne)
      rw [hd] at hD
      cases hD
    unfold unlockTarget
    rcases hd' : deepest Φ
        {B' | B' ∈ Φ.tree ∧ Φ.Anc B' Φ.F ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} with _ | D'
    · rfl
    · have := hsub (hΦ.rooted.2 B hB) (deepest_mem hd').1
      rw [hempty] at this
      exact absurd this (Set.notMem_empty _)
  · rw [hd, Option.getD_some] at hYT
    obtain ⟨⟨-, -, hDf⟩, -⟩ := deepest_mem hd
    refine unlockTarget_eq_self hΦ V s hY (lt_of_le_of_lt ?_ hDf)
    exact Nat.mul_le_mul_left 2 (Set.ncard_le_ncard (opponents_anc hΦ V s hYT) (Set.toFinite _))

/-- The evidence target depends on the lock only through its weight. -/
private theorem evidenceTarget_weight {Φ : Frm sp.n FGP} {V : View sp.n} {s : Int}
    {w w' : WLock} (h : w.weight = w'.weight) (T : Blk sp.n FGP) :
    evidenceTarget sp Φ V s w T = evidenceTarget sp Φ V s w' T := by
  rw [evidenceTarget_eq, evidenceTarget_eq, keepable_weight h]

/-- The evidence stage leaves its own choice in place. -/
private theorem evidenceTarget_fix {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    (w : WLock) {T : Blk sp.n FGP} (hT : T ∈ Φ.tree) :
    evidenceTarget sp Φ V s w (evidenceTarget sp Φ V s w T) = evidenceTarget sp Φ V s w T := by
  have hsub : ∀ {X}, Φ.Anc X T → keepable sp Φ V s w X ⊆ keepable sp Φ V s w T :=
    fun hXT Y hY => mem_keepable.2 ⟨(mem_keepable.1 hY).1, (mem_keepable.1 hY).2.1.trans hXT,
      (mem_keepable.1 hY).2.2⟩
  rw [evidenceTarget_eq, evidenceTarget_eq]
  rcases hd : deepest Φ (keepable sp Φ V s w T) with _ | D
  · rw [Option.getD_none]
    have hempty : keepable sp Φ V s w T = ∅ := by
      by_contra hne
      obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X hX => (mem_keepable.1 hX).1)
        (Set.nonempty_iff_ne_empty.2 hne)
      rw [hd] at hD
      cases hD
    rcases hd' : deepest Φ (keepable sp Φ V s w Φ.F) with _ | D'
    · rfl
    · have := hsub (hΦ.rooted.2 T hT) (deepest_mem hd').1
      rw [hempty] at this
      exact absurd this (Set.notMem_empty _)
  · rw [Option.getD_some]
    obtain ⟨hDt, hDT, hDw⟩ := mem_keepable.1 (deepest_mem hd).1
    have hDS : D ∈ keepable sp Φ V s w D := mem_keepable.2 ⟨hDt, .refl, hDw⟩
    have hsubT : keepable sp Φ V s w D ⊆ Φ.tree := fun X hX => (mem_keepable.1 hX).1
    obtain ⟨D', hD'⟩ := exists_deepest hΦ hsubT ⟨D, hDS⟩
    rw [hD', Option.getD_some]
    have h1 := (mem_keepable.1 (deepest_mem hD').1).2.1
    have h2 := anc_deepest hΦ hsubT
      (fun X hX C hC => anc_total hΦ.coherent (mem_keepable.1 hX).2.1 (mem_keepable.1 hC).2.1)
      hD' D hDS
    exact Anc.antisymm hΦ.coherent h1 h2

/-- Every lock of `unlockW` is live, on a block that is its own viable ancestor and, for a slot
below `s`, fixed by both stages. -/
private theorem unlockW_fixed {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set WLock) (t : Time)
    (s : Int) (V : View sp.n) :
    ∀ w ∈ unlockW sp L Φ t s V, ∃ Y ∈ Φ.tree, Y.root = w.lock.block ∧ w.lock.LiveAt sp t ∧
      Φ.viableAncestor Y = Y ∧ ((w.lock.slot : Int) < s →
        evidenceTarget sp Φ V s w (unlockTarget sp Φ V s Y) = Y) := by
  intro w' hw'
  obtain ⟨_, hw, B, hB, hBr, rfl⟩ := mem_unlockW.1 hw'
  obtain ⟨w₀, -, B₀, hB₀, -, hlive, rfl⟩ := mem_liveLocksW.1 hw
  obtain ⟨hvt, -⟩ := viableAncestor_anc hΦ hB₀
  obtain rfl : B = Φ.viableAncestor B₀ := hΦ.coherent.1 hB hvt hBr
  have hcand := (viableAncestor_spec hΦ hB₀).2.1
  dsimp only at hlive ⊢
  set w := ({ w₀ with lock := { w₀.lock with block := (Φ.viableAncestor B₀).root } } : WLock)
  by_cases hlt : (w₀.lock.slot : Int) < s
  · rw [ite_eq_left hlt]
    obtain ⟨hTt, hTB⟩ := unlockTarget_anc sp hΦ V s hB
    obtain ⟨hYt, hYT⟩ := evidenceTarget_anc hΦ V s w hTt
    refine ⟨_, hYt, rfl, hlive, viableAncestor_self hΦ hYt ?_, fun _ => ?_⟩
    · exact (candidate_of_anc hΦ (hYT.trans hTB) hcand).symm
    · rw [unlockTarget_fix hΦ V s hB hYt hYT]
      refine (evidenceTarget_weight (w' := w) ?_ _).trans (evidenceTarget_fix hΦ V s w hTt)
      rfl
  · rw [ite_eq_right hlt]
    exact ⟨_, hB, rfl, hlive, viableAncestor_self hΦ hB hcand.symm, fun h => absurd h hlt⟩

/-- **A0.4 (d) for the candidate**: `unlockW` is idempotent. -/
theorem unlockW_idempotent {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set WLock) (t : Time)
    (s : Int) (V : View sp.n) :
    unlockW sp (unlockW sp L Φ t s V) Φ t s V = unlockW sp L Φ t s V := by
  have hfix := unlockW_fixed hΦ L t s V
  -- the second pass returns each lock of the first unchanged
  have hid : ∀ w ∈ unlockW sp L Φ t s V, ∀ B ∈ Φ.tree, B.root = w.lock.block →
      (if (w.lock.slot : Int) < s then
        ({ w with lock := { w.lock with
          block := (evidenceTarget sp Φ V s w (unlockTarget sp Φ V s B)).root } } : WLock)
        else w) = w := by
    intro w hw B hB hBr
    obtain ⟨Y, hY, hYr, -, -, hT⟩ := hfix w hw
    obtain rfl : B = Y := hΦ.coherent.1 hB hY (hBr.trans hYr.symm)
    by_cases h : (w.lock.slot : Int) < s
    · rw [ite_eq_left h, hT h, hBr]
    · rw [ite_eq_right h]
  have hlive : ∀ w ∈ unlockW sp L Φ t s V, ∃ Y ∈ Φ.tree, Y.root = w.lock.block ∧
      w.lock.LiveAt sp t ∧
      w = ({ w with lock := { w.lock with block := (Φ.viableAncestor Y).root } } : WLock) := by
    intro w hw
    obtain ⟨Y, hY, hYr, hk, hva, -⟩ := hfix w hw
    exact ⟨Y, hY, hYr, hk, by rw [hva, hYr]⟩
  ext w
  constructor
  · intro hw2
    obtain ⟨w', hw', B, hB, hBr, rfl⟩ := mem_unlockW.1 hw2
    obtain ⟨w₁, hw₁, Y₁, hY₁, hY₁r, -, rfl⟩ := mem_liveLocksW.1 hw'
    obtain ⟨Y₂, hY₂, hY₂r, -, hva, -⟩ := hfix w₁ hw₁
    obtain rfl : Y₁ = Y₂ := hΦ.coherent.1 hY₁ hY₂ (hY₁r.trans hY₂r.symm)
    have he : ({ w₁ with lock := { w₁.lock with block := (Φ.viableAncestor Y₁).root } } : WLock)
        = w₁ := by
      rw [hva, hY₁r]
    rw [he] at hBr ⊢
    rw [hid w₁ hw₁ B hB hBr]
    exact hw₁
  · intro hw
    obtain ⟨Y, hY, hYr, hk, he⟩ := hlive w hw
    exact mem_unlockW.2 ⟨w, mem_liveLocksW.2 ⟨w, hw, Y, hY, hYr, hk, he⟩, Y, hY, hYr,
      (hid w hw Y hY hYr).symm⟩

end Consensus.Goldilocks.EvidenceRelease

end
