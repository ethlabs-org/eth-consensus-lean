module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Inv
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks SA: the live locks, the anchor and the record (A0.4 (a), (b), (f), A0.5)

Under the lock invariant (`LockInv`) every live lock block is the viable ancestor of a stored
lock block, so it is a candidate of `viable_ancestor` (viable or at or below `fc_root`) and an
ancestor of the record's block, which is then in the tree: the live lock blocks lie on one
chain with `fc_root`, the anchor (the deepest of them) extends each, and the effective record
extends each. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {U : Set (Blk sp.n FGP)}

/-- A live lock block is the viable ancestor of the block of a stored live lock. -/
theorem mem_liveLockBlocks {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set Lock} {t : Time}
    {B : Blk sp.n FGP} (hB : B ∈ liveLockBlocks sp L Φ t) :
    ∃ l ∈ L, ∃ B₀ ∈ Φ.tree, B₀.root = l.block ∧ l.LiveAt sp t ∧
      B = Φ.viableAncestor B₀ := by
  obtain ⟨hBt, l', ⟨l, hl, B₀, hB₀, hB₀r, hlive, rfl⟩, hr⟩ := hB
  exact ⟨l, hl, B₀, hB₀, hB₀r, hlive,
    hΦ.coherent.1 hBt (viableAncestor_anc hΦ hB₀).1 hr.symm⟩

/-- A live lock block is viable or at or below `fc_root`. -/
theorem liveLockBlock_candidate {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set Lock} {t : Time}
    {B : Blk sp.n FGP} (hB : B ∈ liveLockBlocks sp L Φ t) :
    B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot := by
  obtain ⟨-, -, B₀, hB₀, -, -, rfl⟩ := mem_liveLockBlocks hΦ hB
  exact (viableAncestor_spec hΦ hB₀).2.1.symm

/-- Under the lock invariant, the effective record extends every live lock block. -/
theorem LockInv.liveBlock_anc (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : SAState sp.n} (h : LockInv U A Φ) {t : Time} {B : Blk sp.n FGP}
    (hB : B ∈ liveLockBlocks sp A.locks Φ t) :
    ∃ E ∈ Φ.tree, E.root = A.latestConfirmed ∧ Φ.Anc B E := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := lockInv_iff.1 h
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := mem_liveLockBlocks hΦ hB
  obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB₀
  have hBE : Anc U (Φ.viableAncestor B₀) E := (Anc.mono hΦU hva).trans (hlE l hl B₀ (hΦU hB₀) hB₀r)
  have hEt' := hEt ((Anc.mono hΦU (hΦ.rooted.2 _ hvt)).trans hBE)
  exact ⟨E, hEt', hEr, anc_tree_of_anc_U hU hΦ hΦU hvt hBE hEt'⟩

/-- Under the lock invariant, the live lock blocks lie on one chain. -/
theorem LockInv.liveBlocks_chain (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A : SAState sp.n} (h : LockInv U A Φ) {t : Time} :
    ∀ B ∈ liveLockBlocks sp A.locks Φ t, ∀ C ∈ liveLockBlocks sp A.locks Φ t,
      Compatible Φ.tree B C := by
  intro B hB C hC
  obtain ⟨E, hE, hEr, hBE⟩ := h.liveBlock_anc hU hΦ hΦU hB
  obtain ⟨E', hE', hE'r, hCE⟩ := h.liveBlock_anc hU hΦ hΦU hC
  obtain rfl : E = E' := hΦ.coherent.1 hE hE' (hEr.trans hE'r.symm)
  exact anc_total hΦ.coherent hBE hCE

/-- A nonempty set of blocks of a well-formed frame's tree has a deepest block. -/
theorem exists_deepest {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {S : Set (Blk sp.n FGP)}
    (hS : S ⊆ Φ.tree) (hne : S.Nonempty) : ∃ D, deepest Φ S = some D := by
  have hfin : S.Finite := hΦ.finite.subset hS
  obtain ⟨D, hD, hmax⟩ := hfin.exists_maximalFor (depth Φ) S hne
  obtain ⟨D', ⟨hD'S, hD'd⟩, hmin⟩ :=
    (hfin.subset (Set.sep_subset S fun C => depth Φ C = depth Φ D)).exists_minimalFor
      Block.root _ ⟨D, hD, rfl⟩
  have h : ∃ D, IsDeepest Φ S D := by
    refine ⟨D', hD'S, fun C hC hne => ?_⟩
    rcases lt_or_ge (depth Φ C) (depth Φ D') with h | h
    · exact Or.inl h
    have hCd : depth Φ C = depth Φ D' := le_antisymm (hD'd ▸ hmax hC (hD'd ▸ h)) h
    refine Or.inr ⟨hCd, lt_of_le_of_ne ?_ fun hr => hne (hΦ.coherent.1 (hS hC) (hS hD'S) hr.symm)⟩
    exact le_of_not_gt fun hlt => (hmin ⟨hC, hCd.trans hD'd⟩ hlt.le).not_gt hlt
  unfold deepest
  split_ifs
  exact ⟨_, rfl⟩

/-- In a chain of blocks of the tree, the deepest block extends every block. -/
theorem anc_deepest {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {S : Set (Blk sp.n FGP)}
    (hS : S ⊆ Φ.tree) (hch : ∀ B ∈ S, ∀ C ∈ S, Compatible Φ.tree B C) {D : Blk sp.n FGP}
    (hD : deepest Φ S = some D) : ∀ X ∈ S, Φ.Anc X D := by
  intro X hX
  have hD' := deepest_mem hD
  refine (hch X hX D hD'.1).elim id fun hDX => ?_
  by_cases hne : D = X
  · exact hne ▸ Relation.ReflTransGen.refl
  · rcases hD'.2 X hX (Ne.symm hne) with h | ⟨h, -⟩ <;>
      have := depth_lt_of_anc hΦ hDX hne (hS hX) <;> omega

/-- **The anchor.** When the live lock blocks lie on one chain, the anchor is in the tree and
extends every live lock block and `fc_root`. -/
theorem anc_getAnchor {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {A : SAState sp.n} {t : Time}
    (hch : ∀ B ∈ liveLockBlocks sp A.locks Φ t, ∀ C ∈ liveLockBlocks sp A.locks Φ t,
      Compatible Φ.tree B C) :
    getAnchor sp A Φ t ∈ Φ.tree ∧
      ∀ X ∈ liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}, Φ.Anc X (getAnchor sp A Φ t) := by
  have hS : liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.1 hX) ▸ hΦ.fcRoot_mem
  have hfc : ∀ B ∈ liveLockBlocks sp A.locks Φ t, Compatible Φ.tree B Φ.fcRoot := fun B hB =>
    (liveLockBlock_candidate hΦ hB).elim (fun h => Or.inr h.2.1) Or.inl
  have hch' : ∀ B ∈ liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot},
      ∀ C ∈ liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}, Compatible Φ.tree B C := by
    rintro B (hB | hB) C (hC | hC)
    · exact hch B hB C hC
    · exact (Set.mem_singleton_iff.1 hC) ▸ hfc B hB
    · exact (Set.mem_singleton_iff.1 hB) ▸ (hfc C hC).symm
    · rw [Set.mem_singleton_iff.1 hB, Set.mem_singleton_iff.1 hC]
      exact Or.inl Relation.ReflTransGen.refl
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨Φ.fcRoot, Or.inr rfl⟩
  have hA : getAnchor sp A Φ t = D := by unfold getAnchor; rw [hD]; rfl
  rw [hA]
  exact ⟨hS (deepest_mem hD).1, anc_deepest hΦ hS hch' hD⟩

variable (sp)

/-- **A0.4 (a), (b).** -/
theorem live_locks_chain : LiveLocksChain sp := by
  intro FGP ro x U hU A Φ t₀ hr t
  obtain ⟨⟨hΦ, hΦU⟩, -, h⟩ := lockInv_of_reachable hU hr
  exact ⟨h.liveBlocks_chain hU hΦ hΦU, fun B hB => liveLockBlock_candidate hΦ hB⟩

/-- **A0.4 (f).** -/
theorem candidates_chain : CandidatesChain sp := by
  intro FGP ro x U hU A Φ t₀ hr t
  obtain ⟨⟨hΦ, hΦU⟩, -, h⟩ := lockInv_of_reachable hU hr
  have hsub : toFGCandidates sp A Φ t ⊆ liveLockBlocks sp A.locks Φ t := by
    rintro B ⟨hB, l, hl, hlb, -⟩
    exact ⟨hB.1, l, hl, hlb⟩
  exact ⟨fun B hB C hC => h.liveBlocks_chain hU hΦ hΦU B (hsub hB) C (hsub hC),
    fun B hB => (anc_getAnchor hΦ (h.liveBlocks_chain hU hΦ hΦU)).2 B (Or.inl (hsub hB))⟩

/-- **A0.5.** -/
theorem lock_to_tip : LockToTip sp := by
  intro FGP ro x U hU A Φ t₀ hr t B hB
  obtain ⟨⟨hΦ, hΦU⟩, -, h⟩ := lockInv_of_reachable hU hr
  obtain ⟨E, hE, hEr, hBE⟩ := h.liveBlock_anc hU hΦ hΦU hB
  have : lookup Φ A.latestConfirmed = some E := by
    rw [← hEr]
    cases hl : lookup Φ E.root with
    | none => exact absurd ⟨E, hE, rfl⟩ (lookup_eq_none hl)
    | some E' => exact congrArg some (hΦ.coherent.1 (lookup_eq_some hl).1 hE (lookup_eq_some hl).2)
  rw [this]
  exact hBE

end Consensus.Goldilocks.SA

end
