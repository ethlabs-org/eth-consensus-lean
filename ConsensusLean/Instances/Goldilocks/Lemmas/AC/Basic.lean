module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Base
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import Mathlib.Order.Preorder.Finite

public section

/-! # Goldilocks SA: shared helpers for the AC proofs

Blocks by root (`lookup`, `InTree`, `AncR`), ancestry in a frame, and the extended time line.
The viable ancestor of claims G0.4 (frame) (`viableAncestor_spec`, `viableAncestor_self`) is
proved here: `Lemmas.Common` cannot import `Spec.Frame`. -/

namespace Consensus.Goldilocks.SA

variable {n : Nat} {FGP : Type}

/-- F.2 (b) for blocks of the SA (`Anc.total`). -/
theorem anc_total {S : Set (Blk n FGP)} {A A' C : Blk n FGP} (hS : Coherent S)
    (h : Anc S A C) (h' : Anc S A' C) : Anc S A A' ∨ Anc S A' A :=
  h.total hS h'

/-- An ancestor inside the tree of a block of the tree is in the tree. -/
theorem mem_of_anc {Φ : Frm n FGP} {A B : Blk n FGP} (h : Φ.Anc A B) (hB : B ∈ Φ.tree) :
    A ∈ Φ.tree := by
  by_cases hAB : A = B
  · exact hAB ▸ hB
  · exact (Anc.mem h hAB).1

/-- **G0.4 (frame), the viable ancestor exists.** In a well-formed frame, a block of the tree has
a viable ancestor: the deepest (by slot) ancestor that is at or below `fc_root` or viable; `Φ.F`
is one, and the ancestors of a block form a chain. -/
theorem exists_isViableAncestor {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B : Blk n FGP}
    (hB : B ∈ Φ.tree) : ∃ A, Φ.IsViableAncestor B A := by
  have hfin : {A | Φ.Anc A B ∧ Φ.AncestorCandidate A}.Finite :=
    hΦ.finite.subset fun A hA => mem_of_anc hA.1 hB
  obtain ⟨A, ⟨hAB, hAc⟩, hmax⟩ := hfin.exists_maximalFor (fun A : Blk n FGP => A.slot) _
    ⟨Φ.F, hΦ.rooted.2 B hB, Or.inl hΦ.F_anc_fcRoot⟩
  refine ⟨A, hAB, hAc, fun A' hA'B hA'c => ?_⟩
  rcases hA'B.total hΦ.coherent hAB with h | h
  · exact h
  · by_cases hne : A = A'
    · exact hne ▸ Relation.ReflTransGen.refl
    · have hlt := (h.slot_le hΦ.coherent).2 hne
      exact absurd (hmax ⟨hA'B, hA'c⟩ (Nat.le_of_lt hlt)) (Nat.not_le.mpr hlt)

open Classical in
/-- `viableAncestor` returns the viable ancestor of a block of a well-formed frame. -/
theorem viableAncestor_spec {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B : Blk n FGP} (hB : B ∈ Φ.tree) :
    Φ.IsViableAncestor B (Φ.viableAncestor B) := by
  have h := exists_isViableAncestor hΦ hB
  unfold Frame.viableAncestor
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

/-- **G0.4 (frame), self.** A block of the tree that is viable or at or below `fc_root` is its own
viable ancestor. -/
theorem viableAncestor_self {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B : Blk n FGP} (hB : B ∈ Φ.tree)
    (hc : B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot) : Φ.viableAncestor B = B := by
  obtain ⟨hAB, -, hmax⟩ := viableAncestor_spec hΦ hB
  exact Anc.antisymm hΦ.coherent hAB (hmax B Relation.ReflTransGen.refl hc.symm)

open Classical in
/-- `viableAncestor B` is an ancestor of `B` in the tree, in any frame. -/
theorem anc_viableAncestor (Φ : Frm n FGP) (B : Blk n FGP) : Φ.Anc (Φ.viableAncestor B) B := by
  unfold Frame.viableAncestor
  split_ifs with h
  · exact h.choose_spec.1
  · exact Relation.ReflTransGen.refl

/-- The viable ancestor of a block of a well-formed frame is in the tree, below the block. -/
theorem viableAncestor_anc {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B : Blk n FGP} (hB : B ∈ Φ.tree) :
    Φ.viableAncestor B ∈ Φ.tree ∧ Φ.Anc (Φ.viableAncestor B) B :=
  ⟨mem_of_anc (viableAncestor_spec hΦ hB).1 hB, (viableAncestor_spec hΦ hB).1⟩

open Classical in
theorem deepest_mem {Φ : Frm n FGP} {S : Set (Blk n FGP)} {D : Blk n FGP}
    (h : deepest Φ S = some D) : IsDeepest Φ S D := by
  unfold deepest at h
  split_ifs at h with hS
  cases h
  exact hS.choose_spec

open Classical in
theorem lookup_eq_some {Φ : Frm n FGP} {r : Nat} {H : Blk n FGP} (h : lookup Φ r = some H) :
    H ∈ Φ.tree ∧ H.root = r := by
  unfold lookup at h
  split_ifs at h with hr
  cases h
  exact hr.choose_spec

open Classical in
theorem lookup_eq_none {Φ : Frm n FGP} {r : Nat} (h : lookup Φ r = none) : ¬ InTree Φ r := by
  unfold lookup at h
  split_ifs at h with hr
  exact hr

/-- A resolved vote (finite resolution time) has its head in the tree. -/
theorem inTree_of_resolutionTime_ne_top {A : SAState n} {Φ : Frm n FGP} {v : Vote n}
    (h : resolutionTime A Φ v ≠ ⊤) : InTree Φ v.head := by
  unfold resolutionTime at h
  split at h
  · exact absurd rfl h
  · rename_i H hH
    obtain ⟨hm, hr⟩ := lookup_eq_some hH
    exact ⟨H, hm, hr⟩

/-- In a rooted frame, every block of the tree is compatible with `Φ.F`. -/
theorem compatible_F {Φ : Frm n FGP} (hΦ : FrameOK Φ) {H : Blk n FGP} (hH : H ∈ Φ.tree) :
    Compatible Φ.tree H Φ.F :=
  Or.inr (hΦ.rooted.2 H hH)

/-- Ancestry inside a coherent `U` between two blocks of a well-formed frame tree contained in
`U` is ancestry inside the tree. -/
theorem anc_tree_of_anc_U {U : Set (Blk n FGP)} (hU : Coherent U) {Φ : Frm n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {B C : Blk n FGP} (hB : B ∈ Φ.tree)
    (h : Anc U B C) : C ∈ Φ.tree → Φ.Anc B C := by
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

/-- In a well-formed frame, depth strictly increases along strict ancestry. -/
theorem depth_lt_of_anc {Φ : Frm n FGP} (hΦ : FrameOK Φ) {A B : Blk n FGP}
    (h : Φ.Anc A B) (hne : A ≠ B) (hB : B ∈ Φ.tree) : depth Φ A < depth Φ B := by
  refine Set.ncard_lt_ncard ⟨fun X hX => hX.trans h, fun hsub => hne ?_⟩
    (hΦ.finite.subset fun X hX => mem_of_anc hX hB)
  exact Anc.antisymm hΦ.coherent h (hsub (Relation.ReflTransGen.refl : Φ.Anc B B))

end Consensus.Goldilocks.SA

end
