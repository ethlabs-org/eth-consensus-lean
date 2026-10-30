module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Base
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Goldilocks SA: shared helpers for the AC proofs

Blocks by root (`lookup`, `InTree`, `AncR`), ancestry in a frame, and the extended time line.
The tree facts of claims F.2 (antisymmetry, ancestors form a chain) are borrowed here as
`sorry` lemmas until `Lemmas/Common` proves them (AGENTS.md: a lemma from another area). -/

namespace Consensus.Goldilocks.SA

variable {n : Nat} {FGP : Type}

/-- **Borrowed (F.2 (b), `Statements.Common.AncTotal`):** inside a coherent set, two ancestors
of one block are compatible. -/
theorem anc_total {S : Set (Blk n FGP)} {A A' C : Blk n FGP} (hS : Coherent S)
    (h : Anc S A C) (h' : Anc S A' C) : Anc S A A' ∨ Anc S A' A := by
  sorry

/-- **Borrowed (F.2 (a), `Statements.Common.AncAntisymm`).** -/
theorem anc_antisymm {S : Set (Blk n FGP)} {B C : Blk n FGP} (hS : Coherent S)
    (h : Anc S B C) (h' : Anc S C B) : B = C := by
  sorry

/-- **Borrowed (G0.4 (frame), `Statements.Frame.ViableAncestorExists`):** in a well-formed
frame, `viableAncestor` returns the viable ancestor of a block of the tree. -/
theorem viableAncestor_spec {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B : Blk n FGP} (hB : B ∈ Φ.tree) :
    Φ.IsViableAncestor B (Φ.viableAncestor B) := by
  sorry

/-- **Borrowed (G0.4 (frame), `Statements.Frame.ViableAncestorSelf`).** -/
theorem viableAncestor_self {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B : Blk n FGP}
    (hB : B ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B Φ.fcRoot) : Φ.viableAncestor B = B := by
  sorry

/-- An ancestor inside the tree of a block of the tree is in the tree. -/
theorem mem_of_anc {Φ : Frm n FGP} {A B : Blk n FGP} (h : Φ.Anc A B) (hB : B ∈ Φ.tree) :
    A ∈ Φ.tree := by
  by_cases hAB : A = B
  · exact hAB ▸ hB
  · exact (Anc.mem h hAB).1

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

end Consensus.Goldilocks.SA

end
