module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Params
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Block

public section

/-! # Goldilocks: tree mathematics, digests and slot arithmetic (proof-side claims)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` (goldilocks#21), the
generic nodes of the Common module: F.2 (tree mathematics: inside a coherent set of blocks,
ancestry is a partial order, the ancestors of a block form a chain, and two blocks with a
common ancestor have a deepest one) and F.3 (digests: two well-rooted blocks whose contents
do not collide, with one root and one proposer, are equal), plus the defining property of
`Params.slotOf`. F.5 (schema), the first-violating-position induction, is Mathlib's
`WellFounded.induction`, cited where it is used; it needs no statement here. That an FG tree is
coherent (F.2 at a node) is an FG store statement.

These claims are proved in `StatementsBundle`; they are outside the trusted surface.
Characterizing lemmas expose their propositions without exporting definition bodies. -/

namespace Consensus.Goldilocks

/-- **F.2 (a), antisymmetry.** Inside a coherent set, `B ⪯ C ⪯ B` only for `B = C`. -/
def AncAntisymm : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (S : Set (Block n FGP ACP)) (B C : Block n FGP ACP),
    Coherent S → Anc S B C → Anc S C B → B = C

theorem ancAntisymm_iff : AncAntisymm ↔
    ∀ (n : Nat) (FGP ACP : Type) (S : Set (Block n FGP ACP)) (B C : Block n FGP ACP),
      Coherent S → Anc S B C → Anc S C B → B = C := by rfl

/-- **F.2 (b), the ancestors of a block form a chain.** Inside a coherent set, two ancestors
of one block are compatible. -/
def AncTotal : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (S : Set (Block n FGP ACP)) (A A' C : Block n FGP ACP),
    Coherent S → Anc S A C → Anc S A' C → Anc S A A' ∨ Anc S A' A

theorem ancTotal_iff : AncTotal ↔
    ∀ (n : Nat) (FGP ACP : Type) (S : Set (Block n FGP ACP)) (A A' C : Block n FGP ACP),
      Coherent S → Anc S A C → Anc S A' C → Anc S A A' ∨ Anc S A' A := by rfl

/-- **F.2 (c), deepest common ancestor.** Inside a coherent set, two blocks with a common
ancestor `R` have a common ancestor `D` that every common ancestor is an ancestor of. -/
def DeepestCommonAncestor : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (S : Set (Block n FGP ACP)) (R B C : Block n FGP ACP),
    Coherent S → Anc S R B → Anc S R C →
      ∃ D, Anc S D B ∧ Anc S D C ∧ ∀ D', Anc S D' B → Anc S D' C → Anc S D' D

theorem deepestCommonAncestor_iff : DeepestCommonAncestor ↔
    ∀ (n : Nat) (FGP ACP : Type) (S : Set (Block n FGP ACP)) (R B C : Block n FGP ACP),
      Coherent S → Anc S R B → Anc S R C →
        ∃ D, Anc S D B ∧ Anc S D C ∧ ∀ D', Anc S D' B → Anc S D' C → Anc S D' D := by rfl

/-- **F.3, digests.** Two blocks whose roots are the digests of their contents, whose contents
do not collide under the digest, with one root and one proposer, are equal (so a test by root
is a test by block). The proposer is not part of the digest input (composition.tex §Blocks);
the node's blocks have the slot proposer. -/
def DigestDeterminesBlock : Prop :=
  ∀ (n : Nat) (FGP ACP : Type) (dg : Digest FGP ACP) (B C : Block n FGP ACP),
    (dg B.parent B.slot B.input B.fgPayload B.acPayload =
        dg C.parent C.slot C.input C.fgPayload C.acPayload →
      B.parent = C.parent ∧ B.slot = C.slot ∧ B.input = C.input ∧ B.fgPayload = C.fgPayload ∧
        B.acPayload = C.acPayload) →
    B.RootOk dg → C.RootOk dg → B.root = C.root → B.proposer = C.proposer → B = C

theorem digestDeterminesBlock_iff : DigestDeterminesBlock ↔
    ∀ (n : Nat) (FGP ACP : Type) (dg : Digest FGP ACP) (B C : Block n FGP ACP),
      (dg B.parent B.slot B.input B.fgPayload B.acPayload =
          dg C.parent C.slot C.input C.fgPayload C.acPayload →
        B.parent = C.parent ∧ B.slot = C.slot ∧ B.input = C.input ∧ B.fgPayload = C.fgPayload ∧
          B.acPayload = C.acPayload) →
      B.RootOk dg → C.RootOk dg → B.root = C.root → B.proposer = C.proposer → B = C := by rfl

/-- **The slot of a time.** From time `0` on, `slot(t)` is the slot whose start is at or
before `t` and whose successor starts after `t`. -/
def SlotOfSpec : Prop :=
  ∀ (P : Params) (t : Time), 0 ≤ t →
    P.slotTime (P.slotOf t) ≤ t ∧ t < P.slotTime (P.slotOf t + 1)

theorem slotOfSpec_iff : SlotOfSpec ↔
    ∀ (P : Params) (t : Time), 0 ≤ t →
      P.slotTime (P.slotOf t) ≤ t ∧ t < P.slotTime (P.slotOf t + 1) := by rfl

/-- The Common statements. -/
structure CommonStatements : Prop where
  ancAntisymm : AncAntisymm
  ancTotal : AncTotal
  deepestCommonAncestor : DeepestCommonAncestor
  digestDeterminesBlock : DigestDeterminesBlock
  slotOfSpec : SlotOfSpec

end Consensus.Goldilocks

end
