module
public import Mathlib.Basic.Finite.Defs
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Tree

@[expose] public section

/-! # Goldilocks: the FG frame

What the FG gives to the AC (composition.tex §"The FG frame"):
`Φ = fg_to_ac(Σ) = (tree, fc_root, viable_heads)`, with `Φ.F` the root of `Φ.tree` (the block
`Σ.F`). This module holds the frame as a value, the FG surface the AC sees
(`Frame`):

* `viableTree Φ S`: the blocks of `S` that extend `fc_root` and have a descendant in
  `S ∩ viable_heads` (composition.tex; it follows from the frame, it is not a part of it);
* `IsViableAncestor` / `viableAncestor`: the deepest `B' ⪯ B` with `B' ⪯ fc_root` or `B'` in the
  viable tree (goldilocks-spec Figure "Goldilocks: locks and unlocking"; a function of `Φ` alone, so
  it is defined here, claims G0.4 (frame)).

Ancestry is `Anc` inside the frame's tree.

This module holds only what the Challenge statements reach; `Frame.Rooted`, the well-formed frames
`FrameOK` and the frame steps `FrameStep` are in `Milestones/Spec/Frame` (`docs/decisions.md`
§"Trusted surface and Challenge scope"). -/

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type}

/-- An FG frame: the tree of accepted blocks that extend the finalized tip `F`, the root of the
fork choice `fcRoot`, and the blocks `viableHeads` on which a head walk may stop. -/
structure Frame (n : Nat) (FGP ACP : Type) where
  /-- `Φ.tree`: the accepted blocks that extend `Φ.F`. -/
  tree : Set (Block n FGP ACP)
  /-- `Φ.F`: the root of the tree, the finalized tip. -/
  F : Block n FGP ACP
  /-- `Φ.fc_root`: the root of the fork choice. -/
  fcRoot : Block n FGP ACP
  /-- `Φ.viable_heads`: the blocks on which a head walk may stop. -/
  viableHeads : Set (Block n FGP ACP)

namespace Frame

variable (Φ : Frame n FGP ACP)

/-- Ancestry inside the frame's tree. -/
abbrev Anc : Block n FGP ACP → Block n FGP ACP → Prop := Goldilocks.Anc Φ.tree

/-- The viable tree `viable_tree(Φ, S)`: the blocks of `S` that extend `fc_root` and have a
descendant in `S ∩ viable_heads`. -/
def viableTree (S : Set (Block n FGP ACP)) : Set (Block n FGP ACP) :=
  {B | B ∈ S ∧ Φ.Anc Φ.fcRoot B ∧ ∃ W ∈ S, W ∈ Φ.viableHeads ∧ Φ.Anc B W}

/-- A candidate of `viable_ancestor`: at or below `fc_root`, or in the viable tree of the whole
frame tree. -/
def AncestorCandidate (A : Block n FGP ACP) : Prop :=
  Φ.Anc A Φ.fcRoot ∨ A ∈ Φ.viableTree Φ.tree

/-- `A` is `viable_ancestor(Φ, B)`: the deepest `A ⪯ B` that is a candidate (every candidate
`A' ⪯ B` is `⪯ A`). -/
def IsViableAncestor (B A : Block n FGP ACP) : Prop :=
  Φ.Anc A B ∧ Φ.AncestorCandidate A ∧ ∀ A', Φ.Anc A' B → Φ.AncestorCandidate A' → Φ.Anc A' A

open Classical in
/-- `viable_ancestor(Φ, B)` as a function: the block of `IsViableAncestor` when there is one
(for a well-formed frame and `B ∈ Φ.tree` there is exactly one), `B` otherwise. -/
noncomputable def viableAncestor (B : Block n FGP ACP) : Block n FGP ACP :=
  if h : ∃ A, Φ.IsViableAncestor B A then h.choose else B

end Frame

end Consensus.Goldilocks

end
