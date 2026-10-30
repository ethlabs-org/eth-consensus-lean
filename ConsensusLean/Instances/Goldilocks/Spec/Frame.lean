module
public import Mathlib.Basic.Finite.Defs
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Tree

@[expose] public section

/-! # Goldilocks: the FG frame

What the FG gives to the AC (composition.tex §"The FG frame"):
`Φ = fg_to_ac(Σ) = (tree, fc_root, viable_heads)`, with `Φ.F` the root of `Φ.tree` (the block
`Σ.F`). This module holds the frame as a value and its contract, the whole FG surface the AC
sees (decomposition §2 D, `Frame`):

* `viableTree Φ S`: the blocks of `S` that extend `fc_root` and have a descendant in
  `S ∩ viable_heads` (composition.tex; it follows from the frame, it is not a part of it);
* `IsViableAncestor` / `viableAncestor`: the deepest `B' ⪯ B` with `B' ⪯ fc_root` or `B'` in the
  viable tree (fgsa-spec Figure "Goldilocks: locks and unlocking"; a function of `Φ` alone, so
  it is defined here, claims G0.4 (frame));
* `FrameOK`: a well-formed frame (claims G0.4 (frame));
* `FrameStep Φ B Φ'` (`Φ ⊑_B Φ'`) and its closure `FrameEvol`: how a frame changes when the FG
  accepts `B` (claims G0.3 (frame)); nothing is said about `fc_root` or `viable_heads`, which a
  contest moves back and forth.

Ancestry is `Anc` inside the frame's tree (or, in a step, inside the tree with the new block).
That an honest node's frames are well formed and evolve by steps is an FG store fact (claims
G0.4 (height), C0.5), not a frame fact. -/

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

/-- The tree is rooted at `Φ.F`: `Φ.F ∈ Φ.tree` and every block of the tree extends `Φ.F`
inside the tree (so the tree is parent-closed down to `Φ.F`). -/
def Rooted : Prop := Φ.F ∈ Φ.tree ∧ ∀ C ∈ Φ.tree, Φ.Anc Φ.F C

end Frame

/-- **G0.4 (frame), a well-formed frame.** The tree is finite, coherent (roots injective, slots
strictly increasing along parent edges: F.2 on the tree) and rooted at `Φ.F`;
`Φ.F ⪯ fc_root ∈ Φ.tree`;
`viable_heads ⊆ Φ.tree` and every block of it extends `fc_root`. -/
structure FrameOK (Φ : Frame n FGP ACP) : Prop where
  /-- The tree is finite (the accepted tree is). -/
  finite : Φ.tree.Finite
  /-- Roots are injective on the tree, and slots strictly increase along its parent edges. -/
  coherent : Coherent Φ.tree
  /-- The tree is rooted at `Φ.F`. -/
  rooted : Φ.Rooted
  /-- `fc_root ∈ Φ.tree`. -/
  fcRoot_mem : Φ.fcRoot ∈ Φ.tree
  /-- `Φ.F ⪯ fc_root`. -/
  F_anc_fcRoot : Φ.Anc Φ.F Φ.fcRoot
  /-- `viable_heads ⊆ Φ.tree`. -/
  viableHeads_subset : Φ.viableHeads ⊆ Φ.tree
  /-- Every viable head extends `fc_root`. -/
  fcRoot_anc_viableHeads : ∀ W ∈ Φ.viableHeads, Φ.Anc Φ.fcRoot W

/-- **G0.3 (frame), a frame step `Φ ⊑_B Φ'`.** The FG accepts the new block `B`
(`B ∉ Φ.tree`) whose parent is in `Φ.tree`; the finalized tip moves to `Φ'.F` with
`Φ.F ⪯ Φ'.F ⪯ B`; and `Φ'.tree` is the blocks of `Φ.tree ∪ {B}` that extend `Φ'.F`
(ancestry inside `Φ.tree ∪ {B}`). Nothing is said about `fc_root` or `viable_heads`. -/
structure FrameStep (Φ : Frame n FGP ACP) (B : Block n FGP ACP) (Φ' : Frame n FGP ACP) : Prop
    where
  /-- `B` is new: `B ∉ Φ.tree`. -/
  new : B ∉ Φ.tree
  /-- The parent of `B` is in `Φ.tree`. -/
  parent_mem : ∃ P ∈ Φ.tree, B.parent = some P.root
  /-- `Φ.F ⪯ Φ'.F` inside `Φ.tree ∪ {B}`. -/
  F_anc_F' : Goldilocks.Anc (insert B Φ.tree) Φ.F Φ'.F
  /-- `Φ'.F ⪯ B` inside `Φ.tree ∪ {B}`. -/
  F'_anc_B : Goldilocks.Anc (insert B Φ.tree) Φ'.F B
  /-- `Φ'.tree` is the blocks of `Φ.tree ∪ {B}` that extend `Φ'.F`. -/
  tree_eq : Φ'.tree = {X | X ∈ insert B Φ.tree ∧ Goldilocks.Anc (insert B Φ.tree) Φ'.F X}

/-- The reflexive-transitive closure of frame steps (`Φ ⊑ Φ'`): equal frames, or a sequence of
steps `Φ ⊑_{B₁} ⋯ ⊑_{B_k} Φ'`. -/
def FrameEvol : Frame n FGP ACP → Frame n FGP ACP → Prop :=
  Relation.ReflTransGen (fun Φ Φ' => ∃ B, FrameStep Φ B Φ')

/-- A sequence of frames that evolves by steps: each frame equals the previous one or is
reached from it by one step. -/
def FrameSeq (Φ : Nat → Frame n FGP ACP) : Prop :=
  ∀ i, Φ (i + 1) = Φ i ∨ ∃ B, FrameStep (Φ i) B (Φ (i + 1))

/-- A frame sequence inside `U`: it evolves by steps, its first frame is rooted, and all its
trees lie in the coherent set `U` (at a node, the accepted blocks of the run). Frames alone allow
a block that left the tree to come back under a reused root; `U` excludes it. -/
structure FrameSeqIn (Φ : Nat → Frame n FGP ACP) (U : Set (Block n FGP ACP)) : Prop where
  /-- Each frame equals the previous one or is reached from it by one step. -/
  seq : FrameSeq Φ
  /-- The first frame is rooted. -/
  rooted : (Φ 0).Rooted
  /-- Every tree lies in `U`. -/
  subset : ∀ i, (Φ i).tree ⊆ U
  /-- `U` is coherent. -/
  coherent : Coherent U

end Consensus.Goldilocks

end
