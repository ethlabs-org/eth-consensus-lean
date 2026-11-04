module
public import ConsensusLean.Instances.Goldilocks.Spec.Frame
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Common.Tree

@[expose] public section

/-! # Goldilocks milestone vocabulary: well-formed frames and frame steps

The part of `Spec/Frame` that no Challenge statement reaches (docs/decisions.md, 2026-11-04): the
milestone statements use it; it is not on the trusted surface. Names and bodies are unchanged.

* `FrameOK`: a well-formed frame (claims G0.4 (frame));
* `FrameStep Φ B Φ'` (`Φ ⊑_B Φ'`): how a frame changes when the FG
  accepts `B` (claims G0.3 (frame)); nothing is said about `fc_root` or `viable_heads`, which a
  contest moves back and forth.

Ancestry is `Anc` inside the frame's tree (or, in a step, inside the tree with the new block).
That an honest node's frames are well formed and evolve by steps is an FG store fact (claims
G0.4 (height), C0.5), not a frame fact. -/

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type}

namespace Frame

variable (Φ : Frame n FGP ACP)

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

end Consensus.Goldilocks

end
