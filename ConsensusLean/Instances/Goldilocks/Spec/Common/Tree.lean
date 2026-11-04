module
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Operations
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Block

@[expose] public section

/-! # Goldilocks: ancestry inside a set of blocks

composition.tex §"Blocks": processed blocks form a parent-closed tree; `B ⪯ C` when `B = C`
or `B` is an ancestor of `C`; two blocks are compatible when one is an ancestor of the other.
A block names its parent by root, so ancestry is relative to a set of blocks `S` (an FG tree,
a frame tree): `Anc S B C` holds when `B = C` or parent edges inside `S` lead from `C` down to
`B`.

This module holds only what the Challenge statements reach; `Coherent` is in
`Milestones/Spec/Common/Tree` (docs/decisions.md, 2026-11-04). -/

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type}

/-- A parent edge inside `S`: `B` and `C` are in `S` and `C` names `B`'s root as its parent. -/
def ParentIn (S : Set (Block n FGP ACP)) (B C : Block n FGP ACP) : Prop :=
  B ∈ S ∧ C ∈ S ∧ C.parent = some B.root

/-- Ancestry inside `S` (`B ⪯ C`): `B = C`, or a chain of parent edges inside `S` leads from
`C` down to `B`. -/
def Anc (S : Set (Block n FGP ACP)) : Block n FGP ACP → Block n FGP ACP → Prop :=
  Relation.ReflTransGen (ParentIn S)

/-- Two blocks are compatible inside `S` when one is an ancestor of the other; they conflict
otherwise. -/
def Compatible (S : Set (Block n FGP ACP)) (B C : Block n FGP ACP) : Prop :=
  Anc S B C ∨ Anc S C B

end Consensus.Goldilocks

end
