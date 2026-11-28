module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Sigma
public import ConsensusLean.Instances.Goldilocks.Spec.Frame

@[expose] public section

/-! # Goldilocks FG store: viability and the FG frame

fg.tex §"Finality caches and frame", Figure "FG: handlers, finality caches and frame":
`is_viable`, `has_viable_descendant` and `fg_to_ac`, with the finalized tip `Σ.F` as the
fork-choice root. Ancestry is inside `Σ.T`. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- `is_viable(Σ, B)`: the state height of `B` is at least `h_max`, or it is `h_max − 1` and either
`h_j + 1 < h_max` or `B` extends `Σ.J`. -/
def IsViable (B : NodeBlock P ACP) : Prop :=
  st.hmax ≤ (st.σ B.root).h ∨
    ((st.σ B.root).h + 1 = st.hmax ∧ (st.hj + 1 < st.hmax ∨ st.Anc st.J B))

/-- `has_viable_descendant(Σ, B)`: some accepted block that extends `B` is viable. -/
def HasViableDescendant (B : NodeBlock P ACP) : Prop :=
  ∃ B' ∈ st.tree, st.Anc B B' ∧ st.IsViable B'

/-- `fg_to_ac(Σ)`: the accepted blocks that extend `Σ.F`, the fork-choice root `Σ.F`, and the
viable heads (the blocks of that tree that are viable). -/
noncomputable def toFrame : Frame P.n (List (FG.Att P.n)) ACP where
  tree := {B | B ∈ st.tree ∧ st.Anc st.F B}
  F := st.F
  viableHeads := {B | B ∈ st.tree ∧ st.Anc st.F B ∧ st.IsViable B}

end Consensus.Goldilocks.Store

end
