module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Sigma
public import ConsensusLean.Instances.Goldilocks.Spec.Frame

@[expose] public section

/-! # Goldilocks FG store: frontier contest, viability and the FG frame

fg.tex §"Finality caches and frame", Figure "FG: handlers, finality caches and frame":
`is_viable`, `has_viable_descendant` and `fg_to_ac`, with the fork-choice root `Σ.F`. The contest
test `fg_contest`, the head height floor and the former root `get_fc_root` are notions of the
analysis; the protocol does not read them. The tests read the whole tree and the finality caches,
never the tree of a voter.
Ancestry is inside `Σ.T`. The functions that branch on a test over the (possibly infinite)
tree are classical. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} (st : Store P ACP)

/-- `fg_contest(Σ)`: `h_max = h_j + 1` and some accepted block that extends `Σ.F`, with state
height `h_max`, does not extend `Σ.J`. An FG-state notion of the analysis; not read by viability or
the frame. -/
def Contest : Prop :=
  st.hmax = st.hj + 1 ∧
    ∃ B ∈ st.tree, st.Anc st.F B ∧ (st.σ B.root).h = st.hmax ∧ ¬ st.Anc st.J B

open Classical in
/-- The head height floor: `h_max` in a contest, `h_max − 1` otherwise. An FG-state notion of the
analysis; not read by viability or the frame. -/
noncomputable def headHeightFloor : Nat := if st.Contest then st.hmax else st.hmax - 1

open Classical in
/-- The former fork-choice root: `Σ.J` when `h_max = h_j + 1` and there is no contest, `Σ.F`
otherwise. An FG-state notion of the analysis; not read by viability or the frame. -/
noncomputable def fcRoot : NodeBlock P ACP :=
  if st.hmax = st.hj + 1 ∧ ¬ st.Contest then st.J else st.F

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
  fcRoot := st.F
  viableHeads := {B | B ∈ st.tree ∧ st.Anc st.F B ∧ st.IsViable B}

end Consensus.Goldilocks.Store

end
