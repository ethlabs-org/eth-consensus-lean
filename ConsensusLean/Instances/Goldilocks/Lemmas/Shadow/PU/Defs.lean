module
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State

public section

/-! # Shadow P-U viability and frame

The shadow execution keeps the stock frame type and uses the finalized block as its root.
These definitions do not alter the stock protocol.
-/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

def IsViable' (st : Store P ACP) (B : NodeBlock P ACP) : Prop :=
  st.hmax ≤ (st.σ B.root).h ∨
  ((st.σ B.root).h + 1 = st.hmax ∧ (st.hj + 1 < st.hmax ∨ st.Anc st.J B))

noncomputable def toFrame' (st : Store P ACP) : Frame P.n (List (FG.Att P.n)) ACP where
  tree := {B | B ∈ st.tree ∧ st.Anc st.F B}
  F := st.F
  fcRoot := st.F
  viableHeads := {B | B ∈ st.tree ∧ st.Anc st.F B ∧ st.IsViable' B}

theorem isViable'_iff (st : Store P ACP) (B : NodeBlock P ACP) :
    st.IsViable' B ↔ st.hmax ≤ (st.σ B.root).h ∨
      ((st.σ B.root).h + 1 = st.hmax ∧ (st.hj + 1 < st.hmax ∨ st.Anc st.J B)) := by
  rfl

theorem toFrame'_tree (st : Store P ACP) :
    st.toFrame'.tree = {B | B ∈ st.tree ∧ st.Anc st.F B} := by
  rfl

theorem toFrame'_F (st : Store P ACP) : st.toFrame'.F = st.F := by rfl

theorem toFrame'_fcRoot (st : Store P ACP) : st.toFrame'.fcRoot = st.F := by rfl

theorem toFrame'_viableHeads (st : Store P ACP) :
    st.toFrame'.viableHeads = {B | B ∈ st.tree ∧ st.Anc st.F B ∧ st.IsViable' B} := by
  rfl

end Consensus.Goldilocks.Store

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

noncomputable def frame' (st : NodeState A) : A.Frm := st.fg.toFrame'

theorem frame'_eq (st : NodeState A) : frame' st = st.fg.toFrame' := by rfl

end Consensus.Goldilocks.Node

end
