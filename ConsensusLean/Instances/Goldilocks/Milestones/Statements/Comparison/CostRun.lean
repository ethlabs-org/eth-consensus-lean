module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.Cost
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection

@[expose] public section

/-! # Cost at Tier A on node runs: one tick per time (statement)

`TickOnceRun`: the premise `TickOnce` of the Tier A lock-memory claims (`Comparison/Cost`) holds
on the AC projection of every node run (`RunTrace.projAC` of a `Node.LocalRun`), for every node
AC. The other premises of `LockMemoryERAC0` and `LockMemoryCertAC0` on a node running a
candidate SA follow from the AC projection (C0.5, `ACProjection`) once that SA meets the AC
requirements, which no proof supplies yet. The parent's stage without the optimistic write has no
node: the composite runs the parent's write mode, where the optimistic write is on. -/

namespace Consensus.Goldilocks.Comparison

/-- **One tick per honest node and time on node runs**: the AC projection of every node run has
one tick per honest node and time. -/
def TickOnceRun : Prop :=
  ∀ (P : Params) (A : NodeAC P) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (H : Set (Fin P.n)) (sg : A.Msg → Fin P.n)
    (tr : RunTrace A), Node.LocalRun proposer dg H sg tr → TickOnce tr.projAC H

end Consensus.Goldilocks.Comparison

end
