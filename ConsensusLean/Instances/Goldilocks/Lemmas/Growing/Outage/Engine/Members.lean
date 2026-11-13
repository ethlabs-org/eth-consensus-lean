module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Binding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.CommitteeVotes

public section

/-! # The committee facts of an outage query

The gate `Q.hGate`, the casters `Q.hG`, and, on a run record of the query's trace, the pools
`Q.hPool`, the frames `Q.hT` and the merged views `Q.hMerged` hold for its dictionary `Q.K`
(`GS/CommitteeVotes`, with `Q.bindsSel`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation

variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

namespace OutageQueryAt

/-- **The gate**: a node honest at `0` may vote in slot `s` iff it is in `Q.K.committee s`. -/
theorem hGate (Q : OutageQueryAt S A V) :
    ∀ x, x ∈ Q.keys 0 → ∀ i s,
      (Q.trace.state x i).ac.mayVote s = true ↔ x ∈ Q.K.committee s :=
  simTraceAt_gate S Q.run.2 Q.hn Q.valid Q.bindsSel

/-- **Honest casters are members** of their votes' committees. -/
theorem hG (Q : OutageQueryAt S A V) :
    ∀ x i e, Compose.Growing.HVoteAt Q.trace Q.keys x i e → x ∈ Q.K.committee e.msg.slot :=
  fun x i e hv => simTraceAt_vote_member S Q.run.2 Q.hn Q.valid Q.bindsSel x i e
    (Compose.Growing.hVoteAt_iff.1 hv).2

variable (Q : OutageQueryAt S A V)
  (hrun : Growing.GoldilocksRun (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys Q.trace)
include hrun

/-- **The pool after an honest call holds votes of members of its slot.** -/
theorem hPool :
    ∀ w c m, w ∈ Q.keys (Q.trace.time c) →
      ∀ v ∈ (Q.trace.projAC.state w (c + 1)).pool m, v.val ∈ Q.K.committee m :=
  simTraceAt_pool_member S hrun Q.valid Q.bindsSel Q.noCollision

/-- **The frames of honest nodes carry votes of members.** -/
theorem hT :
    ∀ w c, w ∈ Q.keys (Q.trace.time c) → ∀ C ∈ (Node.frame (Q.trace.state w c)).tree,
      ∀ v ∈ SA.blockVotes C, v.val ∈ Q.K.committee v.slot :=
  simTraceAt_tree_member S hrun Q.valid Q.bindsSel

/-- **The merged view of an honest cast holds votes of members.** -/
theorem hMerged :
    ∀ y i ℓ e m, y ∈ Q.keys (Q.trace.time i) → SA.CastAt Q.trace.projAC y i ℓ e →
      ∀ v ∈ (SA.mergedVoteView Q.params e.readPoint ℓ.frame m).votes,
        v.val ∈ Q.K.committee v.slot :=
  simTraceAt_merged_member S hrun Q.valid Q.bindsSel Q.noCollision

end OutageQueryAt

end Consensus.Goldilocks.Obligations.Growing

end
