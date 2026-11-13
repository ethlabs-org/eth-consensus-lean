module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Binding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.CommitteeVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run

public section

/-! # The committee facts of an outage query

The gate `Q.hGate`, and, on a run record of the query's trace, P (`Q.committeeP`: the pools and
the optimistic-check states) and the frames (`Q.hT`) hold for its dictionary `Q.K`
(`GS/CommitteeVotes`, with `Q.bindsSel`). With the committee size `Q.hsize` they are the committee
facts `Q.facts` of the outage chain. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation

variable {S : BoundSetup} {A : ContractAssumptions S.toSetup} {V : Type} [Fintype V] [DecidableEq V]

namespace OutageQueryAt

/-- **The gate**: a node honest at `0` may vote in slot `s` iff it is in `Q.K.committee s`. -/
theorem hGate (Q : OutageQueryAt S A V) :
    ∀ x, x ∈ Q.keys 0 → ∀ i s,
      (Q.trace.state x i).ac.mayVote s = true ↔ x ∈ Q.K.committee s :=
  simTraceAt_gate S Q.run.2 Q.hn Q.valid Q.bindsSel

variable (Q : OutageQueryAt S A V) {ini}
  (hrun : Growing.GoldilocksRun (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys Q.trace
    ini)
include hrun

/-- **P**: the pools of a node honest at `t`, before every cut whose earlier cuts are at times
`≤ t`, and its optimistic-check states at the cuts at which it is honest, hold only votes of
members of their slots. The start's pools are empty (`simIni_voteStart`); a later pool is the
post-state of an honest call (`simTraceAt_pool_member`), and an optimistic-check pool is in the
call's post-state pool (`SA.optimisticPoint_pool_post`). -/
theorem committeeP : SA.CommitteePAt Q.K Q.trace.projAC Q.keys := by
  have hpool := simTraceAt_pool_member S hrun Q.valid Q.bindsSel Q.noCollision
  refine ⟨fun t y hy i hi s v hv => ?_, fun y i ℓ A hy hpt s v hv => ?_⟩
  · cases i with
    | zero =>
      have h0 : (Q.trace.projAC.state y 0).pool s = [] := by
        change (((simTraceAt S Q.run.2 Q.hn).init y).ac).pool s = []
        rw [simTraceAt_eq, simTrace_init_eq]
        exact (simIni_voteStart S Q.run.2 Q.hn y).pool s
      rw [h0] at hv
      exact absurd hv List.not_mem_nil
    | succ i => exact hpool y i s (hrun.antitone (hi i (Nat.lt_succ_self i)) hy) v hv
  · have hm := hrun.time_mono
    have hacr := Compose.Growing.acRun_upTo hrun
      (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) (hrun.time_nonneg i)
    have hsub := SA.optimisticPoint_pool_post hacr.localRun hy
      ((SA.upTo_optimisticPoint hm).mpr ⟨le_rfl, hpt⟩) s hv
    rw [Trace.upTo_state Q.trace.projAC y fun k hk => hm (Nat.lt_succ_iff.mp hk)] at hsub
    exact hpool y i s hy v hsub

/-- **The frames of honest nodes carry votes of members.** -/
theorem hT :
    ∀ w c, w ∈ Q.keys (Q.trace.time c) → ∀ C ∈ (Node.frame (Q.trace.state w c)).tree,
      ∀ v ∈ SA.blockVotes C, v.val ∈ Q.K.committee v.slot :=
  simTraceAt_tree_member S hrun Q.valid Q.bindsSel

/-- **The committee facts of the outage query**: size, P, frames, and the gate read at every
read time `t ≥ 0` (a node honest at `t` is honest at `0`). -/
theorem facts : Compose.Growing.CommitteeFacts Q.trace Q.keys Q.K where
  hsize := Q.hsize
  hP := Q.committeeP hrun
  hFrame := Q.hT hrun
  hGate := fun _ ht x hx i _ s => Q.hGate x (hrun.antitone ht hx) i s

end OutageQueryAt

end Consensus.Goldilocks.Obligations.Growing

end
