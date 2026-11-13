module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteForwardQueue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Queue

public section

/-! # Same-event forwarding of freshly pooled votes: the node-local steps

A vote that an engine event newly inserts into a node's pool is queued as a vote-forward envelope
before the event's releasing poll. The queueing reads the node's own steps only; the release of a
delivery's queue reads two facts that depend on the fault model, and they are premises:

* `tick_pool_insertion_queued`: a tick's insertion is queued before the tick's trailing polls;
* `delivery_voteForward_released_of`: when each envelope a delivery queues has its vote held or at
  the outbox head, and the delivering node is honest at `0`, the delivery releases every one;
* `delivery_pool_insertion_queued`: a delivery's insertion is queued by its processing.

Constant faults (`Simulation/Core`) and growing faults (`Growing/Simulation/VoteForwardRelease`)
supply the premises. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- **A tick's pool insertion is queued before its trailing polls.** A vote `m` that the tick
event `i` of `v` at `t` newly inserts into `v`'s pool is the envelope `(t, m)` of the shape after
the tick's leading polls and proposal duties. -/
theorem tick_pool_insertion_queued (hv : rho.ExecutionValid) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    (t, m) ∈ (shapeOf S hn (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocksWith S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++
        (skeleton (pubOf E) S.vote).proposeAt t)).1).voteForwards := by
  have hsel := poll_selected S rho hv v
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hbase : m ∈ (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node.ac.pool m.slot →
      (t, m) ∈ (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).voteForwards := by
    rw [atProposal_shape S rho hn v _ t hsel, ← stateAt_eq S rho hn v i]
    let st := (poll (poll { stateAt S rho hn v i with now := t } t.toNat).1 t.toNat).1
    have hn' : st.node = (stateAt S rho hn v i).node := by
      dsimp only [st]
      rw [poll_node_of_fgDue _ _ (poll_fgDue _ _)]
      exact poll_node_of_fgDue { stateAt S rho hn v i with now := t } _
        (fgDue_eq_false S rho hn v i)
    have ht' : st.now = t := by dsimp only [st]; rw [poll_now, poll_now]
    intro hm
    have hq := nodeTick_pool_insertion_queued st m (hn' ▸ hold) hm
    rwa [ht'] at hq
  have hpool : m ∈ (shapeOf S hn (rho.runDuties v
      (atProposal S rho v (rho.stateBefore i v) t)
      ((skeleton (pubOf E) S.vote).proposeAt t)).1).node.ac.pool m.slot := by
    rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw hsel,
      poll_pool_eq, poll_pool_eq] at hnew
    exact hnew
  have hq := proposal_pool_insertion_queued S rho hn v
    (atProposal S rho v (rho.stateBefore i v) t) t m
    (by rw [atProposal_now S rho hn v _ t hsel]; exact hbase) hpool
  rw [atProposal_now S rho hn v _ t hsel] at hq
  erw [runDuties_fst_append]
  rw [atProposal_eq] at hq
  exact hq

/-- **A delivery releases every envelope it queues.** Premises: `hheld`, each queued vote is held
in the seen closure or at the outbox head (`delivery_voteForward_held_or_head` for constant faults,
`GrowingInventory.delivery_voteForward_held_or_head` for growing faults); `hv'`, the delivering
node is honest at `0`, so it signs the outbox votes. -/
theorem delivery_voteForward_released_of (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0)
    {i : Nat} {o : (Model.protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (hheld : ∀ tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards,
      voteObj tv.2 ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
        (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.head? =
          some (.vote (encodeVote tv.2)))
    (tv : Time × SA.Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈ rho.releasesAt i := by
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  let nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E) :=
    ⟨(Model.protoOf (compiled (goldilocksWith S)) E).process (rho.stateBefore i v).st o
      (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
  have hshape : shapeOf S hn nd =
      process (stateAt S rho hn v i) o (Model.digests rho.hash o) := by
    rw [stateAt_eq]; rfl
  have hself : (shapeOf S hn nd).self = rho.ownKey v := by
    rw [hshape]; exact (process_self _ _ _).trans (self_eq_ownKey S rho hn v i)
  have hfg : (shapeOf S hn nd).fgDue = false := by
    rw [hshape]; exact (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
  have hpre : pollPre (shapeOf S hn nd) = shapeOf S hn nd := by
    rw [pollPre_eq, hfg]; rfl
  have hav : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      voteObj q.2 ∈ Model.closure nd.seen ∨
        (shapeOf S hn nd).outbox.head? = some (.vote (encodeVote q.2)) := by
    intro q hq
    rw [hshape]
    exact hheld q (hshape ▸ hq)
  have hrel : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
    by_cases hh : ∀ q ∈ (shapeOf S hn nd).voteForwards, voteObj q.2 ∈ Model.closure nd.seen
    · exact dutyStep_poll_voteForward S rho hn v nd t.toNat (poll_selected S rho hv v) hself hh
    · push Not at hh
      obtain ⟨q, hq, hnot⟩ := hh
      have hhead := (hav q hq).resolve_left hnot
      obtain ⟨hsign, hk⟩ := delivery_outbox_vote_member S rho hn hv hv' i o q.2
        (List.mem_of_mem_head? (Option.mem_def.mpr (hshape ▸ hhead)))
      apply dutyStep_poll_voteForward_of_own_vote S rho hn v nd t.toNat
        (poll_selected S rho hv v) hself q.2 hsign hk (by rw [hpre]; exact hhead)
      intro r hr
      rcases hav r hr with h | h
      · exact Or.inr h
      · left
        have heq := Body.vote.inj (Option.some.inj (h.symm.trans hhead))
        have hd := congrArg (decodeVote (Fintype.card V)) heq
        simpa only [decodeVote_encodeVote, Option.some.injEq] using hd
  have hout := hrel tv (hshape ▸ htv)
  simp only [Model.Run.releasesAt, he]
  unfold Model.Run.deliver
  rw [deliverDuties_eq S t ht]
  apply List.mem_append_left
  erw [Model.Run.runDuties_cons]
  exact List.mem_append_left _ hout

/-- **A delivery's pool insertion is queued by its processing.** A vote `m` that the delivery
event `i` of `v` at `t` newly inserts into `v`'s pool, `v` honest at `0`, is the envelope `(t, m)`
of the processed shape. -/
theorem delivery_pool_insertion_queued (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0)
    {i : Nat} {o : (Model.protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    (t, m) ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards := by
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hnode : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node =
      (stateAt S rho hn v (i + 1)).node := by
    rw [node_of_deliver S rho hn hv v hv' i o t he]
    unfold process
    erw [foldl_processOne_node (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) (digestOf S rho)]
    rw [self_eq_ownKey, hnow]
  rw [← hnow]
  unfold process
  exact foldl_processOne_pool_insertion_queued (sp := S.params (pubOf E) hn)
    (ro := S.ro _) (Model.digests rho.hash o) _ (stateAt S rho hn v i) m hold
    (show m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool m.slot
      from hnode.symm ▸ hnew)

end Consensus.Goldilocks.Simulation

end
