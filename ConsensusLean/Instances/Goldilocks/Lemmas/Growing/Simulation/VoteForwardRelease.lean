module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant

public section

/-! # Same-event release of freshly pooled vote envelopes

Release guards use the actual engine inventory, without a constant honest set.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem tick_prefix_forward_poll (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : p ≤ ((Model.protoOf (compiled (goldilocks S)) E).duties t).length) :
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1
    (shapeOf S hn nd).outbox.length ≤ 1 →
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
  intro nd hlen
  apply dutyStep_poll_voteForward_of_available S rho hn hv hv' (.tick he hw hp) t.toNat hlen
  intro q hq
  apply GrowingInventory.tick_prefix_pool_available S rho hn hv hv' he hw hp q.2.slot q.2
  apply runDuties_voteForward_in_pool S rho hn v _ _ ?_ q hq
  intro r hr
  change r ∈ ((rho.stateBefore i v).st.1 hn).voteForwards at hr
  rw [← stateAt_eq S rho hn v i, voteForwards_empty S rho hn hv v i] at hr
  cases hr

private theorem tick_forward_released (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {t : Time} (he : rho.events[i]? = some (.tick v t)) :
    let pre : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
      [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ (skeleton (pubOf E)).proposeAt t
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ pre).1
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈ rho.releasesAt i := by
  intro pre nd q hq
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hd : (Model.protoOf (compiled (goldilocks S)) E).duties t =
      pre ++ [.poll t.toNat, .poll t.toNat] := by
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  have htake : ((Model.protoOf (compiled (goldilocks S)) E).duties t).take pre.length = pre := by
    rw [hd, List.take_left]
  have hlen : pre.length ≤ ((Model.protoOf (compiled (goldilocks S)) E).duties t).length := by
    rw [hd, List.length_append]; omega
  have h := tick_prefix_forward_poll S rho hn hv (event_honest_zero S rho hv he) he hw hlen
  rw [htake] at h
  have hbound : (shapeOf S hn nd).outbox.length ≤ 1 := by
    dsimp only [nd, pre]
    erw [runDuties_fst_append]
    apply outbox_after_pre S rho hn v (stateAt S rho hn v i) t ht
      (fgDue_eq_false S rho hn v i)
    · rw [outbox_empty S rho hn hv v i]; simp
    · rw [stateAt_eq]
      exact pre_shape S rho hn v (rho.stateBefore i v) t (poll_selected S rho hv v)
  have hrel := h hbound q hq
  simp only [Model.Run.releasesAt, he]
  rw [rho.tick_of_awake _ _ _ hw]
  apply List.mem_append_left
  have hd' : (Model.protoOf (compiled (goldilocks S)) E).duties t =
      pre ++ .poll t.toNat :: [.poll t.toNat] := hd
  rw [hd']
  exact duty_release_in_runDuties S rho v _ pre _ _ _ hrel

/-- A tick's aggregate pool insertion is released in its trailing poll. -/
theorem tick_pool_insertion_released_at (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {t : Time} (he : rho.events[i]? = some (.tick v t))
    (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i := by
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
      ((skeleton (pubOf E)).proposeAt t)).1).node.ac.pool m.slot := by
    rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw hsel,
      poll_pool_eq, poll_pool_eq] at hnew
    exact hnew
  have hq := proposal_pool_insertion_queued S rho hn v
    (atProposal S rho v (rho.stateBefore i v) t) t m
    (by rw [atProposal_now S rho hn v _ t hsel]; exact hbase) hpool
  rw [atProposal_now S rho hn v _ t hsel] at hq
  apply tick_forward_released S rho hn hv he (t, m)
  erw [runDuties_fst_append]
  rw [atProposal_eq] at hq
  exact hq

private theorem delivery_forward_released (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (tv : Time × SA.Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈ rho.releasesAt i := by
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  let nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
    ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
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
    exact GrowingInventory.delivery_voteForward_held_or_head S rho hn hv he q (hshape ▸ hq)
  have hrel : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
    by_cases hh : ∀ q ∈ (shapeOf S hn nd).voteForwards, voteObj q.2 ∈ Model.closure nd.seen
    · exact dutyStep_poll_voteForward S rho hn v nd t.toNat (poll_selected S rho hv v) hself hh
    · push Not at hh
      obtain ⟨q, hq, hnot⟩ := hh
      have hhead := (hav q hq).resolve_left hnot
      have hsign := GrowingInventory.delivery_outbox_vote_signer S rho hn hv
        (event_honest_zero S rho hv he) i o q.2
        (List.mem_of_mem_head? (Option.mem_def.mpr (hshape ▸ hhead)))
      apply dutyStep_poll_voteForward_of_own_vote S rho hn v nd t.toNat
        (poll_selected S rho hv v) hself q.2 hsign (by rw [hpre]; exact hhead)
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

/-- A delivery's aggregate pool insertion is forwarded in that same event. -/
theorem delivery_pool_insertion_released_at (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i := by
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hnode : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node =
      (stateAt S rho hn v (i + 1)).node := by
    rw [node_of_deliver S rho hn hv v (event_honest_zero S rho hv he) i o t he]
    unfold process
    erw [foldl_processOne_node (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) (digestOf S rho)]
    rw [self_eq_ownKey, hnow]
  apply delivery_forward_released S rho hn hv he (t, m)
  rw [← hnow]
  unfold process
  exact foldl_processOne_pool_insertion_queued (sp := S.params (pubOf E) hn)
    (ro := S.ro _) (Model.digests rho.hash o) _ (stateAt S rho hn v i) m hold
    (show m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool m.slot
      from hnode.symm ▸ hnew)

end Consensus.Goldilocks.Simulation
