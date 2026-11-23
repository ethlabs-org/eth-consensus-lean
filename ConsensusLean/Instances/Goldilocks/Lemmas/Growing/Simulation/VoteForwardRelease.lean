module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteForwardQueue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PoolInsertionRelease

public section

/-! # Same-event release of freshly pooled vote envelopes

Release guards use the actual engine inventory, without a constant honest set.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every queued envelope carries an own canonical vote object whose same-token body is queued:
a tick queues only own emissions, and each poll drains the queue. -/
private def OwnQueued (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) : Prop :=
  ∀ q ∈ st.voteForwards, ∃ z, q.2.2 = voteObj q.2.1 z ∧ Body.vote (encodeVote q.2.1) z ∈ st.outbox

omit [DecidableEq V] in
private theorem ownQueued_apply (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) r
    (h : OwnQueued S hn st) : OwnQueued S hn (apply st none r) := by
  rintro ⟨t, m, w⟩ hq
  rcases apply_voteForward_obj S st none r t m w hq with hq | hown | ⟨h', -⟩
  · obtain ⟨z, hz, hb⟩ := h _ hq
    exact ⟨z, hz, List.mem_append_left _ hb⟩
  · exact hown
  · cases h'

omit [DecidableEq V] in
private theorem ownQueued_recordOwn (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) o hs
    (h : OwnQueued S hn st) : OwnQueued S hn (recordOwn st o hs) := by
  rw [AsChainShape.recordOwn_eq]
  split
  · exact h
  · split
    · exact ownQueued_apply S hn st _ h
    · exact h
  · exact h

omit [DecidableEq V] in
private theorem ownQueued_propose (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) s
    (h : OwnQueued S hn st) : OwnQueued S hn (propose st s).1 := by
  rw [propose_eq]; dsimp only; split <;> exact h

omit [DecidableEq V] in
private theorem ownQueued_nodeTick (st : State (S.params (pubOf E) hn) (S.ro _) S.vote)
    (h : OwnQueued S hn st) : OwnQueued S hn (nodeTick st) := by
  rw [nodeTick_eq]
  split
  · exact ownQueued_apply S hn st _ h
  · exact h

omit [DecidableEq V] in
private theorem ownQueued_poll (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) u :
    OwnQueued S hn (poll st u).1 := by
  intro q hq
  rw [poll_voteForwards] at hq
  cases hq

private theorem tick_prefix_forward_poll (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : p ≤ ((Model.protoOf (compiled (goldilocks S)) E).duties t).length) :
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1
    (shapeOf S hn nd).outbox.length ≤ 1 →
    ∀ q ∈ (shapeOf S hn nd).voteForwards, (∃ z, q.2.2 = voteObj q.2.1 z) ∧
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2.1))) [q.2.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
  intro nd hlen
  have hown : OwnQueued S hn (shapeOf S hn nd) := by
    refine runDuties_pres S rho hn (OwnQueued S hn) (ownQueued_recordOwn S hn)
      (ownQueued_propose S hn) (ownQueued_nodeTick S hn) (fun st u _ => ownQueued_poll S hn st u)
      v _ _ ?_
    intro r hr
    change r ∈ ((rho.stateBefore i v).st.1 hn).voteForwards at hr
    rw [← stateAt_eq S rho hn v i, voteForwards_empty S rho hn hv v i] at hr
    cases hr
  intro q hq
  refine ⟨(hown q hq).imp fun _ h => h.1, ?_⟩
  refine dutyStep_poll_voteForward_of_available S rho hn hv hv' (.tick he hw hp) t.toNat hlen
    (fun q hq => ?_) q hq
  obtain ⟨z, hz, hb⟩ := hown q hq
  exact ⟨z, hz, Or.inr hb⟩

private theorem tick_forward_released (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {t : Time} (he : rho.events[i]? = some (.tick v t)) :
    let pre : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
      [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ (skeleton
          (pubOf E) S.vote).proposeAt t
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ pre).1
    ∀ q ∈ (shapeOf S hn nd).voteForwards, (∃ z, q.2.2 = voteObj q.2.1 z) ∧
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2.1))) [q.2.2] ∈ rho.releasesAt i := by
  intro pre nd q hq
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hd : (Model.protoOf (compiled (goldilocks S)) E).duties t =
      pre ++ [.poll t.toNat, .poll t.toNat] := by
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  have htake : ((Model.protoOf (compiled (goldilocks S)) E).duties t).take pre.length = pre
      := by
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
  obtain ⟨hz, hrel⟩ := h hbound q hq
  refine ⟨hz, ?_⟩
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
    (m : AC.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    ∃ z, Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m z] ∈ rho.releasesAt i := by
  obtain ⟨w, hw⟩ := tick_pool_insertion_queued S rho hn hv he m hold hnew
  obtain ⟨⟨z, hz⟩, hrel⟩ := tick_forward_released S rho hn hv he (t, m, w) hw
  dsimp only at hz hrel
  exact ⟨z, hz ▸ hrel⟩

/-- A delivery's aggregate pool insertion is forwarded in that same event. -/
theorem delivery_pool_insertion_released_at (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (m : AC.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    ∃ z, Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m z] ∈ rho.releasesAt i := by
  have hv' := event_honest_zero S rho hv he
  obtain ⟨w, hw⟩ := delivery_pool_insertion_queued S rho hn hv hv' he m hold hnew
  have hheld := delivery_voteForward_canonical_held S rho hn hv he
  obtain ⟨z, hz, -⟩ := hheld _ hw
  dsimp only at hz
  subst hz
  exact ⟨z, delivery_voteForward_released_of S rho hn hv hv' he hheld (t, m, _) hw⟩

end Consensus.Goldilocks.Simulation
