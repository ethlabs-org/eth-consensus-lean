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

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

private theorem tick_prefix_forward_poll (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : p ≤ ((Model.protoOf (compiled (goldilocksWith S)) E).duties t).length) :
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocksWith S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocksWith S)) E).duties t).take p)).1
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
    let pre : List (Model.protoOf (compiled (goldilocksWith S)) E).Duty :=
      [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ (skeleton
          (pubOf E) S.vote).proposeAt t
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocksWith S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ pre).1
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈ rho.releasesAt i := by
  intro pre nd q hq
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hd : (Model.protoOf (compiled (goldilocksWith S)) E).duties t =
      pre ++ [.poll t.toNat, .poll t.toNat] := by
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  have htake : ((Model.protoOf (compiled (goldilocksWith S)) E).duties t).take pre.length = pre
      := by
    rw [hd, List.take_left]
  have hlen : pre.length ≤ ((Model.protoOf (compiled (goldilocksWith S)) E).duties t).length := by
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
  have hd' : (Model.protoOf (compiled (goldilocksWith S)) E).duties t =
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
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i :=
  tick_forward_released S rho hn hv he (t, m)
    (tick_pool_insertion_queued S rho hn hv he m hold hnew)

/-- A delivery's aggregate pool insertion is forwarded in that same event. -/
theorem delivery_pool_insertion_released_at (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i :=
  delivery_voteForward_released_of S rho hn hv (event_honest_zero S rho hv he) he
    (GrowingInventory.delivery_voteForward_held_or_head S rho hn hv he) (t, m)
    (delivery_pool_insertion_queued S rho hn hv (event_honest_zero S rho hv he) he m hold hnew)

end Consensus.Goldilocks.Simulation
