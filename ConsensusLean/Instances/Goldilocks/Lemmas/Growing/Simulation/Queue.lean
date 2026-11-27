module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Signing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Queue

public section

/-! # Growing-fault vote-pool and release-queue inventories

The inventories of `Simulation/Queue` under growing faults.
`scheduled_proposal_releasable` is the proposal-facing endpoint: the selected proposal's payload
objects are already in the engine's seen closure. `Steps` uses this inventory to relate engine
events to node steps. -/

namespace Consensus.Goldilocks.Simulation.GrowingInventory
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams Vote Payload ACState)

variable {binding : VoteBinding}

section Pools

variable {sp : ACParams} {FGP : Type}

/-- Restart replay can only add actual emissions to its cleared pools. -/
theorem restart_pool_inventory (P : Vote sp.n → Prop)
    (self : Fin sp.n) (A : ACState sp.n) (Φ : AC.Frm sp.n FGP) (t : Time)
    (he : ∀ e ∈ (AC.acRestart sp self A Φ t).2, P e.msg) :
    ∀ s, ∀ v ∈ (AC.acRestart sp self A Φ t).1.pool s, P v :=
  Simulation.restart_pool_inventory P self A Φ t he

end Pools

section ShapeInventory

variable {sp : ACParams}

/-- A batch poll, including the due FG update and any flush of held attestations, leaves vote
pools unchanged, at every release schedule. -/
theorem poll_pool_eq {release : Fin sp.n → Time → Bool} (st : State sp binding) t :
    (pollBatch st t release).1.node.ac.pool = st.node.ac.pool :=
  Simulation.poll_pool_eq st t

end ShapeInventory

section EngineInventory

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)


omit [DecidableEq V] in
/-- Every duty prefix preserves the fact that queued vote envelopes name stored
votes. In particular this applies to the polls of a tick, not only deliveries. -/
theorem runDuties_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2.1 ∈ (shapeOf S hn nd).node.ac.pool tv.2.1.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.runDuties v nd ds).1).voteForwards,
      tv.2.1 ∈ (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool tv.2.1.slot :=
  Simulation.runDuties_voteForward_in_pool S rho hn v nd ds h

omit [DecidableEq V] in
/-- A single duty preserves queue backing, including its own released blocks. -/
theorem dutyStep_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2.1 ∈ (shapeOf S hn nd).node.ac.pool tv.2.1.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.dutyStep v nd d).1).voteForwards,
      tv.2.1 ∈ (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool tv.2.1.slot :=
  Simulation.dutyStep_voteForward_in_pool S rho hn v nd d h

omit [DecidableEq V] in
/-- A single duty retains stored votes through its own-object release callbacks. -/
theorem dutyStep_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool σ :=
  Simulation.dutyStep_pool_subset S rho hn v nd d σ

omit [DecidableEq V] in
/-- Duty execution never removes a stored vote; only restart can do so. -/
theorem runDuties_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool σ :=
  Simulation.runDuties_pool_subset S rho hn v nd ds σ

/-- Pending canonical votes at actual duty boundaries are own votes of a slot whose vote role
selects the local signer. -/
theorem duty_cut_vote_member (hv : rho.ExecutionValid) {v : V} (hv' : v ∉ rho.faultyAt 0)
    {i p : Nat} {nd} (hc : EngineDutyCut S rho v i p nd) (m : Vote (Fintype.card V)) {z : Nat}
    (hm : Body.vote (encodeVote m) z ∈ (shapeOf S hn nd).outbox) :
    m.val = rho.ownKey v ∧ rho.ownKey v ∈ rho.sel (S.vote.voteRole m.slot) :=
  Simulation.duty_cut_vote_member S rho hn hv hv' hc m hm

/-- Delivery processing keeps every queued admission's vote in the final pool. The actual
event-boundary queue is empty, and none of the delivery handlers restarts the AC. -/
theorem delivery_voteForward_in_pool (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (tv : Time × Vote (Fintype.card V) × Wire (Fintype.card V) S.vote)
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    tv.2.1 ∈ (process (stateAt S rho hn v i) o
      (Model.digests rho.hash o)).node.ac.pool tv.2.1.slot :=
  Simulation.delivery_voteForward_in_pool S rho hn hv v i o tv htv

/-- Any ordinary vote left by delivery processing is an own vote of a slot whose vote role
selects the receiving node. -/
theorem delivery_outbox_vote_member (hv : rho.ExecutionValid) {v : V}
    (_hv' : v ∉ rho.faultyAt 0) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (m : Vote (Fintype.card V))
    {z : Nat} (hm : Body.vote (encodeVote m) z ∈
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox) :
    m.val = rho.ownKey v ∧ rho.ownKey v ∈ rho.sel (S.vote.voteRole m.slot) :=
  Simulation.delivery_outbox_vote_member S rho hn hv _hv' i o m hm

/-- Proposal payloads of actual scheduled honest duties were already released or received.
The proof uses engine-event inventory and the empty queue at the slot-start proposal. -/
theorem scheduled_proposal_releasable (hv : rho.ExecutionValid)
    {v : V} {i p : Nat} {t : Time} {s : Slot}
    {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hscheduled : EngineProposalAt S rho v i p t s nd)
    {par : ParentRef} {info : Info} {cs : List (Wire (Fintype.card V) S.vote)}
    (hprop : (propose (shapeOf S hn nd) s).2 = some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure nd.seen :=
  Simulation.scheduled_proposal_releasable S rho hn hv hscheduled hprop

end EngineInventory

end Consensus.Goldilocks.Simulation.GrowingInventory

end
