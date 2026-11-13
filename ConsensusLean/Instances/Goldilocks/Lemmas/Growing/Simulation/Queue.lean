module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Signing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Queue

public section

/-! # Growing-fault vote-pool and release-queue inventories

The inventories of `Simulation/Queue` under growing faults. Its `*_of_protected` forms take one run
fact beyond validity, the own-signature guard of a scheduled poll's ordinary attestation
(`PollAttProtected`); under growing faults it is `engine_poll_att_protected_at`
(`pollAttProtected`). The facts that need no fault premise are those of `Simulation/Queue`.
`scheduled_proposal_releasable` is the proposal-facing endpoint: the selected proposal's payload
objects are already in the engine's seen closure. `Steps` uses this inventory to relate engine
events to node steps. -/

namespace Consensus.Goldilocks.Simulation.GrowingInventory
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload SAState)

variable {binding : VoteBinding}

section Pools

variable {sp : SAParams} {FGP : Type}

/-- Restart replay only imports votes from its frame and its own emissions. The replay
enumeration exists for every well-formed frame; no global collision assumption is needed. -/
theorem restart_pool_inventory (P : Vote sp.n → Prop) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) (A : SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time)
    (hΦ : FrameOK Φ) (hB : ∀ B ∈ Φ.tree, ∀ v ∈ SA.blockVotes B, P v)
    (he : ∀ e ∈ (SA.acRestart sp ro self A Φ t).2, P e.msg) :
    ∀ s, ∀ v ∈ (SA.acRestart sp ro self A Φ t).1.pool s, P v :=
  Simulation.restart_pool_inventory P ro self A Φ t hΦ hB he

end Pools

section ShapeInventory

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- Polling, including the due FG update, leaves vote pools unchanged. -/
theorem poll_pool_eq (st : State sp ro binding) t :
    (poll st t).1.node.ac.pool = st.node.ac.pool :=
  Simulation.poll_pool_eq st t

end ShapeInventory

section EngineInventory

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The poll-attestation protection under growing faults** (`engine_poll_att_protected_at`). -/
theorem pollAttProtected (hv : rho.ExecutionValid) : PollAttProtected S rho hn :=
  (pollAttProtected_iff S rho hn).2 fun _ _ _ _ _ _ hc hd hsel _ _ hm =>
    engine_poll_att_protected_at S rho hn hv hc hd hsel hm

omit [DecidableEq V] in
/-- Every duty prefix preserves the fact that queued vote envelopes name stored
votes. In particular this applies to the polls of a tick, not only deliveries. -/
theorem runDuties_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (ds : List (Model.protoOf (compiled (goldilocksWith S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2 ∈ (shapeOf S hn nd).node.ac.pool tv.2.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.runDuties v nd ds).1).voteForwards,
      tv.2 ∈ (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool tv.2.slot :=
  Simulation.runDuties_voteForward_in_pool S rho hn v nd ds h

omit [DecidableEq V] in
/-- A single duty preserves queue backing, including its own released blocks. -/
theorem dutyStep_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (d : (Model.protoOf (compiled (goldilocksWith S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2 ∈ (shapeOf S hn nd).node.ac.pool tv.2.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.dutyStep v nd d).1).voteForwards,
      tv.2 ∈ (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool tv.2.slot :=
  Simulation.dutyStep_voteForward_in_pool S rho hn v nd d h

omit [DecidableEq V] in
/-- A single duty retains stored votes through its own-object release callbacks. -/
theorem dutyStep_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (d : (Model.protoOf (compiled (goldilocksWith S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool σ :=
  Simulation.dutyStep_pool_subset S rho hn v nd d σ

omit [DecidableEq V] in
/-- Duty execution never removes a stored vote; only restart replay can do so. -/
theorem runDuties_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (ds : List (Model.protoOf (compiled (goldilocksWith S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool σ :=
  Simulation.runDuties_pool_subset S rho hn v nd ds σ

/-- Pending canonical votes at actual duty boundaries are own votes of a slot whose vote role
selects the local signer. -/
theorem duty_cut_vote_member (hv : rho.ExecutionValid) {v : V} (hv' : v ∉ rho.faultyAt 0)
    {i p : Nat} {nd} (hc : EngineDutyCut S rho v i p nd) (m : Vote (Fintype.card V))
    (hm : Body.vote (encodeVote m) ∈ (shapeOf S hn nd).outbox) :
    m.val = rho.ownKey v ∧ rho.ownKey v ∈ rho.sel (S.vote.voteRole m.slot) :=
  Simulation.duty_cut_vote_member S rho hn hv hv' hc m hm

/-- At a tick duty prefix, every pooled vote is already held or pending in the
ordinary outbox. This retains the actual prefix state needed by release guards. -/
theorem tick_prefix_pool_available (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : p ≤ ((Model.protoOf (compiled (goldilocksWith S)) E).duties t).length)
    (σ : Nat) (m : Vote (Fintype.card V)) :
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocksWith S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocksWith S)) E).duties t).take p)).1
    m ∈ (shapeOf S hn nd).node.ac.pool σ →
      voteObj m ∈ Model.closure nd.seen ∨
        Body.vote (encodeVote m) ∈ (shapeOf S hn nd).outbox :=
  Simulation.tick_prefix_pool_available_of_protected S rho hn (pollAttProtected S rho hn hv) hv hv'
    he hw hp σ m

/-- Delivery processing keeps every queued admission's vote in the final pool. The actual
event-boundary queue is empty, and none of the delivery handlers restarts the AC. -/
theorem delivery_voteForward_in_pool (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (tv : Time × Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    tv.2 ∈ (process (stateAt S rho hn v i) o
      (Model.digests rho.hash o)).node.ac.pool tv.2.slot :=
  Simulation.delivery_voteForward_in_pool S rho hn hv v i o tv htv

/-- After processing a delivery, every stored vote is either actually held (including in
the delivered object's closure) or queued as a canonical own vote in the ordinary outbox. -/
theorem delivery_pool_available (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0)
    (i : Nat) (o : (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (σ : Nat) (m : Vote (Fintype.card V))
    (hm : m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool σ) :
    voteObj m ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
      Body.vote (encodeVote m) ∈
        (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox :=
  Simulation.delivery_pool_available_of_protected S rho hn (pollAttProtected S rho hn hv) hv hv' i
    o σ m hm

/-- At an actual delivery, the only not-yet-held stored vote is the ordinary outbox head:
the reachable one-vote invariant rules out a later queued vote. -/
theorem delivery_pool_held_or_head (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (σ : Nat) (m : Vote (Fintype.card V))
    (hm : m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool σ) :
    voteObj m ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.head? =
        some (.vote (encodeVote m)) :=
  Simulation.delivery_pool_held_or_head_of_protected S rho hn (pollAttProtected S rho hn hv) hv he
    σ m hm

/-- Any ordinary vote left by delivery processing is an own vote of a slot whose vote role
selects the receiving node. -/
theorem delivery_outbox_vote_member (hv : rho.ExecutionValid) {v : V}
    (_hv' : v ∉ rho.faultyAt 0) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocksWith S)) E).Object) (m : Vote (Fintype.card V))
    (hm : Body.vote (encodeVote m) ∈
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox) :
    m.val = rho.ownKey v ∧ rho.ownKey v ∈ rho.sel (S.vote.voteRole m.slot) :=
  Simulation.delivery_outbox_vote_member S rho hn hv _hv' i o m hm

/-- Every envelope queued by an actual delivery has its canonical dependency held or at
the ordinary outbox head. No queue-to-pool or readiness premise is left to the caller. -/
theorem delivery_voteForward_held_or_head (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (tv : Time × Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    voteObj tv.2 ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.head? =
        some (.vote (encodeVote tv.2)) :=
  Simulation.delivery_voteForward_held_or_head_of_protected S rho hn (pollAttProtected S rho hn hv)
    hv he tv htv

/-- Proposal payloads of actual scheduled honest duties were already released or received.
The proof uses engine-event inventory and the empty queue at the slot-start proposal. -/
theorem scheduled_proposal_releasable (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {t : Time} {s : Slot}
    {nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E)}
    (hscheduled : EngineProposalAt S rho v i p t s nd)
    {par : ParentRef} {info : Info} {cs : List (Wire (Fintype.card V) S.vote)}
    (hprop : (propose (shapeOf S hn nd) s).2 = some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure nd.seen :=
  Simulation.scheduled_proposal_releasable_of_protected S rho hn (pollAttProtected S rho hn hv) hv
    hv' hscheduled hprop

end EngineInventory

end Consensus.Goldilocks.Simulation.GrowingInventory

end
