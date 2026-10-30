module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace

public section

/-! # Goldilocks Refinement: the engine-side steps

What a valid engine run (`ExecutionValid`) does to the shape's state at each event, stated on
`stateAt`: the node state inside the shape's state after an event of an honest node is the
node's handler applied to the node state before it (a tick at a public time with the encoded
mempool, a delivery one `canonEvent` after the other, a restart), the shape's clock is the time of
the node's last tick or restart, and the obligations the #92 interface listed: at most two bodies
pending at a tick, a proposal carries only released objects (so `releasable` admits it), the
own-object guard `protects` never blocks an honest node, and the digests the engine passes with a
block object map its header to its root.

Each theorem is a named step; the `sorry` ones are open. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The node state after a delivery of the objects `os` at time `t` from `st`: the handler of
each canonical object in order, nothing for a dropped object (the state `deliverRecs` threads). -/
noncomputable def deliverState (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) :
    List (Wire sp.n) → NodeState (goldilocksNode sp ro) → NodeState (goldilocksNode sp ro)
  | [], st => st
  | o :: os, st =>
      match canonEvent sp ro hs o with
      | some e => deliverState dg hs self t os (exec dg self st t e).1
      | none => deliverState dg hs self t os st

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## The clock -/

/-- **`Simulates.now`.** The shape's clock before an engine cut is the time of the node's last
tick or restart before it. -/
theorem now_eq_lastClock (hv : rho.ExecutionValid) (v : V) (i : Nat) :
    (stateAt S rho hn v i).now = lastClock S rho v i := by
  sorry

/-! ## The node state across an event -/

/-- An engine tick of an honest node at a public time runs the node's tick with the encoded
mempool on the node state before it. -/
theorem node_of_tick_public (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node =
      (exec (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).1 := by
  sorry

/-- An engine tick at a non-public time leaves the node state unchanged. -/
theorem node_of_tick_other (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node = (stateAt S rho hn v i).node := by
  sorry

/-- An engine delivery to an honest node runs the handlers of the delivered canonical objects in
order on the node state before it, with the digests the engine passes. -/
theorem node_of_deliver (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (o : (Model.protoOf (compiled (family S)) E).Object) (t : Time)
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v (i + 1)).node =
      deliverState (digestOf S rho) (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node := by
  sorry

/-- An engine restart of an honest node runs the node's restart on the node state before it. -/
theorem node_of_restart (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.restart v t)) :
    (stateAt S rho hn v (i + 1)).node =
      (exec (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t .restart).1 := by
  sorry

/-- An event of another node leaves the shape's state unchanged. -/
theorem state_of_other (v : V) (i : Nat)
    (e : Model.Event V (Model.protoOf (compiled (family S)) E).Object)
    (he : rho.events[i]? = some e) (hne : e.node ≠ v) :
    stateAt S rho hn v (i + 1) = stateAt S rho hn v i := by
  sorry

/-! ## The release obligations -/

/-- **At most two bodies pending at a tick.** Between two ticks an honest node queues at most
its SA vote and its attestation, so two poll steps release everything queued. -/
theorem outbox_le_two (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) :
    (stateAt S rho hn v i).outbox.length ≤ 2 := by
  sorry

/-- After an awake honest node's tick at a public time nothing is pending: the tick's own bodies
were released by its last poll steps. -/
theorem outbox_empty_after_tick (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).outbox = [] := by
  sorry

/-- **A proposal carries only released objects.** The objects the slot proposal of an honest
node at its tick carries (its attestations' and votes' canonical objects) are in the closure of
what the node has seen, so the engine's `releasable` admits the block. -/
theorem proposal_releasable (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (par : ParentRef)
    (info : Info) (cs : List (Wire (Fintype.card V)))
    (hprop : (propose { stateAt S rho hn v i with now := t } s).2 = some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure (rho.stateBefore i v).seen := by
  sorry

/-- **`protects` never blocks an honest node.** An honest node's own attestation in its pool
passes the own-object guard against everything it has seen: an honest signer's attestations
never conflict (`non_framing`, Lemmas/Compose/Regimes). -/
theorem protects_own_att (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (a : FG.Att (Fintype.card V)) (ha : a ∈ (stateAt S rho hn v i).node.fg.atts)
    (hself : a.val = rho.ownKey v) :
    Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v)
      (rho.stateBefore i v).seen (attObj a) = true := by
  sorry

omit [DecidableEq V] in
/-- The digests the engine passes with a block object map the block's header to the engine's
hash of it. -/
theorem rootOf_digests_blockObj (B : Blk (S.params (pubOf E) hn)) :
    rootOf (Model.digests rho.hash (blockObj (S.params (pubOf E) hn) B))
        (headerOf (S.params (pubOf E) hn) B) =
      some (rho.hash (headerOf (S.params (pubOf E) hn) B)) := by
  sorry

omit [DecidableEq V] in
/-- The digests the engine passes with a relay wrapper map the header of each carried block
object to the engine's hash of it. -/
theorem rootOf_digests_relay (cs : List (Wire (Fintype.card V))) (B : Blk (S.params (pubOf E) hn))
    (hB : blockObj (S.params (pubOf E) hn) B ∈ cs) :
    rootOf (Model.digests rho.hash (.mk .none (.data .relay) cs))
        (headerOf (S.params (pubOf E) hn) B) =
      some (rho.hash (headerOf (S.params (pubOf E) hn) B)) := by
  sorry

end Consensus.Goldilocks.Refinement

end
