module
public import Mathlib.Data.Fintype.Card
public import ConsensusLean.Spec.Model.Protocol

@[expose] public section

/-! # Runs and the engine (L1)

A run fixes everything the protocol does not choose: the honest set, the
horizon, the scheduler's events, the PKI (which validator owns each key), the
selection (which keys act in each role), the transactions submitted to every
node and those the network relays to it, and the hash function. The engine runs the protocol on
the events. Per node it keeps the protocol state and the `seen` log of every
object the node released or received.

At a tick of awake node `v` at `t`, the engine
1. runs `clock` with `v`'s own and relayed transactions up to `t` (its mempool);
2. runs the due duties one after the other, in `duties` order, each from the
   state the previous one left. A duty whose role does not select `v`'s key is
   skipped: no state change and no candidates (`dutyStep`). A selected duty's
   `act` gives a new state, which the engine applies, and a message, which
   becomes a candidate signed with `v`'s own key in the duty's role and goes
   through release (3) before the next duty runs;
3. releases a candidate only if every object it carries is already in the
   closure of `seen` (so honest code passes on no object it has not seen),
   slashing protection allows it (`protects`: a candidate signed by the own
   key must not conflict, under the protocol's `conflicts`, with itself or
   with an own-signed object in the closure of `seen`), and its dependencies
   are held (`P.dependencies.ready` on the closure of `seen`); it then adds it
   to `seen` and records it with `recordOwn`;
4. last, builds unsigned gossip from the final state and releases it as in 3.

Same-tick semantics: a duty reads the state after the earlier duties of the
tick, including the `recordOwn` of their released messages (which is how a
node learns that it signed). It gets no other feedback: a selected duty whose
candidates are refused leaves only its own state; an unselected duty leaves
nothing. Duties run only at awake
ticks and at deliveries (which the conditions make only to awake nodes).

At a raw arrival to awake node `v` at `t`, the engine runs `process`, adds the
object to `seen`, then runs the protocol's `deliverDuties t` as in 2–3 and
gossip as in 4, from the processed state: what the delivery makes the node
emit, relay or acknowledge leaves at the delivery's own time, not at the
next tick (which may never come if the node sleeps). The engine neither checks
incoming dependency readiness nor buffers arrivals; admission and retries are
the protocol's responsibility. The durable `seen` log is evidence, not a retry queue.
At a restart it runs
`restore` (with the own key) of
`durable`, keeping `seen`. The `seen` log survives restarts, so slashing
protection persists across them, as a validator's slashing-protection
database does (EIP-3076); that the deployed engine keeps it is part of model
adequacy. A node starts in `init` of its own key. Only the
engine evaluates the hash: with every object processed or recorded it passes
the digests of the items in the object's closure. -/

namespace Consensus.Model

/-- A scheduler event at a node: a tick, the delivery of an object, or a
restart (which the conditions allow only at a wake). -/
inductive Event (V O : Type) where
  | tick (v : V) (t : Time)
  | deliver (v : V) (o : O) (t : Time)
  | restart (v : V) (t : Time)
  deriving DecidableEq

namespace Event
variable {V O : Type}
def time : Event V O → Time
  | tick _ t => t
  | deliver _ _ t => t
  | restart _ t => t
def node : Event V O → V
  | tick v _ => v
  | deliver v _ _ => v
  | restart v _ => v
/-- Restarts first at a time, then ticks, then deliveries. -/
def phase : Event V O → Nat
  | restart _ _ => 0
  | tick _ _ => 1
  | deliver _ _ _ => 2
def keyLe (e f : Event V O) : Prop :=
  e.time < f.time ∨ (e.time = f.time ∧ e.phase ≤ f.phase)
end Event

/-- The public parameters of an environment. -/
abbrev pubOf {V : Type} [Fintype V] (E : Env V) : Public :=
  ⟨Fintype.card V, E.Δ, E.Δ_pos, E.ΔF, E.ΔF_pos⟩

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The protocol that family `F` runs in environment `E`. -/
abbrev protoOf {O : OutputSchema} (F : Family O) (E : Env V) : Protocol (pubOf E) O.Id :=
  F (pubOf E)

/-- A run of family `F` in environment `E`. -/
structure Run {O : OutputSchema} (F : Family O) (E : Env V) where
  honest : Finset V
  horizon : Time
  events : List (Event V (protoOf F E).Object)
  /-- The PKI: key `k` belongs to validator `key k`. A bijection, so distinct
  keys are distinct validators. -/
  key : Fin (Fintype.card V) ≃ V
  /-- The selection: the keys acting in each role. Admissibility for the
  protocol's `selSpec` is an execution condition (`ExecutionValid.selValid`). -/
  sel : (protoOf F E).Role → Finset (Fin (Fintype.card V))
  /-- The transactions submitted to every node at every time. -/
  submit : V → Time → List Tx
  /-- Transactions relayed by the network, chosen by the scheduler. -/
  relay : V → Time → List Tx
  /-- The hash function: arbitrary, possibly with collisions; evaluated only by
  the engine. -/
  hash : (protoOf F E).Item → Nat

variable {O : OutputSchema} {F : Family O} {E : Env V}

/-- The environment point of a run. -/
def Run.point (rho : Run F E) : EnvPoint V := ⟨E, rho.honest, rho.horizon, rho.submit⟩

/-- Own submissions and network ingress are indistinguishable to honest code. -/
def Run.inbox (rho : Run F E) (v : V) (t : Time) : List Tx :=
  rho.submit v t ++ rho.relay v t

/-- An engine node: the protocol state and the `seen` log. -/
structure Node {pub : Public} {Out : Type} (P : Protocol pub Out) where
  st : P.State
  seen : List P.Object

/-- The closure of a list of objects: the objects and everything they carry. -/
def closure {pub : Public} {Out : Type} {P : Protocol pub Out} (l : List P.Object) :
    List P.Object :=
  l.flatMap Obj.parts

/-- The digests the engine passes with object `o`: every item in its closure. -/
def digests {pub : Public} {Out : Type} {P : Protocol pub Out} (hash : P.Item → Nat)
    (o : P.Object) : List (P.Item × Nat) :=
  (o.parts.filterMap Obj.item?).map (fun x => (x, hash x))

/-- Release guard: everything the candidate carries is already in the closure
of `seen`. -/
def releasable {pub : Public} {Out : Type} {P : Protocol pub Out} (seen : List P.Object)
    (c : P.Object) : Bool :=
  c.carried.all (fun x => decide (x ∈ closure seen))

/-- Slashing protection, generic over the protocol's `conflicts`: a candidate
signed by the own key `k` is refused if it conflicts with itself or, in either
order, with an object signed by `k` in the closure of `seen`. Other candidates
pass (engine candidates are own-signed or unsigned). -/
def protects {pub : Public} {Out : Type} (P : Protocol pub Out) (k : Key pub)
    (seen : List P.Object) (c : P.Object) : Bool :=
  if c.signer? = some k then
    !(P.conflicts c c) &&
      (closure seen).all fun o => o.signer? != some k || !(P.conflicts c o || P.conflicts o c)
  else true

/-- Release candidates in order, for the node with own key `k`: a candidate is
released if it is `releasable`, `protects` allows it and its dependencies are
held (`P.dependencies.ready` on the closure of `seen`); released objects join
`seen` at once, so later candidates of the same tick are checked against
them. -/
def releaseAll {pub : Public} {Out : Type} (P : Protocol pub Out) (hash : P.Item → Nat)
    (k : Key pub) : Node P → List P.Object → Node P × List P.Object
  | nd, [] => (nd, [])
  | nd, c :: cs =>
    if releasable nd.seen c && protects P k nd.seen c &&
        P.dependencies.ready (closure nd.seen) c then
      let nd' : Node P := ⟨P.recordOwn nd.st c (digests hash c), nd.seen ++ [c]⟩
      let r := releaseAll P hash k nd' cs
      (r.1, c :: r.2)
    else releaseAll P hash k nd cs

/-- The gossip candidates at time `t` in state `st`: unsigned. -/
def gossipCandidates {pub : Public} {Out : Type} (P : Protocol pub Out) (st : P.State)
    (t : Time) : List P.Object :=
  (P.gossip st t).map (fun mc => .mk .none mc.1 mc.2)

/-- The transactions of `submit` at node `v` at times `0, …, t`; the engine passes `Run.inbox`,
the submitted and the relayed ones. -/
def mempool (submit : V → Time → List Tx) (v : V) (t : Time) : List Tx :=
  if t < 0 then [] else (List.range (t.toNat + 1)).flatMap (fun k => submit v k)

namespace Run

variable (rho : Run F E)

/-- The own key of validator `v`. -/
def ownKey (v : V) : Fin (Fintype.card V) := rho.key.symm v

/-- The validator that signed an object, through the PKI. -/
def signerOf (o : (protoOf F E).Object) : Option V := o.signer?.map rho.key

/-- The initial world: every node starts in `init` of its own key, having
seen nothing. -/
def initWorld (v : V) : Node (protoOf F E) := ⟨(protoOf F E).init (rho.ownKey v), []⟩

/-- The ordered candidates of duty `d`, signed with the selected node's own key
in the duty's role. An unselected node produces no candidates. -/
def signedCandidate (v : V) (d : (protoOf F E).Duty) :
    List (Msg (protoOf F E).Item (protoOf F E).Body × List (protoOf F E).Object) →
      List (protoOf F E).Object := fun candidates =>
  if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
    candidates.map fun (m, cs) => .mk (.signed (rho.ownKey v) ((protoOf F E).role d)) m cs
  else []

/-- One selected duty of node `v`: `act`'s state is applied, then its candidates
are released in order. An unselected duty does not execute or mutate state. -/
def dutyStep (v : V) (nd : Node (protoOf F E)) (d : (protoOf F E).Duty) :
    Node (protoOf F E) × List (protoOf F E).Object :=
  if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
    let a := (protoOf F E).act nd.st d
    releaseAll (protoOf F E) rho.hash (rho.ownKey v) ⟨a.1, nd.seen⟩ (rho.signedCandidate v d a.2)
  else (nd, [])

/-- The duties `ds` of node `v`, one after the other, in order, from node
`nd`: the final node and what the duties released, in order. -/
def runDuties (v : V) (nd : Node (protoOf F E)) (ds : List (protoOf F E).Duty) :
    Node (protoOf F E) × List (protoOf F E).Object :=
  ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2)) (nd, [])

/-- A tick: the clock (with the node's mempool), then, if awake, the due duties
in order, then gossip from the final state. -/
def tick (nd : Node (protoOf F E)) (v : V) (t : Time) :
    Node (protoOf F E) × List (protoOf F E).Object :=
  let nd₁ : Node (protoOf F E) := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
  if E.awake v t then
    let r := rho.runDuties v nd₁ ((protoOf F E).duties t)
    let g := releaseAll (protoOf F E) rho.hash (rho.ownKey v) r.1
      (gossipCandidates (protoOf F E) r.1.st t)
    (g.1, r.2 ++ g.2)
  else (nd₁, [])

/-- A raw arrival of `o` to node `v` at `t`: `process` and the `seen` entry, then
the delivery duties in order, then gossip from the final state. No awake test:
the conditions deliver only to awake nodes (`ExecutionValid.deliver_awake`).
No dependency test: the protocol owns buffering and admission. -/
def deliver (nd : Node (protoOf F E)) (v : V) (o : (protoOf F E).Object) (t : Time) :
    Node (protoOf F E) × List (protoOf F E).Object :=
  let nd₁ : Node (protoOf F E) :=
    ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
  let r := rho.runDuties v nd₁ ((protoOf F E).deliverDuties t)
  let g := releaseAll (protoOf F E) rho.hash (rho.ownKey v) r.1
    (gossipCandidates (protoOf F E) r.1.st t)
  (g.1, r.2 ++ g.2)

/-- One event. -/
def step (w : V → Node (protoOf F E)) : Event V (protoOf F E).Object → V → Node (protoOf F E)
  | .tick v t => Function.update w v (rho.tick (w v) v t).1
  | .deliver v o t => Function.update w v (rho.deliver (w v) v o t).1
  | .restart v t =>
      Function.update w v
        ⟨(protoOf F E).restore (rho.ownKey v) ((protoOf F E).durable (w v).st) t, (w v).seen⟩

/-- The world before event `i` (event cut `i`). -/
def stateBefore (i : Nat) : V → Node (protoOf F E) :=
  (rho.events.take i).foldl rho.step rho.initWorld

/-- The objects released by the event at index `i`: by its tick or its
delivery (a restart releases nothing). -/
def releasesAt (i : Nat) : List (protoOf F E).Object :=
  match rho.events[i]? with
  | some (.tick v t) => (rho.tick (rho.stateBefore i v) v t).2
  | some (.deliver v o t) => (rho.deliver (rho.stateBefore i v) v o t).2
  | _ => []

/-- Event `i` is a sending event of node `v` at `t`: its tick at `t`, or a
delivery to it at `t`. -/
def SendsAt (v : V) (i : Nat) (t : Time) : Prop :=
  rho.events[i]? = some (Event.tick v t) ∨
    ∃ o : (protoOf F E).Object, rho.events[i]? = some (Event.deliver v o t)

/-- Node `v` released `o` at `t`: at its tick at `t` or at a delivery to it at
`t`. The send time is the event's own time. -/
def releases (v : V) (o : (protoOf F E).Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.SendsAt v i t ∧ o ∈ rho.releasesAt i

/-- Node `v` received `o` at `t`. -/
def receives (v : V) (o : (protoOf F E).Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (Event.deliver v o t)

/-- What node `v` has seen before event cut `i`: the closure of its `seen`
log, i.e. every object it released or received before the cut, with everything
those objects carry (`Run.mem_viewIdx_iff`). -/
def ViewIdx (v : V) (i : Nat) : Set (protoOf F E).Object :=
  {o | o ∈ closure (rho.stateBefore i v).seen}

/-- Everything the honest nodes saw in the run. -/
def Observed : Set (protoOf F E).Object :=
  {o | ∃ v ∈ rho.honest, o ∈ rho.ViewIdx v rho.events.length}

/-- The time of event cut `i`: the time of its last event (`0` for the empty
cut). -/
def cutTime (i : Nat) : Time :=
  match i with
  | 0 => 0
  | k + 1 => match rho.events[k]? with
    | some e => e.time
    | none => 0

/-- Output `g` of node `v` at event cut `i`. -/
def readIdx (g : O.Id) (v : V) (i : Nat) : Ledger :=
  (protoOf F E).out g (rho.stateBefore i v).st

end Run

end Consensus.Model

end
