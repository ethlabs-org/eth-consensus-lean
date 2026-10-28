module
public import Mathlib.Data.Fintype.Card
public import ConsensusModel.Protocol

@[expose] public section

/-! # Runs and the engine (layer ½)

A run fixes everything the protocol does not choose: the honest set, the
horizon, the scheduler's events, the holder of every seat, the transactions
submitted to every node, and the hash function. The engine runs the protocol on
the events. Per node it keeps the protocol state and the `seen` log of every
object the node released or received.

At a tick of awake node `v` at `t`, the engine
1. runs `clock` with `v`'s own and relayed transactions up to `t` (its mempool);
2. builds the candidates from that state: for every due duty, in order, and
   every seat of its label that `v` holds, the duty's message signed with that
   seat; then unsigned gossip;
3. releases a candidate only if every object it carries is already in the
   closure of `seen` (so honest code passes on no object it has not seen), adds
   it to `seen`, and records it with `recordOwn`.
At a delivery it runs `process`; at a restart, `restore ∘ durable`, keeping
`seen`. Only the engine evaluates the hash: with every object processed or
recorded it passes the digests of the items in the object's closure. -/

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
def pubOf {V : Type} [Fintype V] (E : Env V) : Public := ⟨Fintype.card V, E.Δ, E.Δ_pos⟩

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The protocol that family `F` runs in environment `E`. -/
abbrev protoOf (F : Family) (E : Env V) : Protocol (pubOf E) := F (pubOf E)

/-- A run of family `F` in environment `E`. -/
structure Run (F : Family) (E : Env V) where
  honest : Finset V
  horizon : Time
  events : List (Event V (protoOf F E).Object)
  /-- The validator holding every seat. Within one label, distinct seats are
  held by distinct validators (an embedding), so a quorum of seats is a quorum
  of distinct validators; a full committee is a bijection automatically. -/
  holder : (ℓ : (protoOf F E).Label) → Fin ((protoOf F E).seats ℓ) ↪ V
  /-- The transactions submitted to every node at every time. -/
  submit : V → Time → List Tx
  /-- Transactions relayed by the network, chosen by the scheduler. -/
  relay : V → Time → List Tx
  /-- The hash function: arbitrary, possibly with collisions; evaluated only by
  the engine. -/
  hash : (protoOf F E).Item → Nat

variable {F : Family} {E : Env V}

/-- The environment point of a run. -/
def Run.point (rho : Run F E) : EnvPoint V := ⟨E, rho.honest, rho.horizon, rho.submit⟩

/-- Own submissions and network ingress are indistinguishable to honest code. -/
def Run.inbox (rho : Run F E) (v : V) (t : Time) : List Tx :=
  rho.submit v t ++ rho.relay v t

/-- An engine node: the protocol state and the `seen` log. -/
structure Node {pub : Public} (P : Protocol pub) where
  st : P.State
  seen : List P.Object

/-- The initial world. -/
def initWorld (F : Family) (E : Env V) : V → Node (protoOf F E) :=
  fun _ => ⟨(protoOf F E).init, []⟩

/-- The closure of a list of objects: the objects and everything they carry. -/
def closure {pub : Public} {P : Protocol pub} (l : List P.Object) : List P.Object :=
  l.flatMap Obj.parts

/-- The digests the engine passes with object `o`: every item in its closure. -/
def digests {pub : Public} {P : Protocol pub} (hash : P.Item → Nat) (o : P.Object) :
    List (P.Item × Nat) :=
  (o.parts.filterMap Obj.item?).map (fun x => (x, hash x))

/-- Release candidates in order: a candidate is released if everything it
carries is in the closure of `seen`; released objects join `seen` at once. -/
def releaseAll {pub : Public} {P : Protocol pub} (hash : P.Item → Nat) :
    Node P → List P.Object → Node P × List P.Object
  | nd, [] => (nd, [])
  | nd, c :: cs =>
    if c.carried.all (fun x => decide (x ∈ closure nd.seen)) then
      let nd' : Node P := ⟨P.recordOwn nd.st c (digests hash c), nd.seen ++ [c]⟩
      let r := releaseAll hash nd' cs
      (r.1, c :: r.2)
    else releaseAll hash nd cs

/-- The transactions submitted to node `v` at times `0, …, t`. -/
def mempool (submit : V → Time → List Tx) (v : V) (t : Time) : List Tx :=
  if t < 0 then [] else (List.range (t.toNat + 1)).flatMap (fun k => submit v k)

namespace Run

variable (rho : Run F E)

/-- The seats of label `ℓ` that `v` holds. -/
def ownSeats (ℓ : (protoOf F E).Label) (v : V) : List (Fin ((protoOf F E).seats ℓ)) :=
  (List.finRange _).filter (fun i => decide (rho.holder ℓ i = v))

/-- The candidates of node `v` at time `t` in state `st`. -/
def candidates (st : (protoOf F E).State) (v : V) (t : Time) :
    List (protoOf F E).Object :=
  let P := protoOf F E
  ((P.duties t).flatMap (fun d =>
    match P.act st d with
    | some (m, cs) => (rho.ownSeats (P.label d) v).map (fun i => .mk (.signed (P.label d) i) m cs)
    | none => [])) ++
  (P.gossip st t).map (fun bc => .mk .none (.data bc.1) bc.2)

/-- A tick: the clock (with the node's mempool), then, if awake, signing and
release. -/
def tick (nd : Node (protoOf F E)) (v : V) (t : Time) :
    Node (protoOf F E) × List (protoOf F E).Object :=
  let nd₁ : Node (protoOf F E) := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
  if E.awake v t then releaseAll rho.hash nd₁ (rho.candidates nd₁.st v t) else (nd₁, [])

/-- One event. -/
def step (w : V → Node (protoOf F E)) : Event V (protoOf F E).Object → V → Node (protoOf F E)
  | .tick v t => Function.update w v (rho.tick (w v) v t).1
  | .deliver v o _ =>
      Function.update w v ⟨(protoOf F E).process (w v).st o (digests rho.hash o), (w v).seen ++ [o]⟩
  | .restart v t =>
      Function.update w v
        ⟨(protoOf F E).restore ((protoOf F E).durable (w v).st) t, (w v).seen⟩

/-- The world before event `i` (event cut `i`). -/
def stateBefore (i : Nat) : V → Node (protoOf F E) :=
  (rho.events.take i).foldl rho.step (initWorld F E)

/-- The objects released by the tick at index `i`. -/
def releasesAt (i : Nat) : List (protoOf F E).Object :=
  match rho.events[i]? with
  | some (.tick v t) => (rho.tick (rho.stateBefore i v) v t).2
  | _ => []

/-- Node `v` released `o` at its tick at `t`. -/
def releases (v : V) (o : (protoOf F E).Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (Event.tick v t) ∧ o ∈ rho.releasesAt i

/-- Node `v` received `o` at `t`. -/
def receives (v : V) (o : (protoOf F E).Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (Event.deliver v o t)

/-- What node `v` has seen before event cut `i`: every object it released or
received at an event with index `< i`, with everything those objects carry. -/
def ViewIdx (v : V) (i : Nat) : Set (protoOf F E).Object :=
  {o | ∃ k o₀, k < i ∧
    ((∃ t, rho.events[k]? = some (Event.tick v t) ∧ o₀ ∈ rho.releasesAt k) ∨
      ∃ t, rho.events[k]? = some (Event.deliver v o₀ t)) ∧ Obj.Contains o₀ o}

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

/-- The validator that holds an authentication. -/
def holderOf : Auth (protoOf F E).Label (protoOf F E).seats → Option V
  | .signed ℓ i => some (rho.holder ℓ i)
  | .none => none

/-- Output `g` of node `v` at event cut `i`. -/
def readIdx (g : Out) (v : V) (i : Nat) : Ledger :=
  (protoOf F E).out g (rho.stateBefore i v).st

end Run

end Consensus.Model

end
