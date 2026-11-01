module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import AvailableChainModel.Objects.Seats
public import AvailableChainModel.Generic.Env

@[expose] public section

namespace AvailableChain.Generic

/-- A scheduler event at a node: its local clock tick, or the delivery of one object. -/
inductive Event (V Object : Type) where
  | tick (v : V) (t : Time)
  | deliver (v : V) (object : Object) (t : Time)
  deriving DecidableEq

namespace Event
variable {V Object : Type}
def time : Event V Object → Time
  | .tick _ t => t
  | .deliver _ _ t => t
def node : Event V Object → V
  | .tick v _ => v
  | .deliver v _ _ => v
def object? : Event V Object → Option Object
  | .tick _ _ => none
  | .deliver _ object _ => some object
def phase : Event V Object → Nat
  | .tick _ _ => 0
  | .deliver _ _ _ => 1
/-- Event order is lexicographic by time and phase. Ticks therefore precede
deliveries at the same time; equal-phase deliveries keep their list order. -/
def key (e : Event V Object) : Lex (Time × Nat) := toLex (e.time, e.phase)
end Event

/-- A committee protocol with `n` seats per label.

The type mentions no validator, so honest code has no identity, no key, and
one shared initial state. Honest code decides payloads; the engine signs them
(`Run.emittedAt`). The state changes only through `clock` and `process`:
emitting never changes the state, and a node receives its own objects only by
delivery. So a node does not know its seats, and it can use only what a node
that was not sampled can also compute. -/
structure ProtocolSpec (n : Nat) where
  State : Type
  /-- Duty labels. Every label has its own committee of `n` seats. -/
  Label : Type
  /-- What honest code sends. A payload can carry signed objects. -/
  Payload : Type
  init : State
  /-- The local clock update, at every tick, awake or asleep. -/
  clock : State → Time → State
  /-- The act time of a label. A seat of the label signs only at this time.
  Duties at the same instant can share one label and one payload. -/
  actTime : Label → Time
  /-- The labels due at a time: those with that act time, each once. -/
  duties : Time → List Label
  duties_spec : ∀ ℓ t, ℓ ∈ duties t ↔ actTime ℓ = t
  duties_nodup : ∀ t, (duties t).Nodup
  /-- The payload of every seat of label `ℓ` in this state. It does not
  depend on the seat. -/
  act : State → Label → Option Payload
  /-- The proposal schedule. The proposer of a slot is run data. -/
  proposalTime : Slot → Time
  /-- The slots whose proposal time is a time, each once. -/
  slotsAt : Time → List Slot
  slotsAt_spec : ∀ s t, s ∈ slotsAt t ↔ proposalTime s = t
  slotsAt_nodup : ∀ t, (slotsAt t).Nodup
  /-- The proposal payload of the proposer of slot `s` in this state. -/
  propose : State → Slot → Option Payload
  /-- Unsigned payloads at a tick. Any node, sampled or not, can send them. -/
  gossip : State → Time → List Payload
  /-- How a node processes a delivered object. -/
  process : State → Signed Label n Payload → State
  /-- Syntactic well-formedness of an object on the wire. -/
  wellFormed : Signed Label n Payload → Bool
  /-- The node's state holds what the object depends on (e.g. the parent block). -/
  depsPresent : State → Signed Label n Payload → Bool
  /-- The node's state already holds the object. -/
  processed : State → Signed Label n Payload → Bool
  /-- The node's state excludes the object for good: the node rejects it now and
  in every later state. Delivery obligations do not apply to excluded objects. -/
  excludes : State → Signed Label n Payload → Bool
  /-- In state `s`, the delivery of the first object makes the node handle the
  second (the object itself, or one carried inside it). `handles` is the
  handler-call gate; it can hold even when the object is rejected. -/
  handles : State → Signed Label n Payload → Signed Label n Payload → Prop
  /-- Structural containment, with the containing object first. -/
  carries : Signed Label n Payload → Signed Label n Payload → Prop

/-- Wire objects of a protocol. -/
abbrev ProtocolSpec.Object {n : Nat} (P : ProtocolSpec n) : Type :=
  Signed P.Label n P.Payload

/-- Every node's local state. -/
abbrev World (V : Type) {n : Nat} (P : ProtocolSpec n) := V → P.State

namespace World
variable {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
def init : World V P := fun _ => P.init
/-- A tick runs the clock; a delivery runs `process`. Emission does not
change the state. -/
def step (w : World V P) : Event V P.Object → World V P
  | .tick v t => Function.update w v (P.clock (w v) t)
  | .deliver v o _ => Function.update w v (P.process (w v) o)
end World

/-- A run: the honest set, the horizon, the event list, and the hidden
assignments. `seatOf ℓ` is a fresh bijection from the seats of label `ℓ` to
validators; `proposerOf s` is the proposer of slot `s`. Claims quantify over
all runs, so over all assignments. -/
structure Run (V : Type) {n : Nat} (P : ProtocolSpec n) where
  honest : Finset V
  horizon : Time
  events : List (Event V P.Object)
  seatOf : P.Label → Fin n ≃ V
  proposerOf : Slot → V

namespace Run
variable {V : Type} [DecidableEq V] {n : Nat} (P : ProtocolSpec n)
/-- Events before index `i` have been folded into the returned world. -/
def stateBefore (rho : Run V P) (i : Nat) : World V P :=
  (rho.events.take i).foldl World.step World.init
/-- The returned world includes events strictly before time `t`. -/
def stateBeforeTime (rho : Run V P) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time < t))).foldl World.step World.init
/-- The returned world includes events up to and including time `t`. -/
def readAt (rho : Run V P) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldl World.step World.init
/-- The returned world includes the complete event list. -/
def final (rho : Run V P) : World V P :=
  rho.events.foldl World.step World.init

/-- The objects that the tick of `v` at index `i` and time `t` emits, from the
state after its clock update. An asleep node emits nothing. An awake node
signs, with its own seat of each due label, the label's payload; with the
proposer key of each of its slots due now, the proposal payload; and nothing
else but unsigned gossip. -/
def emittedAt (E : Env V) (rho : Run V P) (i : Nat) (v : V) (t : Time) :
    List P.Object :=
  if E.awake v t then
    let st := P.clock (stateBefore P rho i v) t
    (P.duties t).filterMap (fun ℓ =>
        (P.act st ℓ).map (fun p => ⟨.seat ℓ ((rho.seatOf ℓ).symm v), p⟩)) ++
      (P.slotsAt t).filterMap (fun s =>
        if rho.proposerOf s = v then
          (P.propose st s).map (fun p => ⟨.proposer s, p⟩)
        else none) ++
      (P.gossip st t).map (fun p => ⟨.none, p⟩)
  else []

/-- Payloads from delivery events only; self-emitted objects are not included. -/
def objects (rho : Run V P) : List P.Object := rho.events.filterMap Event.object?
/-- An object appears in a tick's output. -/
def emits (E : Env V) (rho : Run V P) (v : V) (o : P.Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧ o ∈ emittedAt P E rho i v t

/-- A delivery of the object to the node. Delivery records the handler call
even when the handler rejects; carried children are covered by
`UnforgeableSignatures.carried` and `handlesAt`. -/
def processes (rho : Run V P) (v : V) (o : P.Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.deliver v o t)

/-- The handler call recorded at index `i`. A handler call may reject the object;
the false-to-true `processed` transition belongs to `acceptsAt`. -/
def handlesAt (rho : Run V P) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  ∃ o', rho.events[i]? = some (.deliver v o' t) ∧
    P.handles (stateBefore P rho i v) o' o

/-- An accepted call is a handler call that flips `processed` from `false` to
`true`. -/
def acceptsAt (rho : Run V P) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  handlesAt P rho i v o t ∧ P.processed (stateBefore P rho i v) o = false ∧
    P.processed (stateBefore P rho (i + 1) v) o = true

/-- The validator that holds an authentication in this run, if any. -/
def holder (rho : Run V P) : Auth P.Label n → Option V
  | .seat ℓ i => some (rho.seatOf ℓ i)
  | .proposer s => some (rho.proposerOf s)
  | .none => none
end Run
end AvailableChain.Generic

end
