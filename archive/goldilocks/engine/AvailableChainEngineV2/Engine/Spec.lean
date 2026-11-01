module
public import AvailableChainModel.Objects.Time
public import AvailableChainEngineV2.Engine.Objects

@[expose] public section

namespace AvailableChain.V2

open AvailableChain

/-- A protocol for engine v2 (design §2 E1, E2, E5, E6).

`In` is the type of the run-chosen input (for example a transaction list). It
is a parameter, not a field, so a protocol cannot choose it: the claim domain
fixes it. The run gives an input to every validator at every time
(`Run.input`); `act` reads it.

The type mentions no validator, so honest code has no identity, no key, and
one shared initial state. Honest code decides payloads; the engine signs them
(`tick`). The state changes only through `clock`, `recordOwn` (at a tick),
`process` (at a delivery) and `restore` (at a restart). A node does not know
its seats, and it can use only what a node that holds no seat can also
compute. -/
structure ProtocolSpec (In : Type) where
  State : Type
  /-- Duty labels. A proposal duty is a label with one seat. -/
  Label : Type
  /-- The committee size of every label (design §2 E2). There is no global
  committee size. -/
  seats : Label → Nat
  /-- What honest code sends. A payload can carry signed objects. -/
  Payload : Type
  /-- The data that survives a restart (design §2 E6). -/
  Durable : Type
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
  /-- The payload of every seat of label `ℓ` in this state, for this input. It
  does not depend on the seat. -/
  act : State → Label → In → Option Payload
  /-- Unsigned payloads at a tick. Any node, with seats or not, can send them. -/
  gossip : State → Time → List Payload
  /-- How a node processes a delivered object. -/
  process : State → Signed Label seats Payload → State
  /-- `selfVisible` controls the private own-signature record. A normal
  delivery to the emitting node may occur at the emission timestamp, after
  the tick phase. -/
  selfVisible : Label → Bool
  /-- The private own-signature record: at its tick, a node records every
  object that it signs with a self-visible label (design §2 E5). -/
  recordOwn : State → Signed Label seats Payload → State
  /-- The part of the state that a restart keeps. -/
  durable : State → Durable
  /-- The state after a restart, from the kept part. -/
  restore : Durable → Time → State
  /-- Syntactic well-formedness of an object on the wire. -/
  wellFormed : Signed Label seats Payload → Bool
  /-- The node's state holds what the object depends on (e.g. the parent block). -/
  depsPresent : State → Signed Label seats Payload → Bool
  /-- The node's state already holds the object. -/
  processed : State → Signed Label seats Payload → Bool
  /-- The node's state excludes the object for good: the node rejects it now and
  in every later state of the same restart epoch. Delivery obligations do not
  apply to excluded objects. -/
  excludes : State → Signed Label seats Payload → Bool
  /-- In state `s`, the delivery of the first object makes the node handle the
  second (the object itself, or one carried inside it). `handles` is the
  handler-call gate; it can hold even when the object is rejected. -/
  handles : State → Signed Label seats Payload → Signed Label seats Payload → Prop
  /-- Structural containment, with the containing object first. -/
  carries : Signed Label seats Payload → Signed Label seats Payload → Prop

namespace ProtocolSpec

variable {In : Type}

/-- Wire objects of a protocol. -/
abbrev Object (P : ProtocolSpec In) : Type :=
  Signed P.Label P.seats P.Payload

/-- An object goes into the own-signature record: its label is self-visible.
Unsigned objects never do. -/
def objSelfVisible (P : ProtocolSpec In) (o : P.Object) : Bool :=
  match o.auth with
  | .seat ℓ _ => P.selfVisible ℓ
  | .none => false

end ProtocolSpec

end AvailableChain.V2

end
