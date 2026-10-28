module
public import Mathlib.Logic.Encodable.Basic
public import ConsensusProblem.Basic
public import ConsensusModel.Objects

@[expose] public section

/-! # The protocol interface (layer ½)

What a protocol supplies to the execution model: its types, the sizes of its
committees, a state machine, its output ledgers (one per output identifier
of its schema), and its slashing rule.
There is no slot, proposer or block here: a proposer is a label with one seat
whose duty acts at the proposal time, and blocks are items of the protocol.

The protocol knows only the public parameters `n` and `Δ`. It does not know the
GST, the honest set, the awake profile, the seat assignment, the submission
or relay functions, or the hash function: the engine gives it its own and relayed
transactions (at its ticks) and the digests of the items it receives or signs. -/

namespace Consensus.Model

/-- The public parameters that honest code may depend on. -/
structure Public where
  n : Nat
  Δ : Time
  Δ_pos : 0 < Δ

/-- A protocol for public parameters `pub`, with output identifiers `Out`. -/
structure Protocol (pub : Public) (Out : Type) : Type 1 where
  State : Type
  /-- Signing labels; label `ℓ` has `seats ℓ` seats. -/
  Label : Type
  /-- Duties: each signs with its label, at its act time. -/
  Duty : Type
  /-- Items: what the engine hashes (for example block headers). -/
  Item : Type
  /-- Protocol data. -/
  Body : Type
  /-- What a restart keeps. -/
  Durable : Type
  decLabel : DecidableEq Label
  decItem : DecidableEq Item
  decBody : DecidableEq Body
  encItem : Encodable Item
  seats : Label → Nat
  /-- A label has at most `n` seats, so that seats can be held by distinct
  validators. -/
  seats_le : ∀ ℓ, seats ℓ ≤ pub.n
  label : Duty → Label
  actTime : Duty → Time
  /-- The duties due at a time, each once, in the order the engine signs them. -/
  duties : Time → List Duty
  duties_spec : ∀ d t, d ∈ duties t ↔ actTime d = t
  duties_nodup : ∀ t, (duties t).Nodup
  init : State
  /-- The clock update at a tick, with the node's cumulative own and relayed transactions
  so far. -/
  clock : State → Time → List Tx → State
  /-- What every seat of duty `d` signs: a message and carried objects. -/
  act : State → Duty → Option (Msg Item Body × List (Obj Label seats Item Body))
  /-- Unsigned objects. Relay of received objects is done here, by carrying
  them. -/
  gossip : State → Time → List (Body × List (Obj Label seats Item Body))
  /-- Processing a delivered object, with the digests of the items it
  contains. Total: any object, at any time. -/
  process : State → Obj Label seats Item Body → List (Item × Nat) → State
  /-- Recording an object the node has just signed, with the digests of the
  items it contains. -/
  recordOwn : State → Obj Label seats Item Body → List (Item × Nat) → State
  durable : State → Durable
  restore : Durable → Time → State
  /-- The output ledgers, one per output identifier. -/
  out : Out → State → Ledger
  /-- The slashing rule: two objects that, signed by one validator, convict
  it. -/
  conflicts : Obj Label seats Item Body → Obj Label seats Item Body → Bool

attribute [instance] Protocol.decLabel Protocol.decItem Protocol.decBody Protocol.encItem

/-- Wire objects of a protocol. -/
abbrev Protocol.Object {pub : Public} {Out : Type} (P : Protocol pub Out) : Type :=
  Obj P.Label P.seats P.Item P.Body

/-- A protocol for every choice of the public parameters, with the outputs of
schema `O`. -/
abbrev Family (O : OutputSchema) := (pub : Public) → Protocol pub O.Id

end Consensus.Model

end
