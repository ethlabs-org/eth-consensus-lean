module
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Fintype.Card
public import ConsensusLean.Spec.Problem.Basic
public import ConsensusLean.Spec.Model.Objects

@[expose] public section

/-! # The protocol interface (L1)

What a protocol supplies to the execution model: its types, who may act in
each role (closed selection syntax), a state machine, its output ledgers (one
per output identifier of its schema), and its slashing rule. There is no slot,
proposer or block here: a proposer is a role whose selection has one key and
whose duty acts at the proposal time, and blocks are items of the protocol.

Honest code knows only the public parameters `n` and `Δ`, and its own key
(`init` and `restore` receive it). It never sees the selection, the PKI, the
honest set, the GST, the awake profile, the submission or relay functions, or
the hash function: the engine gives it its own and relayed transactions (at its
ticks) and the digests of the items it receives or signs. It learns its own
selection only by acting: dispatch is engine-side (a duty's message is signed
only if the node's key is selected for the duty's role). Hiding the selection
from honest code buys nothing against the static, all-knowing adversary, and
the model does not attempt it. -/

namespace Consensus.Model

/-- The public parameters that honest code may depend on. -/
structure Public where
  n : Nat
  Δ : Time
  Δ_pos : 0 < Δ

/-- Validator keys: the public key space `Fin n`. The run's PKI maps keys to
validators. -/
abbrev Key (pub : Public) := Fin pub.n

/-- Closed selection syntax: a fixed public set of keys (everybody is
`.fixed univ`), or some set of `m` keys (all keys if `m ≥ n`) chosen by the
run. The run picks one admissible set per role. -/
inductive SelSpec (n : Nat) where
  | fixed (S : Finset (Fin n))
  | sized (m : Nat)

namespace SelSpec

variable {n : Nat}

/-- `S` is an admissible selection for the specification. -/
def Admits : SelSpec n → Finset (Fin n) → Prop
  | .fixed T, S => S = T
  | .sized m, S => S.card = min m n

end SelSpec

/-- A protocol for public parameters `pub`, with output identifiers `Out`. -/
structure Protocol (pub : Public) (Out : Type) : Type 1 where
  State : Type
  /-- Signing roles. A signature binds its role. -/
  Role : Type
  /-- Duties: each signs in its role, at the times `duties` lists it. -/
  Duty : Type
  /-- Items: what the engine hashes (for example block headers). -/
  Item : Type
  /-- Protocol data. -/
  Body : Type
  /-- What a restart keeps. -/
  Durable : Type
  decRole : DecidableEq Role
  decItem : DecidableEq Item
  decBody : DecidableEq Body
  /-- Items are countable, so an injective hash exists. -/
  cntItem : Countable Item
  /-- Who may act in each role: public, closed syntax; the run picks an
  admissible set of keys. -/
  selSpec : Role → SelSpec pub.n
  role : Duty → Role
  /-- The duties due at a time, in the order the engine runs them (one after
  the other, each from the state the previous one left). -/
  duties : Time → List Duty
  /-- The initial state of the node with the given key. -/
  init : Key pub → State
  /-- The clock update at a tick, with the node's cumulative own and relayed transactions
  so far. -/
  clock : State → Time → List Tx → State
  /-- Duty `d`: the new state, and what the node signs for the duty (if selected
  for its role): a message and carried objects. On an awake tick, when the duty
  runs, the engine applies the state whether or not the node is selected and
  whether or not the message is released. `act` gets no selection or
  release-result argument and no failure feedback, so the state it returns
  cannot depend on selection or refusal; a later duty (also within the tick)
  learns of a successful release only through `recordOwn`. A purely local
  step returns `none`. -/
  act : State → Duty → State × Option (Msg Item Body × List (Obj pub.n Role Item Body))
  /-- Unsigned objects (items allowed). Relay of received objects is done here,
  by carrying them. -/
  gossip : State → Time → List (Msg Item Body × List (Obj pub.n Role Item Body))
  /-- Processing a delivered object, with the digests of the items it
  contains. Total: any object, at any time. -/
  process : State → Obj pub.n Role Item Body → List (Item × Nat) → State
  /-- Recording an object the node has just released, with the digests of the
  items it contains. -/
  recordOwn : State → Obj pub.n Role Item Body → List (Item × Nat) → State
  durable : State → Durable
  /-- The state after a restart of the node with the given key, from what it
  kept, at the restart time. -/
  restore : Key pub → Durable → Time → State
  /-- The output ledgers, one per output identifier. -/
  out : Out → State → Ledger
  /-- The slashing rule: two objects that, signed by one validator, convict
  it. -/
  conflicts : Obj pub.n Role Item Body → Obj pub.n Role Item Body → Bool

attribute [instance] Protocol.decRole Protocol.decItem Protocol.decBody Protocol.cntItem

/-- `sel` is an admissible selection of `P`: admissible for every role. -/
def Protocol.SelAdmits {pub : Public} {Out : Type} (P : Protocol pub Out)
    (sel : P.Role → Finset (Fin pub.n)) : Prop :=
  ∀ r, (P.selSpec r).Admits (sel r)

/-- Wire objects of a protocol. -/
abbrev Protocol.Object {pub : Public} {Out : Type} (P : Protocol pub Out) : Type :=
  Obj pub.n P.Role P.Item P.Body

/-- A protocol for every choice of the public parameters, with the outputs of
schema `O`. -/
abbrev Family (O : OutputSchema) := (pub : Public) → Protocol pub O.Id

end Consensus.Model

end
