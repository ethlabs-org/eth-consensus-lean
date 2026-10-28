module
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Fintype.Card
public import ConsensusProblem.Basic
public import ConsensusModel.Objects

@[expose] public section

/-! # The protocol interface (layer ½)

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

/-- Closed selection syntax: everybody, a fixed public set of keys, or some
set of `m` keys (all keys if `m ≥ n`) chosen by the run. The run picks one
admissible set per role. -/
inductive SelSpec (n : Nat) where
  | all
  | fixed (S : Finset (Fin n))
  | sized (m : Nat)

namespace SelSpec

variable {n : Nat}

/-- `S` is an admissible selection for the specification. -/
def Admits : SelSpec n → Finset (Fin n) → Prop
  | .all, S => S = Finset.univ
  | .fixed T, S => S = T
  | .sized m, S => S.card = min m n

/-- Every specification admits some selection. -/
theorem admits_exists (s : SelSpec n) : ∃ S, s.Admits S := by
  cases s with
  | all => exact ⟨Finset.univ, rfl⟩
  | fixed T => exact ⟨T, rfl⟩
  | sized m =>
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := min m n)
      (by simp [Finset.card_univ, Fintype.card_fin])
    exact ⟨S, hS⟩

/-- Under a positive population, the selection of `.all` is nonempty. -/
theorem admits_all_nonempty {S : Finset (Fin n)} (hn : 0 < n)
    (h : (SelSpec.all : SelSpec n).Admits S) : S.Nonempty := by
  change S = Finset.univ at h
  subst h
  exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The selection of `.fixed T` is nonempty when `T` is. -/
theorem admits_fixed_nonempty {S T : Finset (Fin n)} (hT : T.Nonempty)
    (h : (SelSpec.fixed T).Admits S) : S.Nonempty := by
  change S = T at h
  exact h ▸ hT

/-- Under a positive population, the selection of `.sized m` with `m > 0` is
nonempty. -/
theorem admits_sized_nonempty {S : Finset (Fin n)} {m : Nat} (hn : 0 < n) (hm : 0 < m)
    (h : (SelSpec.sized m).Admits S) : S.Nonempty := by
  change S.card = min m n at h
  apply Finset.card_pos.mp
  rw [h]
  exact lt_min hm hn

end SelSpec

/-- A protocol for public parameters `pub`, with output identifiers `Out`. -/
structure Protocol (pub : Public) (Out : Type) : Type 1 where
  State : Type
  /-- Signing roles. A signature binds its role. -/
  Role : Type
  /-- Duties: each signs in its role, at its act time. -/
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
  encItem : Encodable Item
  /-- Who may act in each role: public, closed syntax; the run picks an
  admissible set of keys. -/
  selSpec : Role → SelSpec pub.n
  role : Duty → Role
  actTime : Duty → Time
  /-- The duties due at a time, each once, in the order the engine signs them. -/
  duties : Time → List Duty
  duties_spec : ∀ d t, d ∈ duties t ↔ actTime d = t
  duties_nodup : ∀ t, (duties t).Nodup
  /-- The initial state of the node with the given key. -/
  init : Key pub → State
  /-- The clock update at a tick, with the node's cumulative own and relayed transactions
  so far. -/
  clock : State → Time → List Tx → State
  /-- What the node signs for duty `d` (if selected for its role): a message
  and carried objects. -/
  act : State → Duty → Option (Msg Item Body × List (Obj pub.n Role Item Body))
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

attribute [instance] Protocol.decRole Protocol.decItem Protocol.decBody Protocol.encItem

/-- Wire objects of a protocol. -/
abbrev Protocol.Object {pub : Public} {Out : Type} (P : Protocol pub Out) : Type :=
  Obj pub.n P.Role P.Item P.Body

/-- A protocol for every choice of the public parameters, with the outputs of
schema `O`. -/
abbrev Family (O : OutputSchema) := (pub : Public) → Protocol pub O.Id

end Consensus.Model

end
