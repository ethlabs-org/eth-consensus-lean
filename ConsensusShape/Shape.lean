module
public import ConsensusBlocks
public import ConsensusModel

@[expose] public section

/-! # Chain shapes (L2)

A chain shape is a protocol written over the building blocks: a public
skeleton (time grid, proposer selection, poll selection, committee kinds with
their phases and selections) and a state machine that proposes headers,
signs committee and poll messages, gossips, processes, and reads chains. The
engine-facing protocol is `compile` (next module); everything here is public
syntax that a reviewer reads once for every protocol.

Proposals come in two forms (D-25): a slot proposal (role `.proposer s`,
released at the slot's time, at position `s`), and a poll proposal (role
`.poll`, released at a unit tick the protocol chooses locally, at a position
it chooses, for example a height). In both the engine writes the payload
(`input`). Committee duties sign in role `.duty s k` (slot and kind). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg)

/-- Public block choices of a shape (D-15, D-21, D-25): the time grid, one
proposer selection for every slot, the poll selection (`.fixed ∅` disables
polling), and a finite list of committee kinds, each with a phase (its
`Δ`-offset within the slot) and a selection. -/
structure Skeleton (n : Nat) : Type 1 where
  /-- The time grid. -/
  grid : TimeGrid
  /-- Who may propose at a slot (the same specification for every slot). -/
  proposerSel : SelSpec n
  /-- Who may sign in the poll role; `.fixed ∅` disables polling. -/
  pollSel : SelSpec n
  /-- Committee kinds. -/
  Kind : Type
  decKind : DecidableEq Kind
  /-- Every kind, once, in the order the engine signs their duties. -/
  kinds : List Kind
  kinds_nodup : kinds.Nodup
  kinds_complete : ∀ k, k ∈ kinds
  /-- The `Δ`-offset of the kind's duty from the slot start (not required to
  be below `slotDeltas`: a kind may act in a later slot's interval). -/
  phase : Kind → Nat
  /-- Who may sign for a kind (at every slot). -/
  kindSel : Kind → SelSpec n

attribute [instance] Skeleton.decKind

/-- Signing roles: the proposer of a slot, a committee kind at a slot, or the
poll role. -/
inductive ShapeRole (Kind : Type) where
  | proposer (s : Slot)
  | duty (s : Slot) (k : Kind)
  | poll
  deriving DecidableEq

/-- Closed provenance rule (D-25): a header may be signed as a proposal by the
proposer of its own position, or in the poll role. -/
def ProposalRole {Info Kind : Type} (h : Header Info) : ShapeRole Kind → Prop
  | .proposer s => s = h.pos
  | .duty _ _ => False
  | .poll => True

instance {Info Kind : Type} (h : Header Info) (r : ShapeRole Kind) :
    Decidable (ProposalRole h r) := by
  cases r <;> unfold ProposalRole <;> infer_instance

/-- Duties: the proposal of a positive slot, a committee kind at a slot, and
the two poll duties (proposal and message) at every unit tick `t ≥ 0`, not
tied to the grid. -/
inductive ShapeDuty (Kind : Type) where
  | propose (s : Slot) (hs : 0 < s)
  | act (s : Slot) (k : Kind)
  | pollPropose (t : Nat)
  | poll (t : Nat)

/-- The wire objects of a shape. -/
abbrev ShapeObj (n : Nat) (Kind Info Body : Type) : Type :=
  Obj n (ShapeRole Kind) (Header Info) Body

/-- A chain shape: the skeleton plus the protocol's state machine. Honest code
knows the public parameters and its own key (`init`, `restore`); the engine
writes positions of slot proposals and every proposal's payload. -/
structure ChainShape (pub : Public) (Out : Type) (Info : Type) [DecidableEq Info]
    [Encodable Info] : Type 1 where
  /-- The public skeleton. -/
  skel : Skeleton pub.n
  State : Type
  /-- Protocol data (votes, certificates, …). -/
  Body : Type
  /-- What a restart keeps. -/
  Durable : Type
  decBody : DecidableEq Body
  /-- The initial state of the node with the given key. -/
  init : Key pub → State
  /-- The clock update at every tick. -/
  clock : State → Time → State
  /-- Slot proposal: parent, info, carried objects. `compile` writes
  `pos := s` and `input := encodeTxs mempool`. -/
  propose : State → Slot →
    Option (ParentRef × Info × List (ShapeObj pub.n skel.Kind Info Body))
  /-- The message of committee kind `k` at slot `s`: data and carried objects. -/
  act : State → Slot → skel.Kind → Option (Body × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Poll proposal at tick `t`: parent, locally chosen position (height), info
  (round), carried objects. `compile` writes `input := encodeTxs mempool`. -/
  pollPropose : State → Time →
    Option (ParentRef × Nat × Info × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Poll message at tick `t` (votes of poll protocols). -/
  poll : State → Time → Option (Body × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Unsigned objects (items allowed); relay is done here, by carrying. -/
  gossip : State → Time →
    List (Msg (Header Info) Body × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Processing a delivered object, with the digests of the items it contains. -/
  process : State → ShapeObj pub.n skel.Kind Info Body → List (Header Info × Nat) → State
  /-- Recording an own released object, with the digests of the items it
  contains. -/
  recordOwn : State → ShapeObj pub.n skel.Kind Info Body → List (Header Info × Nat) → State
  durable : State → Durable
  /-- The state after a restart, from the own key, what was kept, and the time. -/
  restore : Key pub → Durable → Time → State
  /-- The output chains, one per output identifier. -/
  out : Out → State → Chain Info
  /-- The slashing rule: two objects that, signed by one validator, convict it.
  The `.poll` role carries no tick or round, so a poll shape must tell its
  proposals apart by their contents (e.g. height and round in `pos`/`info`):
  a rule keyed only on the role would make an honest re-proposal in a later
  round conflict, and the engine's slashing protection would suppress it. -/
  conflicts : ShapeObj pub.n skel.Kind Info Body → ShapeObj pub.n skel.Kind Info Body → Bool

attribute [instance] ChainShape.decBody

/-- A chain shape for every choice of the public parameters, with the outputs
of schema `O`. -/
abbrev ShapeFamily (O : OutputSchema) (Info : Type) [DecidableEq Info] [Encodable Info] :=
  (pub : Public) → ChainShape pub O.Id Info

end Consensus.Shape

end
