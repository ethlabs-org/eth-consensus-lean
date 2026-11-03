module
public import ConsensusLean.Spec.Blocks.TimeGrid
public import ConsensusLean.Spec.Blocks.Progress
public import ConsensusLean.Spec.Blocks.Chains
public import ConsensusLean.Spec.Blocks.Payload
public import ConsensusLean.Spec.Model.System

@[expose] public section

/-! # Chain shapes (L2)

A chain shape is a protocol written over the building blocks: a public
skeleton (time grid, proposer selection, poll selection, committee kinds with
their phases and selections) and a state machine that proposes headers,
signs committee and poll messages, gossips, processes, and reads chains. The
engine-facing protocol is `compile` (next module); everything here is public
syntax that a reviewer reads once for every protocol.

Proposals come in two forms: a slot proposal (role `.proposer s`,
released at the slot's time, at position `s`), and a poll proposal (role
`.poll`, released at a unit tick the protocol chooses locally, at a position
it chooses, for example a height). In both the engine writes the payload
(`input`). Committee duties sign in role `.duty s k` (slot and kind). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (Public Key SelSpec Obj Msg)

/-- A step of a tick's order: the slot proposal, committee kind `k`, the poll
proposal, the poll message. -/
inductive Step (Kind : Type) where
  | propose
  | kind (k : Kind)
  | pollPropose
  | poll

/-- Public block choices of a shape: the time grid, a proposer selection
per slot, the poll selection (`.fixed ∅` disables polling), a finite list of
committee kinds, each with a phase (its time offset within the slot) and a
selection, and the order of the steps within a tick. -/
structure Skeleton (n : Nat) : Type 1 where
  /-- The time grid. -/
  grid : TimeGrid
  /-- Who may propose at slot `s`: a fixed schedule (`fun s => .fixed {p s}`)
  or a free choice of the run (`fun _ => .sized 1`). -/
  proposerSel : Slot → SelSpec n
  /-- Who may sign in the poll role; `.fixed ∅` disables the poll steps
  altogether (an unselected duty does not run, so neither its state update nor
  a signature happens, `Model.Run.dutyStep`). -/
  pollSel : SelSpec n
  /-- Committee kinds. -/
  Kind : Type
  decKind : DecidableEq Kind
  /-- The committee kinds, in the order of the default `order`. -/
  kinds : List Kind
  /-- The nonnegative time offset of the kind's duty from the slot start (not required to
  be below the slot length: a kind may act in a later slot's interval). -/
  phase : Kind → Nat
  /-- Who may sign for a kind (at every slot). -/
  kindSel : Kind → SelSpec n
  /-- The steps of a tick, in the order the engine runs them; at a tick, the
  steps due at it run (`Skeleton.duties`). By default the proposal, then the
  kinds in `kinds` order, then the poll proposal and the poll message.

  A step left out never runs. A step may repeat: a repeated step yields the
  identical duty (the same slot and kind, so the same role and selection and,
  under a typical slashing rule, at most one signed message per duty), so
  repeats are for state-dependent placement or local work; two votes need two
  kinds. A fixed order bounds the signed attempts per tick: there are no
  reaction chains of state-dependent length, and a reaction to a receipt runs
  at the delivery only if `deliverOrder` lists a step for it. Gossip is built
  once, after all the duties of the tick (so no step sees the digests of the
  tick's gossip). Per-tick work goes in `clock`, which runs at the start of
  every tick; work after the duties of an awake tick goes in a trailing poll
  step, for keys selected in the poll role (the poll steps are due at every
  tick `t ≥ 0`; the other steps only at some ticks; an unselected duty is
  skipped). -/
  order : List (Step Kind) := [.propose] ++ kinds.map .kind ++ [.pollPropose, .poll]
  /-- The steps the engine runs at a delivery, in order, after `process` and
  before the delivery's gossip (`Model.Run.deliver`); the steps due at the
  delivery's time run (`Skeleton.deliverDuties`). By default none: a receipt
  then only changes the state, and its gossip leaves at the delivery. A shape
  that reacts to receipts (a poll vote sent when the receipt completes the
  node's view) lists the step here, typically `[.poll]`, so that the reaction
  leaves at the delivery's own time and not at a next tick that a sleeping
  node may never take. -/
  deliverOrder : List (Step Kind) := []

attribute [instance] Skeleton.decKind

/-- Signing roles: the proposer of a slot, a committee kind at a slot, or the
poll role. -/
inductive ShapeRole (Kind : Type) where
  | proposer (s : Slot)
  | duty (s : Slot) (k : Kind)
  | poll
  deriving DecidableEq

/-- Closed provenance rule: a header may be signed as a proposal by the
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
    [Countable Info] : Type 1 where
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
  /-- Slot proposal: the new state, and parent, info, carried objects.
  `compile` writes `pos := s` and `input := encodeTxs mempool`. As for every
  step, the state is applied for a selected proposer whether or not the
  proposal is released; for an unselected key the step does not run. -/
  propose : State → Slot →
    State × Option (ParentRef × Info × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Committee kind `k` at slot `s`: the new state, and data and carried
  objects. -/
  act : State → Slot → skel.Kind →
    State × Option (Body × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Poll proposal at tick `t`: the new state, and parent, locally chosen
  position (height), info (round), carried objects. `compile` writes
  `input := encodeTxs mempool`. -/
  pollPropose : State → Time →
    State × Option (ParentRef × Nat × Info × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Poll message at tick `t` (votes of poll protocols): the new state, and
  data and carried objects. -/
  poll : State → Time → State × Option (Body × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Ordered poll candidates. The default preserves the single-message poll;
  a publisher may override it to drain a parent-first queue in one selected duty. -/
  pollBatch : State → Time → State × List (Body × List (ShapeObj pub.n skel.Kind Info Body)) :=
    fun st t => let r := poll st t; (r.1, r.2.toList)
  /-- Unsigned objects (items allowed); relay is done here, by carrying. -/
  gossip : State → Time →
    List (Msg (Header Info) Body × List (ShapeObj pub.n skel.Kind Info Body))
  /-- Processing a delivered object, with the digests of the items it contains. -/
  process : State → ShapeObj pub.n skel.Kind Info Body → List (Header Info × Nat) → State
  /-- Engine-held dependencies for release and delivery. -/
  dependencies : Model.DependencyPolicy (ShapeObj pub.n skel.Kind Info Body) :=
    .trivial _
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
  /-- The row objects (`Model.Protocol.isRow`): delivered strictly before `ΔF`. Default: none. -/
  isRow : ShapeObj pub.n skel.Kind Info Body → Prop := fun _ => False

attribute [instance] ChainShape.decBody

/-- A chain shape for every choice of the public parameters, with the outputs
of schema `O`. -/
abbrev ShapeFamily (O : OutputSchema) (Info : Type) [DecidableEq Info] [Countable Info] :=
  (pub : Public) → ChainShape pub O.Id Info

end Consensus.Shape

end
