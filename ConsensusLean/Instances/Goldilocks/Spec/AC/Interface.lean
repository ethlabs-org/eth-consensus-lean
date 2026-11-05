module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Params
public import ConsensusLean.Instances.Goldilocks.Spec.Frame

@[expose] public section

/-! # Goldilocks: the AC interface

The available chain as the node sees it (`specs/goldilocks/tex/shared/composition.tex`
§"The available chain"): an AC has a state, wire messages, a block
payload and nine functions over `(𝒜, Φ, t)`, never over the FG state. `ACInterface P FGP` is
that record, executable: each call returns the new state and what it emits, and every function
reads the frame `Φ` (a `Frame` whose blocks carry the FG payload `FGP`, which the AC never
reads, and the AC's own payload). The local validator index (`val_index`) is an argument of the
calls that can sign.

Each emission carries the AC state at its **internal read point** (for an own vote: after the
unlocking, before the own admission) and, for a duty that walks to a head, a `DutyHead`: the
head, where its walk starts, and the domain whose viable tree it walks (requirement 1 is about
these).

This module holds only what the Challenge statements reach; the reachable states and the interface
requirements (`ReachableAt`, `CallOK`, `Requirements`) are in `Milestones/Spec/AC/Interface`
(`docs/decisions.md` §"Trusted surface and Challenge scope"). -/

namespace Consensus.Goldilocks

/-- The head of a duty with its walk: the head, the block where the walk starts, and the domain
whose viable tree it walks (the full tree for a proposal; for a vote the vote domain
`SA.voteDomain`: the voter block tree, or the whole tree when the voter block tree's viable tree
is empty, the full-tree fallback of `docs/decisions.md` §"Goldilocks model choices"). -/
structure DutyHead (n : Nat) (FGP ACP : Type) where
  /-- The head. -/
  head : Block n FGP ACP
  /-- The block where the walk starts (the anchor). -/
  start : Block n FGP ACP
  /-- The domain: the walk walks `viable_tree(Φ, dom)`. -/
  dom : Set (Block n FGP ACP)

/-- An emission of an AC call: the message, the AC state at the call's internal read point for
it, and its duty head when the message is a duty with a head (a vote). -/
structure Emission (n : Nat) (FGP ACP S M : Type) where
  /-- The emitted message. -/
  msg : M
  /-- The AC state at the internal read point of the emission. -/
  readPoint : S
  /-- The duty head of the emission, if any. -/
  head : Option (DutyHead n FGP ACP)

/-- An available chain for the node with parameters `P`, polymorphic in nothing but the FG
payload `FGP` it never reads: its state, wire messages and block payload, the stateless checks,
the initial state, and the nine functions of composition.tex (four return the new state and
their emissions: `ac_on_message`, `ac_on_block`, `ac_on_tick`, `ac_restart`; `ac_proposal` and
`ac_to_fg` return the new state and their value; `ac_confirmed` and `ac_head` only read). -/
structure ACInterface (P : Params) (FGP : Type) where
  /-- The AC state `𝒜`. -/
  State : Type
  /-- The AC wire messages. -/
  Msg : Type
  /-- The AC block payload. -/
  Payload : Type
  /-- `ac_valid_payload(B)`: the stateless check of a block's AC payload. -/
  validPayload : Block P.n FGP Payload → Prop
  /-- The AC's wire checks of a message. -/
  validMsg : Msg → Prop
  /-- The state holds (has admitted) the message: an honest node forwards an AC message when its
  AC admits it, also from a block's payload (composition.tex §"Model"). -/
  holdsMsg : State → Msg → Prop
  /-- The AC payload of genesis. -/
  genesisPayload : Payload
  /-- The initial AC state. -/
  initial : State
  /-- `ac_on_message(𝒜, Φ, t, m)` at validator `self`. -/
  onMessage : Fin P.n → State → Frame P.n FGP Payload → Time → Msg →
    State × List (Emission P.n FGP Payload State Msg)
  /-- `ac_on_block(𝒜, Φ, t, B)` at validator `self`, after the FG accepted `B`. -/
  onBlock : Fin P.n → State → Frame P.n FGP Payload → Time → Block P.n FGP Payload →
    State × List (Emission P.n FGP Payload State Msg)
  /-- `ac_on_tick(𝒜, Φ, t)` at validator `self`. -/
  onTick : Fin P.n → State → Frame P.n FGP Payload → Time →
    State × List (Emission P.n FGP Payload State Msg)
  /-- `ac_proposal(𝒜, Φ, t)`: the parent (a duty head) and the AC payload, or `⊥`. -/
  proposal : State → Frame P.n FGP Payload → Time →
    State × Option (DutyHead P.n FGP Payload × Payload)
  /-- `ac_to_fg(𝒜, Φ, t)`: `fg_confirmed` (or `⊥`). -/
  toFG : State → Frame P.n FGP Payload → Time → State × Option (Block P.n FGP Payload)
  /-- `ac_confirmed(𝒜, Φ, t)`: the confirmed tip. -/
  confirmed : State → Frame P.n FGP Payload → Time → Block P.n FGP Payload
  /-- `ac_head(𝒜, Φ, t)`: the head. -/
  head : State → Frame P.n FGP Payload → Time → Block P.n FGP Payload
  /-- `ac_restart(𝒜, Φ, t)` at validator `self`, with the emissions of its replay. -/
  restart : Fin P.n → State → Frame P.n FGP Payload → Time →
    State × List (Emission P.n FGP Payload State Msg)

namespace ACInterface

variable {P : Params} {FGP : Type} (A : ACInterface P FGP)

/-- The blocks the AC sees. -/
abbrev Blk := Block P.n FGP A.Payload

/-- The frames the AC reads. -/
abbrev Frm := Frame P.n FGP A.Payload

/-- The emissions of the AC's calls. -/
abbrev Em := Emission P.n FGP A.Payload A.State A.Msg

/-- An AC call, as the node makes it (composition.tex Figure "Node"). -/
inductive Call where
  /-- `ac_on_tick`. -/
  | tick
  /-- `ac_proposal`. -/
  | proposal
  /-- `ac_to_fg`. -/
  | toFG
  /-- `ac_on_message(m)`. -/
  | message (m : A.Msg)
  /-- `ac_on_block(B)`. -/
  | block (B : A.Blk)
  /-- `ac_restart`. -/
  | restart

/-- One call at validator `self` from state `s` with frame `Φ` at time `t`: the new state and
the emissions. -/
def step (self : Fin P.n) (s : A.State) (Φ : A.Frm) (t : Time) : A.Call → A.State × List A.Em
  | .tick => A.onTick self s Φ t
  | .proposal => ((A.proposal s Φ t).1, [])
  | .toFG => ((A.toFG s Φ t).1, [])
  | .message m => A.onMessage self s Φ t m
  | .block B => A.onBlock self s Φ t B
  | .restart => A.restart self s Φ t

end ACInterface

end Consensus.Goldilocks

end
