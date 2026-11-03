module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Params
public import ConsensusLean.Instances.Goldilocks.Spec.Frame

@[expose] public section

/-! # Goldilocks: the AC interface, reachable AC states, and the interface requirements

The available chain as the node sees it (fradamt-agent/goldilocks `spec/shared/composition.tex`
§"The available chain"; decomposition §2 D, `AC`): an AC has a state, wire messages, a block
payload and nine functions over `(𝒜, Φ, t)`, never over the FG state. `ACInterface P FGP` is
that record, executable: each call returns the new state and what it emits, and every function
reads the frame `Φ` (a `Frame` whose blocks carry the FG payload `FGP`, which the AC never
reads, and the AC's own payload). The local validator index (`val_index`) is an argument of the
calls that can sign.

Each emission carries the AC state at its **internal read point** (for an own vote: after the
unlocking, before the own admission) and, for a duty that walks to a head, a `DutyHead`: the
head, where its walk starts, and the domain whose viable tree it walks (requirement 1 is about
these).

`ReachableAt` is the claims' reachability (goldilocks-claims.tex §"How to read the DAG",
goldilocks#21): the states reached from the initial state by calls at nondecreasing times from
`0`, starting from the initial frame (tree `{genesis}`), with well-formed frames, where
every call other than `ac_on_block` (a restart included) sees the frame of the previous call and
`ac_on_block(Φ', B)` is called only when `Φ ⊑_B Φ'` for the previous frame `Φ` (G0.3 (frame));
the trees of all the frames (hence every block passed to `ac_on_block`, which is in the new tree)
lie in one coherent set `U` (roots injective, slots increasing; at a node, the accepted tree
`Σ.T`, which only grows); and the inputs pass the AC wire checks: a message passes `validMsg`, a
block passes `validPayload` and is not of a future slot (the node drops those). That an honest
node's AC states are reachable is claims C0.5. The restart replay is inside the restart call.

`Requirements` is requirements 1–4 of composition.tex §"The available chain" (claims A0.6) and
requirement 5, the proposal payload (claims A0.9), each at every reachable state and every
later time. (A well-formed frame is finite, `FrameOK.finite`: the AC's "deepest" choices and
head walks are functions on finite trees.) -/

namespace Consensus.Goldilocks

/-- The head of a duty with its walk: the head, the block where the walk starts, and the domain
whose viable tree it walks (the full tree for a proposal and `ac_to_fg`; for a vote the vote
domain `SA.voteDomain`: the voter block tree, or the whole tree when the voter block tree's
viable tree is empty, the recorded fallback of `docs/decisions.md`, 2026-11-02). -/
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
the initial state, and the nine functions of composition.tex (the six that change the state
return the new state and their emissions; `ac_proposal` and `ac_to_fg` also return their
values; `ac_confirmed` and `ac_head` only read). -/
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
  AC admits it, also from a block's payload (composition.tex §"Model"; goldilocks#28, #32). -/
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

/-- The initial frame: the tree is `{genesis}`, the block of slot `0` with the genesis root, no
parent, and the AC's genesis payload. -/
def InitialFrame (Φ : A.Frm) : Prop :=
  Φ.tree = {Φ.F} ∧ Φ.F.root = P.genesisRoot ∧ Φ.F.slot = 0 ∧ Φ.F.parent = none ∧
    Φ.F.acPayload = A.genesisPayload

/-- A frame the AC may be called with inside `U`: well formed (so finite) and in `U`. -/
def FrameIn (U : Set A.Blk) (Φ : A.Frm) : Prop := FrameOK Φ ∧ Φ.tree ⊆ U

/-- The call law (claims C0.5 (a), (b)) for the call `c` at time `t` with frame `Φ'`, after a
call with frame `Φ`: the frame is well formed and in `U`; it is the previous frame,
except that `ac_on_block(Φ', B)` is called exactly with `Φ ⊑_B Φ'`; a message passes the AC's
wire checks; a block passes `ac_valid_payload` and is not of a future slot. (A block passed to
`ac_on_block` is in `Φ'.tree ⊆ U` by the frame step.) -/
def CallOK (U : Set A.Blk) (Φ : A.Frm) (t : Time) (c : A.Call) (Φ' : A.Frm) : Prop :=
  A.FrameIn U Φ' ∧
    match c with
    | .block B => FrameStep Φ B Φ' ∧ A.validPayload B ∧ B.slot ≤ P.slotOf t
    | .message m => Φ' = Φ ∧ A.validMsg m
    | _ => Φ' = Φ

/-- `s` is reachable at validator `self` inside `U`, with `Φ` the frame of the last call (the
initial frame before any call) and `t` the time of the last call (`0` before any call). -/
inductive ReachableAt (self : Fin P.n) (U : Set A.Blk) : A.State → A.Frm → Time → Prop
  /-- The initial state, with the initial frame, at time `0`. -/
  | init (Φ : A.Frm) : A.InitialFrame Φ → A.FrameIn U Φ → ReachableAt self U A.initial Φ 0
  /-- One more call, at a time not before the last one, obeying the call law. -/
  | step {s : A.State} {Φ Φ' : A.Frm} {t t' : Time} (c : A.Call) :
      ReachableAt self U s Φ t → t ≤ t' → A.CallOK U Φ t' c Φ' →
      ReachableAt self U (A.step self s Φ' t' c).1 Φ' t'

/-- One lawful call `c` of validator `self` inside `U`, from the state `p.1` whose last call had
frame `p.2.1` at time `p.2.2`, to the state `q.1` it leaves, with the call's frame `q.2.1` and
time `q.2.2`. -/
def CallStep (self : Fin P.n) (U : Set A.Blk) (p : A.State × A.Frm × Time) (c : A.Call)
    (q : A.State × A.Frm × Time) : Prop :=
  p.2.2 ≤ q.2.2 ∧ A.CallOK U p.2.1 q.2.2 c q.2.1 ∧ q.1 = (A.step self p.1 q.2.1 q.2.2 c).1

/-- `s` is a reachable AC state of validator `self`: reachable inside some coherent set. -/
def Reachable (self : Fin P.n) (s : A.State) : Prop :=
  ∃ U : Set A.Blk, Coherent U ∧ ∃ Φ t, A.ReachableAt self U s Φ t

/-- A duty head is good at frame `Φ` (requirement 1): it extends `fc_root`, and, when its walk
starts in the viable tree of its domain, it is in `viable_heads`. -/
def HeadOK (Φ : A.Frm) (d : DutyHead P.n FGP A.Payload) : Prop :=
  Φ.Anc Φ.fcRoot d.head ∧ (d.start ∈ Φ.viableTree d.dom → d.head ∈ Φ.viableHeads)

/-- `Q` holds at every reachable state (with the frame and time of its last call) of every
validator, inside every coherent set. -/
def AtReachable (Q : Fin P.n → Set A.Blk → A.State → A.Frm → Time → Prop) : Prop :=
  ∀ (self : Fin P.n) (U : Set A.Blk), Coherent U →
    ∀ s Φ t₀, A.ReachableAt self U s Φ t₀ → Q self U s Φ t₀

/-- **Requirement 1.** Every head of a duty extends `fc_root`, and one whose walk starts in the
viable tree of its domain is in `viable_heads`: the parent of a proposal (at a slot start) and
the head of every emitted vote of every lawful next call (at that call's frame). -/
def ReqHeads : Prop :=
  A.AtReachable fun self U s Φ t₀ =>
    (∀ σ : Nat, t₀ ≤ P.slotTime σ → ∀ d p,
      (A.proposal s Φ (P.slotTime σ)).2 = some (d, p) → A.HeadOK Φ d) ∧
    (∀ t (c : A.Call) Φ', t₀ ≤ t → A.CallOK U Φ t c Φ' →
      ∀ e ∈ (A.step self s Φ' t c).2, ∀ d, e.head = some d → A.HeadOK Φ' d)

/-- **Requirement 2.** A block `fg_confirmed ≠ ⊥` is in `viable_tree(Φ, Φ.tree)`. -/
def ReqSource : Prop :=
  A.AtReachable fun _ _ s Φ t₀ => ∀ t, t₀ ≤ t → ∀ C,
    (A.toFG s Φ t).2 = some C → C ∈ Φ.viableTree Φ.tree

/-- **Requirement 3.** The output of `ac_head` extends `fc_root`, and the confirmed tip extends
`Φ.F` and is an ancestor of that output. -/
def ReqOutputs : Prop :=
  A.AtReachable fun _ _ s Φ t₀ => ∀ t, t₀ ≤ t →
    Φ.Anc Φ.fcRoot (A.head s Φ t) ∧ Φ.Anc Φ.F (A.confirmed s Φ t) ∧
      Φ.Anc (A.confirmed s Φ t) (A.head s Φ t)

/-- **Requirement 4.** The parent of a proposal (at a slot start) is a head of the AC at that
time: the head of `ac_head` at the state the proposal leaves. -/
def ReqParent : Prop :=
  A.AtReachable fun _ _ s Φ t₀ => ∀ σ : Nat, t₀ ≤ P.slotTime σ → ∀ s' d p,
    A.proposal s Φ (P.slotTime σ) = (s', some (d, p)) → d.head = A.head s' Φ (P.slotTime σ)

/-- **Requirement 5** (claims A0.9). The payload of a proposal at the start of slot `σ` passes
`ac_valid_payload` in every block of slot `σ` that carries it. -/
def ReqPayload : Prop :=
  A.AtReachable fun _ _ s Φ t₀ => ∀ σ : Nat, t₀ ≤ P.slotTime σ → ∀ d p,
    (A.proposal s Φ (P.slotTime σ)).2 = some (d, p) →
      ∀ B : A.Blk, B.slot = σ → B.acPayload = p → A.validPayload B

/-- The interface requirements 1–5 (claims A0.6 with A0.9): what the FG and the node may
assume of an AC. -/
structure Requirements : Prop where
  heads : A.ReqHeads
  source : A.ReqSource
  outputs : A.ReqOutputs
  parent : A.ReqParent
  payload : A.ReqPayload

end ACInterface

end Consensus.Goldilocks

end
