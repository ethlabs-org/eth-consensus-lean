module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Frame

@[expose] public section

/-! # Goldilocks milestone vocabulary: reachable AC states and the interface requirements

The part of `Spec/AC/Interface` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. Names and bodies are unchanged.

`ReachableAt` is the claims' reachability (goldilocks-claims.tex §"How to read the DAG"):
the states reached from the initial state and frame by calls at nondecreasing
times that obey the call law `CallOK`, inside one coherent set `U` (at a node, the accepted tree
`Σ.T`, which only grows). That an honest node's AC states are reachable is claims C0.5. The
restart replay is inside the restart call.

`Requirements` is requirements 1–4 of composition.tex §"The available chain" (claims A0.6) and
requirement 5, the proposal payload (claims A0.9), each at every reachable state and every
later time. (A well-formed frame is finite, `FrameOK.finite`: the AC's "deepest" choices and
head walks are functions on finite trees.) -/

namespace Consensus.Goldilocks

namespace ACInterface

variable {P : Params} {FGP : Type} (A : ACInterface P FGP)

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
