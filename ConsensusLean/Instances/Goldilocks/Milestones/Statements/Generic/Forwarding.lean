module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace

/-! # Ordered forwarding statements

Protocol-independent wire observations and ordered execution. The implication targets in this
module are unproved statements, not supplied forwarding or service theorems. Source execution
and honest-prefix finality-gadget laws remain unsupplied obligations.
-/

@[expose] public section

set_option autoImplicit false

namespace Consensus.Goldilocks.Generic

namespace ForwardingEmit

open Model

variable {V : Type} [Fintype V] [DecidableEq V]
  {O : OutputSchema} {F : ProtocolFamily O} {E : Env V}

/-- Actual engine operations, with each candidate release retaining its own occurrence. -/
inductive Phase (rho : Run F E) where
  | process (object : (protoOf F E).Object)
  | clock (t : Time)
  | act (duty : (protoOf F E).Duty)
  | release (candidate : (protoOf F E).Object)
  | restore (t : Time)

/-- A selected act installs state before release; an unselected act is a no-op. -/
def phaseStep (rho : Run F E) (v : V) (nd : Model.Node (protoOf F E)) :
    Phase rho → Model.Node (protoOf F E) × List (protoOf F E).Object
  | .process o =>
    (⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩, [])
  | .clock t =>
    (⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩, [])
  | .act d =>
    if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
      (⟨((protoOf F E).act nd.st d).1, nd.seen⟩, [])
    else (nd, [])
  | .release c => releaseAll (protoOf F E) rho.hash (rho.ownKey v) nd [c]
  | .restore t =>
    (⟨(protoOf F E).restore (rho.ownKey v) ((protoOf F E).durable nd.st) t, nd.seen⟩, [])

/-- Candidates are captured from the pre-act state, not recomputed after the act. -/
def dutyPhases (rho : Run F E) (v : V) (nd : Model.Node (protoOf F E))
    (d : (protoOf F E).Duty) : List (Phase rho) :=
  .act d :: (rho.signedCandidate v d ((protoOf F E).act nd.st d).2).map Phase.release

/-- Execute phases in order, accumulating ordered outputs without removing duplicates. -/
def runPhases (rho : Run F E) (v : V) (nd : Model.Node (protoOf F E))
    (phases : List (Phase rho)) : Model.Node (protoOf F E) × List (protoOf F E).Object :=
  phases.foldl (fun r p => let s := phaseStep rho v r.1 p; (s.1, r.2 ++ s.2)) (nd, [])

/-- Unsupplied endpoint binding. Exact scheduler binding is required separately. -/
structure EventBinding (rho : Run F E) where
  phases : Nat → List (Phase rho)
  actor : Nat → V
  actor_eq : ∀ i e, rho.events[i]? = some e → actor i = e.node
  finalState : ∀ i, i < rho.events.length →
    (runPhases rho (actor i) (rho.stateBefore i (actor i)) (phases i)).1 =
      rho.stateBefore (i + 1) (actor i)
  releases : ∀ i, i < rho.events.length →
    (runPhases rho (actor i) (rho.stateBefore i (actor i)) (phases i)).2 = rho.releasesAt i

/-- Thread the existing duty engine state between consecutive duties. -/
def expandDuties (rho : Run F E) (v : V) :
    Model.Node (protoOf F E) → List (protoOf F E).Duty → List (Phase rho)
  | _, [] => []
  | nd, d :: ds => dutyPhases rho v nd d ++ expandDuties rho v (rho.dutyStep v nd d).1 ds

/-- Expand the existing event scheduler without introducing new scheduling behavior. -/
def eventPhases (rho : Run F E) (i : Nat) : List (Phase rho) :=
  match rho.events[i]? with
  | none => []
  | some (.restart _ t) => [.restore t]
  | some (.tick v t) =>
    let nd := rho.stateBefore i v
    let nd₁ : Model.Node (protoOf F E) :=
      ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
    if E.awake v t then
      let ds := (protoOf F E).duties t
      [.clock t] ++ expandDuties rho v nd₁ ds ++
        (gossipCandidates (protoOf F E) (rho.runDuties v nd₁ ds).1.st t).map Phase.release
    else [.clock t]
  | some (.deliver v o t) =>
    let nd := rho.stateBefore i v
    let nd₁ : Model.Node (protoOf F E) :=
      ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
    let ds := (protoOf F E).deliverDuties t
    [.process o] ++ expandDuties rho v nd₁ ds ++
      (gossipCandidates (protoOf F E) (rho.runDuties v nd₁ ds).1.st t).map Phase.release

/-- Unsupplied exact phase-list equation, excluding endpoint-preserving fake schedules. -/
def SchedulerBinding (rho : Run F E) (binding : EventBinding rho) : Prop :=
  ∀ i, binding.phases i = eventPhases rho i

/-- Actual state before a phase, computed by the prefix fold. -/
def boundary (rho : Run F E) (binding : EventBinding rho) (i p : Nat) :
    Model.Node (protoOf F E) :=
  (runPhases rho (binding.actor i) (rho.stateBefore i (binding.actor i))
    ((binding.phases i).take p)).1

end ForwardingEmit

open Shape Blocks

variable {P : Params} {A : NodeAC P} {n : Nat} {Role Item Body : Type}

/-- Unbundled wire observation, definitionally the engine's protocol-indexed digests. -/
def forwardingDigests (hash : Item → Nat) (o : Model.Obj n Role Item Body) :
    List (Item × Nat) :=
  (o.parts.filterMap Model.Obj.item?).map (fun x => (x, hash x))

/-- Canonical blocks, messages and signed forwarding envelopes over the actual wire objects.
Decoder context laws compare results on one object, never whole digest lists. -/
structure ForwardingCodec (A : NodeAC P) (n : Nat) (Role Item Body : Type) where
  forwardObject : Fin P.n → Time → Option (Model.Obj n Role Item Body) → A.Blk →
    Model.Obj n Role Item Body
  decodeForward : List (Item × Nat) → Model.Obj n Role Item Body →
    Option (Fin P.n × Time × Option (Model.Obj n Role Item Body) × A.Blk)
  blockObject : A.Blk → Model.Obj n Role Item Body
  decodeBlock : List (Item × Nat) → Model.Obj n Role Item Body → Option A.Blk
  blockHeader : A.Blk → Item
  messageObject : A.Msg → Model.Obj n Role Item Body
  decodeMessage : List (Item × Nat) → Model.Obj n Role Item Body → Option A.Msg
  messageForwardObject : Fin P.n → Time → A.Msg → Model.Obj n Role Item Body
  decodeMessageForward : List (Item × Nat) → Model.Obj n Role Item Body →
    Option (Fin P.n × Time × A.Msg)
  canon : List (Item × Nat) → Model.Obj n Role Item Body → Option (Node.Event A)
  keyIndex : Fin P.n → Fin n
  pollRole : Role
  forward_exact : ∀ hs o x t parent B, decodeForward hs o = some (x, t, parent, B) →
    o = forwardObject x t parent B ∧
    o.auth = .signed (keyIndex x) pollRole ∧
    o.carried = parent.toList ++ [blockObject B]
  forward_child_decode : ∀ hs o x t parent B,
    decodeForward hs o = some (x, t, parent, B) →
    decodeBlock hs (blockObject B) = some B
  block_decode_exact : ∀ hs q B, decodeBlock hs q = some B → q = blockObject B
  block_canon : ∀ hs q B, decodeBlock hs q = some B ↔ canon hs q = some (.block B)
  block_item : ∀ B, (blockObject B).item? = some (blockHeader B)
  message_forward_exact : ∀ hs o x t m, decodeMessageForward hs o = some (x, t, m) →
    o = messageForwardObject x t m ∧
    o.auth = .signed (keyIndex x) pollRole ∧ o.carried = [messageObject m] ∧
    decodeMessage hs (messageObject m) = some m
  message_decode_exact : ∀ hs q m, decodeMessage hs q = some m → q = messageObject m
  message_canon : ∀ hs q m, decodeMessage hs q = some m ↔ canon hs q = some (.message m)
  forward_digest_context : ∀ hash outer inner, Model.Obj.Contains outer inner →
    decodeForward (forwardingDigests hash outer) inner =
      decodeForward (forwardingDigests hash inner) inner
  block_digest_context : ∀ hash outer inner, Model.Obj.Contains outer inner →
    decodeBlock (forwardingDigests hash outer) inner =
      decodeBlock (forwardingDigests hash inner) inner
  message_digest_context : ∀ hash outer inner, Model.Obj.Contains outer inner →
    decodeMessage (forwardingDigests hash outer) inner =
      decodeMessage (forwardingDigests hash inner) inner
  message_forward_digest_context : ∀ hash outer inner, Model.Obj.Contains outer inner →
    decodeMessageForward (forwardingDigests hash outer) inner =
      decodeMessageForward (forwardingDigests hash inner) inner

/-- The actual ordered recursive parts execute canonical node groups; failed decoding and
empty execution advance the part occurrence without inventing a node cut. -/
inductive OrderedDelivery (proposer : Nat → Fin P.n) (tr : RunTrace A)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (canon : List (Item × Nat) → Model.Obj n Role Item Body → Option (Node.Event A))
    (hs : List (Item × Nat)) (y : Fin P.n) (u : Time) :
    List (Model.Obj n Role Item Body) → Nat → Nat → Prop
  | nil (j : Nat) : OrderedDelivery proposer tr dg canon hs y u [] j j
  | event {o os j j'} (ev : Node.Event A) : canon hs o = some ev →
      tr.GroupAt proposer dg y j u ev →
      OrderedDelivery proposer tr dg canon hs y u os
        (j + (Node.exec proposer dg y (tr.state y j) u ev).2.length) j' →
      OrderedDelivery proposer tr dg canon hs y u (o :: os) j j'
  | drop {o os j j'} : canon hs o = none →
      OrderedDelivery proposer tr dg canon hs y u os j j' →
      OrderedDelivery proposer tr dg canon hs y u (o :: os) j j'
  | noCut {o os j j'} (ev : Node.Event A) : canon hs o = some ev →
      (Node.exec proposer dg y (tr.state y j) u ev).2 = [] →
      OrderedDelivery proposer tr dg canon hs y u os j j' →
      OrderedDelivery proposer tr dg canon hs y u (o :: os) j j'

/-- Unsupplied source laws. Store projection equality is derived from local execution;
the honest-prefix finality-gadget contract is a separate named requirement. -/
structure ForwardingSourceLaws (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A) : Prop where
  local_run : Growing.LocalRun proposer dg H sg tr
  fg_prefix : Compose.NoCollRun dg tr → ∀ d : Time, 0 ≤ d →
    FGLocalRun A.genesisPayload (H d) (tr.HonestBlocksAt H) (tr.upTo d).projFG

/-- Unproved parent-first holding implication over the same signer, trace and block universe. -/
def ForwardReceiptHeldEdge (codec : ForwardingCodec A n Role Item Body)
    (proposer : Nat → Fin P.n) (tr : RunTrace A)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) : Prop :=
  ForwardingSourceLaws proposer dg H sg tr → Compose.NoCollRun dg tr →
  ∀ x y j d, 0 ≤ d → (∀ k < j, tr.time k ≤ d) → y ∈ H d →
  ∀ hs u B, Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
  ∀ child o stamp parent r e,
    codec.decodeForward hs o = some (x, stamp, parent, child) →
    OrderedDelivery proposer tr dg codec.canon hs y u o.parts r e →
    e ≤ j → stamp ≤ u → Anc (tr.HonestBlocksAt H) child B →
    (∀ q tq pq C, Model.Obj.Contains o q →
      codec.decodeForward hs q = some (x, tq, pq, C) →
      ∃ k, tr.AcceptAt x k C ∧ x ∈ H (tr.time k)) →
    child ∈ (tr.state y e).fg.tree

end Consensus.Goldilocks.Generic
