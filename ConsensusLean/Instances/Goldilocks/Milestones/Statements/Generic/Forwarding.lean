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

/-- Global receiver output vocabulary with the identical field formulas of
`Compose.Growing.ReceiverServiceAfterAt`. Explicit fieldwise conversion is deferred;
the distinct records are not definitionally equal. This is never a supplier premise. -/
structure ForwardingReceiverServiceAfter {P : Params} {FGP : Type} {A : ACInterface P FGP}
    (H : Time → Set (Fin P.n)) (U : Set A.Blk) (g : Time) (y : Fin P.n) (ac : ACTrace A) :
    Prop where
  message : ∀ x i m, x ∈ H (ac.time i) → ac.SendOrAdmit x i m → ∀ j ℓ, y ∈ H (ac.time j) →
    ac.CallAt y j ℓ → ac.deadline y j (max (ac.time i) g) ≤ ac.time j →
    ∃ k ≤ j, ac.time i ≤ ac.time k ∧ ac.ProcessAt y k m ∧
      ac.time k < ac.deadline y k (max (ac.time i) g)
  relay : ∀ x i B, x ∈ H (ac.time i) → ac.AcceptAt x i B → ∀ j ℓ, y ∈ H (ac.time j) →
    ac.CallAt y j ℓ → ac.deadline y j (max (ac.time i) g) ≤ ac.time j → Anc U ℓ.frame.F B →
    ∃ k ≤ j, ac.AcceptAt y k B ∧ ac.time k < ac.deadline y k (max (ac.time i) g)

/-- Finite pre-service output for an arbitrary node AC. The positive finality annotation
is independent of the node AC delay used by the actual deadlines. -/
structure FiniteServiceBefore (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.projAC.SendOrAdmit x i m → 0 ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ →
      tr.projAC.deadline y j (tr.time i) ≤ b →
      tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
      ∃ k ≤ j, tr.time i ≤ tr.time k ∧ tr.projAC.ProcessAt y k m ∧
        tr.time k < tr.projAC.deadline y k (tr.time i)
  acRelay : ∀ x i B, x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ →
      tr.projAC.deadline y j (tr.time i) ≤ b →
      tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
      ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k (tr.time i)
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → tr.BlockAcceptedBy y j (tr.time i) B

section Engine

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- Actual local mechanisms through a bounded reader horizon on the same engine run.
The trace may be a lawful prefix, but is not asserted to be an execution of a truncated run.
Every source, reader and used event has an explicit finite domain. -/
structure ForwardingEngineLaws (M : RunMap rho payload)
    (codec : ForwardingCodec A (Fintype.card V) (Model.protoOf (compiled F) E).Role
      (Model.protoOf (compiled F) E).Item (Model.protoOf (compiled F) E).Body)
    (binding : ForwardingEmit.EventBinding rho) (N : RunTrace A) (through : Time)
    (processStart processEnd : Nat → Nat) (receiptCuts internalBoundary : Nat → Nat → Nat) :
    Prop where
  scheduler : ForwardingEmit.SchedulerBinding rho binding
  source : rho.ExecutionValid → ForwardingSourceLaws M.proposer M.digest M.honest M.signer N
  key_eq : codec.keyIndex = M.keyIndex
  process_segment : ∀ e y outer u,
    rho.events[e]? = some (.deliver (M.validator y) outer u) → y ∈ M.honest u →
    u ≤ through → ∃ p : Nat, (binding.phases e)[p]? =
      some (ForwardingEmit.Phase.process (rho := rho) outer) ∧
      M.cut e ≤ processStart e ∧ processStart e ≤ processEnd e ∧
      processEnd e ≤ M.cut (e + 1) ∧ receiptCuts e 0 = processStart e ∧
      receiptCuts e outer.parts.length = processEnd e ∧
      (∀ k, processStart e ≤ k → k < processEnd e → N.time k = u)
  receipt_ordered : ∀ e y outer u,
    rho.events[e]? = some (.deliver (M.validator y) outer u) → y ∈ M.honest u →
    u ≤ through →
    OrderedDelivery M.proposer N M.digest codec.canon (Model.digests rho.hash outer)
      y u outer.parts (processStart e) (processEnd e)
  receipt_occurrence : ∀ e y outer u a q,
    rho.events[e]? = some (.deliver (M.validator y) outer u) → y ∈ M.honest u →
    u ≤ through → outer.parts[a]? = some q →
    receiptCuts e a ≤ receiptCuts e (a + 1) ∧
    processStart e ≤ receiptCuts e a ∧ receiptCuts e (a + 1) ≤ processEnd e ∧
    internalBoundary e a < internalBoundary e (a + 1) ∧
    OrderedDelivery M.proposer N M.digest codec.canon (Model.digests rho.hash outer)
      y u [q] (receiptCuts e a) (receiptCuts e (a + 1))
  used_event_cuts : ∀ e event, rho.events[e]? = some event → event.time ≤ through →
    (∀ k < M.cut (e + 1), N.time k ≤ through)
  released_wrapper_source : ∀ e event x outer q t parent B,
    rho.events[e]? = some event → event.node = M.validator x →
    event.time ≤ through → x ∈ M.honest event.time → outer ∈ rho.releasesAt e →
    Model.Obj.Contains outer q →
    codec.decodeForward (Model.digests rho.hash q) q = some (x, t, parent, B) →
    ∃ k, k < M.cut (e + 1) ∧ N.AcceptAt x k B ∧ N.time k = t ∧ t ≤ event.time
  root_stamp_le_release : ∀ e v s o x t parent B,
    rho.SendsAt v e s → v = M.validator x → o ∈ rho.releasesAt e →
    codec.decodeForward (Model.digests rho.hash o) o = some (x, t, parent, B) → t ≤ s
  acceptance_candidate : ∀ x k B, x ∈ M.honest (N.time k) → N.AcceptAt x k B →
    N.time k ≤ through → ∃ e r parent event,
      rho.events[e]? = some event ∧ event.node = M.validator x ∧ event.time = N.time k ∧
      M.cut e ≤ k ∧ k < M.cut (e + 1) ∧
      (binding.phases e)[r]? = some (.release (codec.forwardObject x (N.time k) parent B)) ∧
      codec.decodeForward (Model.digests rho.hash (codec.forwardObject x (N.time k) parent B))
        (codec.forwardObject x (N.time k) parent B) = some (x, N.time k, parent, B) ∧
      Model.releasable (ForwardingEmit.boundary rho binding e r).seen
        (codec.forwardObject x (N.time k) parent B) = true ∧
      Model.protects (Model.protoOf (compiled F) E) (rho.ownKey (M.validator x))
        (ForwardingEmit.boundary rho binding e r).seen
        (codec.forwardObject x (N.time k) parent B) = true ∧
      (Model.protoOf (compiled F) E).dependencies.ready
        (Model.closure (ForwardingEmit.boundary rho binding e r).seen)
        (codec.forwardObject x (N.time k) parent B) = true
  message_self : ∀ x i m j ℓ τ, x ∈ M.honest (N.projAC.time i) →
    N.projAC.SendOrAdmit x i m → N.projAC.time i ≤ through → N.projAC.time i ≤ τ →
    x ∈ M.honest (N.projAC.time j) → N.projAC.CallAt x j ℓ →
    N.projAC.time j ≤ through → N.projAC.deadline x j τ ≤ N.projAC.time j →
    ∃ k, k ≤ j ∧ N.projAC.ProcessAt x k m ∧ N.projAC.time k = N.projAC.time i ∧
      N.projAC.time k < N.projAC.deadline x k τ
  message_candidate : ∀ x i m, x ∈ M.honest (N.projAC.time i) →
    N.projAC.SendOrAdmit x i m → N.projAC.time i ≤ through → ∃ e r event,
      rho.events[e]? = some event ∧ event.node = M.validator x ∧
      event.time = N.projAC.time i ∧ M.cut e ≤ i ∧ i < M.cut (e + 1) ∧
      (binding.phases e)[r]? =
        some (.release (codec.messageForwardObject x (N.projAC.time i) m)) ∧
      codec.decodeMessageForward
        (Model.digests rho.hash (codec.messageForwardObject x (N.projAC.time i) m))
        (codec.messageForwardObject x (N.projAC.time i) m) = some (x, N.projAC.time i, m) ∧
      Model.releasable (ForwardingEmit.boundary rho binding e r).seen
        (codec.messageForwardObject x (N.projAC.time i) m) = true ∧
      Model.protects (Model.protoOf (compiled F) E) (rho.ownKey (M.validator x))
        (ForwardingEmit.boundary rho binding e r).seen
        (codec.messageForwardObject x (N.projAC.time i) m) = true ∧
      (Model.protoOf (compiled F) E).dependencies.ready
        (Model.closure (ForwardingEmit.boundary rho binding e r).seen)
        (codec.messageForwardObject x (N.projAC.time i) m) = true
  message_receipt_group : ∀ x i m e y receipt u q a j ℓ τ,
    x ∈ M.honest (N.projAC.time i) → N.projAC.SendOrAdmit x i m →
    N.projAC.time i ≤ through →
    rho.events[e]? = some (.deliver (M.validator y) receipt u) → y ∈ M.honest u →
    u ≤ through → N.projAC.time i ≤ u → Model.Obj.Contains receipt q →
    codec.decodeMessageForward (Model.digests rho.hash q) q = some (x, N.projAC.time i, m) →
    receipt.parts[a]? = some (codec.messageObject m) →
    (∃ b, receipt.parts[b]? = some q ∧ b ≤ a ∧ a < b + q.parts.length) →
    y ∈ M.honest (N.projAC.time j) → N.projAC.CallAt y j ℓ →
    N.projAC.time j ≤ through → processEnd e ≤ j → u < N.projAC.deadline y j τ →
    (∃ k, receiptCuts e a ≤ k ∧ k < receiptCuts e (a + 1) ∧
      processStart e ≤ k ∧ k < processEnd e ∧ k ≤ j ∧ N.projAC.ProcessAt y k m ∧
      N.projAC.time k = u ∧ N.projAC.time i ≤ N.projAC.time k ∧
      N.projAC.time k < N.projAC.deadline y k τ) ∨
    (∃ k, k < receiptCuts e a ∧ k ≤ j ∧ N.projAC.ProcessAt y k m ∧
      N.projAC.time i ≤ N.projAC.time k ∧ N.projAC.time k ≤ u ∧
      N.projAC.time k < N.projAC.deadline y k τ)

variable (M : RunMap rho payload)
  (codec : ForwardingCodec A (Fintype.card V) (Model.protoOf (compiled F) E).Role
    (Model.protoOf (compiled F) E).Item (Model.protoOf (compiled F) E).Body)
  (binding : ForwardingEmit.EventBinding rho)
  (processStart processEnd : Nat → Nat) (receiptCuts internalBoundary : Nat → Nat → Nat)

/-- Unproved acceptance-to-publication implication. The released object itself decodes;
a signed descendant of an unsigned carrier is not this output. -/
def ForwardAcceptancePublicationEdge : Prop :=
  rho.ExecutionValid →
  ForwardingEngineLaws M codec binding M.trace rho.horizon
    processStart processEnd receiptCuts internalBoundary →
  ∀ x k B, x ∈ M.honest (M.trace.time k) → M.trace.AcceptAt x k B →
    M.trace.time k ≤ rho.horizon → ∃ e r : Nat, ∃ parent event,
      rho.events[e]? = some event ∧ event.node = M.validator x ∧
      event.time = M.trace.time k ∧ M.cut e ≤ k ∧ k < M.cut (e + 1) ∧
      (binding.phases e)[r]? =
        some (ForwardingEmit.Phase.release (rho := rho)
          (codec.forwardObject x (M.trace.time k) parent B)) ∧
      codec.forwardObject x (M.trace.time k) parent B ∈ rho.releasesAt e ∧
      codec.decodeForward
        (Model.digests rho.hash (codec.forwardObject x (M.trace.time k) parent B))
        (codec.forwardObject x (M.trace.time k) parent B) = some (x, M.trace.time k, parent, B)

/-- Unproved receipt-to-acceptance implication with the original finite reader,
same-signer release, ancestry and strict-deadline guards. -/
def ReleasedReceiptAcceptedEdge : Prop :=
  rho.ExecutionValid → Compose.NoCollRun M.digest M.trace →
  ForwardingEngineLaws M codec binding M.trace rho.horizon
    processStart processEnd receiptCuts internalBoundary →
  ∀ i j v receipt o x u t deadline parent B t₀,
    rho.events[i]? = some (.deliver v receipt u) →
    (∀ k < j, M.trace.time k ≤ t₀) → rho.point.HonestAt v t₀ →
    Model.Obj.Contains receipt o → x ∈ M.honest t →
    rho.releases (M.validator x) o t →
    codec.decodeForward (Model.digests rho.hash o) o = some (x, t, parent, B) →
    M.cut (i + 1) ≤ j →
    Anc (M.trace.HonestBlocksAt M.honest) (M.trace.state (M.validator.symm v) j).fg.F B →
    u < deadline → ∃ k, k < M.cut (i + 1) ∧
      M.trace.AcceptAt (M.validator.symm v) k B ∧
      M.trace.time k ≤ u ∧ M.trace.time k < deadline

/-- Unproved post-synchrony acceptance relay on the same actual run. -/
def AcceptanceRelayAfterEdge : Prop :=
  rho.ExecutionValid → Compose.NoCollRun M.digest M.trace →
  ForwardingEngineLaws M codec binding M.trace rho.horizon
    processStart processEnd receiptCuts internalBoundary →
  ∀ g, rho.log.PSync rho.point g →
  ∀ x i B, x ∈ M.honest (M.trace.time i) → M.trace.AcceptAt x i B →
  ∀ y j, y ∈ M.honest (M.trace.time j) → M.trace.IsCall y j →
    M.trace.time j ≤ rho.horizon →
    M.trace.deadline y j (max (M.trace.time i) g) P.Δ ≤ M.trace.time j →
    Anc (M.trace.HonestBlocksAt M.honest) (M.trace.state y j).fg.F B →
    M.trace.BlockAcceptedBy y j (max (M.trace.time i) g) B

/-- Unproved global receiver-service output, with explicit fieldwise conversion to the
existing receiver record deferred. No target service is an input. -/
def ReceiverServiceAfterEdge : Prop :=
  rho.ExecutionValid → Compose.NoCollRun M.digest M.trace →
  ForwardingEngineLaws M codec binding M.trace rho.horizon
    processStart processEnd receiptCuts internalBoundary →
  ∀ g, rho.log.PSync rho.point g → ∀ y,
    ForwardingReceiverServiceAfter M.honest (M.trace.HonestBlocksAt M.honest) g y M.trace.projAC

/-- Unproved finite pre-service output, preserving the actual network cutoff. -/
def FiniteServiceBeforeEdge : Prop :=
  rho.ExecutionValid → Compose.NoCollRun M.digest M.trace →
  ForwardingEngineLaws M codec binding M.trace rho.horizon
    processStart processEnd receiptCuts internalBoundary →
  ∀ b, b ≤ rho.horizon → rho.log.SyncUntil rho.point b →
  ∀ ΔF, 0 < ΔF → FiniteServiceBefore M.trace M.honest ΔF b

/-- Unproved bounded post-service implication. Only prefix no-collision and prefix source
laws are consumed; the real engine point, log, event indices and horizon are unchanged. -/
def ReceiverServiceAfterThroughEdge (h : Time) : Prop :=
  0 ≤ h → h ≤ rho.horizon → rho.ExecutionValid →
  Compose.NoCollRun M.digest (M.trace.upTo h) →
  ForwardingSourceLaws M.proposer M.digest M.honest M.signer (M.trace.upTo h) →
  ForwardingEngineLaws M codec binding (M.trace.upTo h) h
    processStart processEnd receiptCuts internalBoundary →
  ∀ g, rho.log.PSync rho.point g → ∀ y,
    (∀ x i m, x ∈ M.honest ((M.trace.upTo h).projAC.time i) →
      (M.trace.upTo h).projAC.SendOrAdmit x i m → (M.trace.upTo h).projAC.time i ≤ h →
      ∀ j ℓ, y ∈ M.honest ((M.trace.upTo h).projAC.time j) →
        (M.trace.upTo h).projAC.CallAt y j ℓ → (M.trace.upTo h).projAC.time j ≤ h →
        (M.trace.upTo h).projAC.time j ≤ rho.horizon →
        (M.trace.upTo h).projAC.deadline y j
          (max ((M.trace.upTo h).projAC.time i) g) ≤ (M.trace.upTo h).projAC.time j →
        ∃ k, k ≤ j ∧ (M.trace.upTo h).projAC.time i ≤ (M.trace.upTo h).projAC.time k ∧
          (M.trace.upTo h).projAC.ProcessAt y k m ∧
          (M.trace.upTo h).projAC.time k < (M.trace.upTo h).projAC.deadline y k
            (max ((M.trace.upTo h).projAC.time i) g)) ∧
    (∀ x i B, x ∈ M.honest ((M.trace.upTo h).projAC.time i) →
      (M.trace.upTo h).projAC.AcceptAt x i B → (M.trace.upTo h).projAC.time i ≤ h →
      ∀ j ℓ, y ∈ M.honest ((M.trace.upTo h).projAC.time j) →
        (M.trace.upTo h).projAC.CallAt y j ℓ → (M.trace.upTo h).projAC.time j ≤ h →
        (M.trace.upTo h).projAC.time j ≤ rho.horizon →
        (M.trace.upTo h).projAC.deadline y j
          (max ((M.trace.upTo h).projAC.time i) g) ≤ (M.trace.upTo h).projAC.time j →
        Anc ((M.trace.upTo h).HonestBlocksAt M.honest) ℓ.frame.F B →
        ∃ k, k ≤ j ∧ (M.trace.upTo h).projAC.AcceptAt y k B ∧
          (M.trace.upTo h).projAC.time k < (M.trace.upTo h).projAC.deadline y k
            (max ((M.trace.upTo h).projAC.time i) g))

/-- Unproved bounded finite-service implication. The network cutoff need not precede h;
source and reader calls, rather than the cutoff, are restricted to the retained trace. -/
def FiniteServiceBeforeThroughEdge (h : Time) : Prop :=
  0 ≤ h → h ≤ rho.horizon → rho.ExecutionValid →
  Compose.NoCollRun M.digest (M.trace.upTo h) →
  ForwardingSourceLaws M.proposer M.digest M.honest M.signer (M.trace.upTo h) →
  ForwardingEngineLaws M codec binding (M.trace.upTo h) h
    processStart processEnd receiptCuts internalBoundary →
  ∀ b, b ≤ rho.horizon → rho.log.SyncUntil rho.point b → ∀ ΔF, 0 < ΔF →
    0 < ΔF ∧
    (∀ x i m, x ∈ M.honest ((M.trace.upTo h).time i) →
      (M.trace.upTo h).projAC.SendOrAdmit x i m → 0 ≤ (M.trace.upTo h).time i →
      (M.trace.upTo h).time i ≤ h → ∀ y j ℓ,
      y ∈ M.honest ((M.trace.upTo h).time j) → (M.trace.upTo h).projAC.CallAt y j ℓ →
      (M.trace.upTo h).time j ≤ h →
      (M.trace.upTo h).projAC.deadline y j ((M.trace.upTo h).time i) ≤ b →
      (M.trace.upTo h).projAC.deadline y j ((M.trace.upTo h).time i) ≤
        (M.trace.upTo h).time j →
      ∃ k ≤ j, (M.trace.upTo h).time i ≤ (M.trace.upTo h).time k ∧
        (M.trace.upTo h).projAC.ProcessAt y k m ∧
        (M.trace.upTo h).time k <
          (M.trace.upTo h).projAC.deadline y k ((M.trace.upTo h).time i)) ∧
    (∀ x i B, x ∈ M.honest ((M.trace.upTo h).time i) →
      (M.trace.upTo h).projAC.AcceptAt x i B → 0 ≤ (M.trace.upTo h).time i →
      (M.trace.upTo h).time i ≤ h → ∀ y j ℓ,
      y ∈ M.honest ((M.trace.upTo h).time j) → (M.trace.upTo h).projAC.CallAt y j ℓ →
      (M.trace.upTo h).time j ≤ h →
      (M.trace.upTo h).projAC.deadline y j ((M.trace.upTo h).time i) ≤ b →
      (M.trace.upTo h).projAC.deadline y j ((M.trace.upTo h).time i) ≤
        (M.trace.upTo h).time j →
      Anc ((M.trace.upTo h).HonestBlocksAt M.honest) ℓ.frame.F B →
      ∃ k ≤ j, (M.trace.upTo h).projAC.AcceptAt y k B ∧
        (M.trace.upTo h).time k <
          (M.trace.upTo h).projAC.deadline y k ((M.trace.upTo h).time i)) ∧
    (∀ x i B, x ∈ M.honest ((M.trace.upTo h).time i) →
      (M.trace.upTo h).AcceptAt x i B → 0 ≤ (M.trace.upTo h).time i →
      (M.trace.upTo h).time i ≤ h → ∀ y j,
      y ∈ M.honest ((M.trace.upTo h).time j) → (M.trace.upTo h).IsCall y j →
      (M.trace.upTo h).time j ≤ h →
      (M.trace.upTo h).deadline y j ((M.trace.upTo h).time i) P.Δ ≤ b →
      (M.trace.upTo h).deadline y j ((M.trace.upTo h).time i) P.Δ ≤ (M.trace.upTo h).time j →
      Anc ((M.trace.upTo h).HonestBlocksAt M.honest) ((M.trace.upTo h).state y j).fg.F B →
      (M.trace.upTo h).BlockAcceptedBy y j ((M.trace.upTo h).time i) B)

end Engine

end Consensus.Goldilocks.Generic
