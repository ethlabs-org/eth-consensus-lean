module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.NodeEngine.Simulation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run

@[expose] public section
namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V) (D : TraceData)

/-- Actual handler cuts, including cuts inside a multi-object delivery. -/
def CallDomain (self : Fin (Fintype.card V)) (s : (nodeAC (E := E) A hn).State)
    (Φ : (nodeAC (E := E) A hn).Frm) (t : Time) (c : (nodeAC (E := E) A hn).Call) : Prop :=
  rho.ExecutionValid ∧ ∃ k ℓ, (simTraceNodeAt A fin rho hn D).CallAt self k (.ac ℓ) ∧
    (simTraceNodeAt A fin rho hn D).time k = t ∧ ℓ.call = c ∧
    ℓ.frame = Φ ∧ ((simTraceNodeAt A fin rho hn D).state self k).ac = s

/-- Operation history through an engine event, before transport to global trace indices. -/
def EmittedThrough (i : Nat) (self : Fin (Fintype.card V))
    (m : (nodeAC (E := E) A hn).Msg) : Prop :=
  ∃ j ≤ i, ∃ r ∈ eventRecords A fin rho hn D j, r.node = self ∧
    ∃ ℓ, r.label = .ac ℓ ∧ ∃ e ∈ ℓ.emits, e.msg = m

def SignedThrough (i : Nat) (self : Fin (Fintype.card V))
    (a : FG.Att (Fintype.card V)) : Prop :=
  ∃ j ≤ i, ∃ r ∈ eventRecords A fin rho hn D j, r.node = self ∧
    ∃ C, r.label = .fg (.attest C (some a))

/-- The same invariant is consumed at event, duty, release-prefix and gossip-prefix stages.
No queue is asserted empty here. Root and message provenance live alongside the FG store. -/
def Represents (observedAt : Time) (self : Fin (Fintype.card V))
    (st : State (runWire (E := E) A hn))
    (seen : List (ShapeObj (Fintype.card V) Empty I B)) : Prop :=
  st.self = self ∧ st.node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload ∧
  (∀ C ∈ st.node.fg.tree, C.RootOk (digest A fin rho hn D)) ∧
  (∀ C ∈ st.node.fg.tree, C.root ≠ (A.runtime (pubOf E) hn).genesisRoot →
    blockObj (runWire (E := E) A hn) C ∈
      Model.closure (P := Model.protoOf (compiled (shapeFamily A fin)) E) seen) ∧
  (∀ m, (nodeAC (E := E) A hn).holdsMsg st.node.ac m →
    (runWire (E := E) A hn).signer m ∈ honestAt A fin rho observedAt →
    ∃ i, EmittedThrough A fin rho hn D i ((runWire (E := E) A hn).signer m) m)

/-- Closure is an obligation, not an invariant assumed true by definition. All stage prefixes,
including saturated list prefixes, and every consumed handler frame are covered. -/
structure RepresentationClosure : Prop where
  initial : rho.ExecutionValid → ∀ v, v ∉ rho.faultyAt 0 →
    Represents A fin rho hn D 0 (rho.ownKey v) (engineState A fin rho hn v 0)
      (rho.stateBefore 0 v).seen
  boundary : rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
    v ∉ rho.faultyAt (rho.cutTime i) →
    Represents A fin rho hn D (rho.cutTime i) (rho.ownKey v) (engineState A fin rho hn v i)
      (rho.stateBefore i v).seen
  within : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ stage,
    let nd := stageNode A fin rho i ev.node stage
    Represents A fin rho hn D ev.time (rho.ownKey ev.node) (nd.st.1 hn) nd.seen
  handler : rho.ExecutionValid → ∀ k ℓ, (simTraceNodeAt A fin rho hn D).label k = some (.ac ℓ) →
    ((simTraceNodeAt A fin rho hn D).state ((simTraceNodeAt A fin rho hn D).node k) k).fg.Reachable
      (nodeAC (E := E) A hn).genesisPayload ∧
    FrameOK ℓ.frame

/-- Candidate refusals are permitted. Protection of a relevant signing is derived from
its history and the prefix's own-signer provenance, not required for every FG candidate. -/
structure PublicationLaws : Prop where
  signing_conflicts : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ a b,
    SignedThrough A fin rho hn D i (rho.ownKey ev.node) a →
    SignedThrough A fin rho hn D i (rho.ownKey ev.node) b →
    A.conflicts (Fintype.card V)
      (.mk (.signed a.val .poll) (.data ((runWire (E := E) A hn).encodeAtt a)) [])
      (.mk (.signed b.val .poll) (.data ((runWire (E := E) A hn).encodeAtt b)) []) = false
  prefix_signatures : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ stage o,
    o ∈ Model.closure (stageNode A fin rho i ev.node stage).seen →
    rho.signerOf o = some ev.node →
    ∀ a, o = .mk (.signed a.val .poll) (.data ((runWire (E := E) A hn).encodeAtt a)) [] →
      SignedThrough A fin rho hn D i (rho.ownKey ev.node) a
  conflict_domain : ∀ a o,
    let c := Model.Obj.mk (.signed a.val .poll) (.data ((runWire (E := E) A hn).encodeAtt a)) []
    A.conflicts (Fintype.card V) c o = true ∨ A.conflicts (Fintype.card V) o c = true →
    ∃ b, o = .mk (.signed b.val .poll) (.data ((runWire (E := E) A hn).encodeAtt b)) []
  signed_candidate : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ r C a,
    r ∈ eventRecords A fin rho hn D i → r.label = .fg (.attest C (some a)) →
    a.val = rho.ownKey ev.node ∧ ∃ j d,
      (eventDuties A fin rho i)[j]? = some d ∧
      let P := Model.protoOf (compiled (shapeFamily A fin)) E
      let nd := stageNode A fin rho i ev.node (.duty j)
      Model.Obj.mk (.signed a.val .poll) (.data ((runWire (E := E) A hn).encodeAtt a)) [] ∈
        rho.signedCandidate ev.node d (P.act nd.st d).2
  gossip_ready : ∀ i ev, rho.ExecutionValid → rho.events[i]? = some ev → ∀ k c,
    let P := Model.protoOf (compiled (shapeFamily A fin)) E
    let nd := stageNode A fin rho i ev.node (.duty (eventDuties A fin rho i).length)
    (Model.gossipCandidates P nd.st ev.time)[k]? = some c →
    let pre := stageNode A fin rho i ev.node (.gossip k)
    Model.releasable pre.seen c = true ∧
    Model.protects P (rho.ownKey ev.node) pre.seen c = true ∧
    P.dependencies.ready (Model.closure pre.seen) c = true
  admission : rho.ExecutionValid → ∀ y k m, (simTraceNodeAt A fin rho hn D).SendOrAdmitAt y k m →
    y ∈ honestAt A fin rho ((simTraceNodeAt A fin rho hn D).time k) →
    ∃ i, cutMapNode A fin rho hn D i ≤ k ∧ k < cutMapNode A fin rho hn D (i + 1) ∧
      ∃ j, ((simTraceNodeAt A fin rho hn D).time k, m) ∈
        (((stageNode A fin rho i (rho.key y) (.duty j)).st.1 hn).msgForwards)
  forwarding : rho.ExecutionValid → ∀ y k C,
    (simTraceNodeAt A fin rho hn D).AcceptAt y k C → (simTraceNodeAt A fin rho hn D).pos k = 0 →
    y ∈ honestAt A fin rho ((simTraceNodeAt A fin rho hn D).time k) →
    ∃ i j, cutMapNode A fin rho hn D i ≤ k ∧ k < cutMapNode A fin rho hn D (i + 1) ∧
      blockObj (runWire (E := E) A hn) C ∈ Model.closure
        (stageNode A fin rho i (rho.key y) (.duty j)).seen

/-- These are named, non-circular supplier obligations. No final simulation witness is an input.
Requirements and collision transport are deliberately absent from local-run/publication supply. -/
structure SimulationSuppliers : Prop where
  wire : WireLaws (runWire (E := E) A hn)
  run : WireRunLaws A fin rho
  restart : RestartSilent (nodeAC (E := E) A hn)
  grid : (A.skeleton (pubOf E)).grid = ⟨4 * (pubOf E).ΔAC, by
    have := (pubOf E).ΔAC_pos; positivity⟩
  proposer_policy : ∀ s, A.proposerSel (pubOf E) s = .sized 1
  order : A.order = [.poll, .poll, .pollPropose, .propose, .poll, .poll]
  deliver_order : A.deliverOrder = [.poll]
  genesis : ((params (pubOf E) hn (A.runtime (pubOf E) hn).genesisRoot
    (A.runtime (pubOf E) hn).δt).genesisBlock
      (nodeAC (E := E) A hn).genesisPayload).RootOk (digest A fin rho hn D)
  header_shape : ∀ C, (runWire (E := E) A hn).headerOf C =
    ⟨(runWire (E := E) A hn).parentRef C.parent, C.slot, C.input,
      (runWire (E := E) A hn).encodeInfo C.fgPayload C.acPayload⟩
  parent_genesis : (runWire (E := E) A hn).parentRef
    (some (A.runtime (pubOf E) hn).genesisRoot) = .root
  parent_tag : ∀ d, (runWire (E := E) A hn).parentRef
    (some (D.tag (A.runtime (pubOf E) hn).genesisRoot d)) = .digest d
  message_not_attestation : ∀ m a, (runWire (E := E) A hn).encodeMsg m ≠
    (runWire (E := E) A hn).encodeAtt a
  received : rho.ExecutionValid → ∀ (i : Nat) v o t,
    rho.events[i]? = some (Model.Event.deliver v o t) →
    ∀ part ∈ o.parts, ∀ e,
      (runWire (E := E) A hn).canonEvent (Model.digests rho.hash o) part = some e →
      Node.WireOK (digest A fin rho hn D) e ∧
        (∀ C, e = .block C → C.proposer = proposer A fin rho hn C.slot)
  original_candidates : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ j d m,
    (eventDuties A fin rho i)[j]? = some d →
    let P := Model.protoOf (compiled (shapeFamily A fin)) E
    let nd := stageNode A fin rho i ev.node (.duty j)
    msgObj (runWire (E := E) A hn) m ∈ rho.signedCandidate ev.node d (P.act nd.st d).2 →
    EmittedThrough A fin rho hn D i (rho.ownKey ev.node) m
  gossip_originals : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ m,
    let P := Model.protoOf (compiled (shapeFamily A fin)) E
    let nd := stageNode A fin rho i ev.node (.duty (eventDuties A fin rho i).length)
    msgObj (runWire (E := E) A hn) m ∈ Model.gossipCandidates P nd.st ev.time →
    EmittedThrough A fin rho hn D i (rho.ownKey ev.node) m
  queued_messages : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ stage m,
    (runWire (E := E) A hn).encodeMsg m ∈
      ((stageNode A fin rho i ev.node stage).st.1 hn).outbox →
    EmittedThrough A fin rho hn D i (rho.ownKey ev.node) m
  proposal_payload : rho.ExecutionValid → ∀ i ev, rho.events[i]? = some ev → ∀ j s hs h cs,
    (eventDuties A fin rho i)[j]? = some (.propose s hs) →
    let P := Model.protoOf (compiled (shapeFamily A fin)) E
    let nd := stageNode A fin rho i ev.node (.duty j)
    (.item h, cs) ∈ (P.act nd.st (.propose s hs)).2 →
    ∀ o ∈ cs, o ∈ Model.closure nd.seen
  admission : AdmissionLaws (nodeAC (E := E) A hn) (runWire (E := E) A hn).payloadMsgs
    (CallDomain A fin rho hn D)
  signer : EmissionSigner (runWire (E := E) A hn) (CallDomain A fin rho hn D)
  emitted_admitted : ∀ self s Φ t c, CallDomain A fin rho hn D self s Φ t c →
    ∀ e ∈ ((nodeAC (E := E) A hn).step self s Φ t c).2,
      ¬ (nodeAC (E := E) A hn).holdsMsg s e.msg ∧
        (nodeAC (E := E) A hn).holdsMsg ((nodeAC (E := E) A hn).step self s Φ t c).1 e.msg
  own_payload : rho.ExecutionValid → ∀ y k C, (simTraceNodeAt A fin rho hn D).OwnBlockAt y k C →
    (nodeAC (E := E) A hn).validPayload C
  representation : RepresentationClosure A fin rho hn D
  publication : PublicationLaws A fin rho hn D

def SimulationObligation : Prop := SimulationSuppliers A fin rho hn D →
  EngineSimulatesNodeAt A fin rho hn D

def CollisionObligation : Prop := CollisionLaws A fin rho hn D →
  NoCollTransportNodeAt A fin rho hn D

/-- Full Requirements belongs only at the component projection which consumes it.
Genesis and collision freedom are additional FG projection inputs, not codec consequences. -/
def ProjectionExports : Prop := ProjectionRequirements (nodeAC (E := E) A hn) →
  NodeRunAt A fin rho hn D (simTraceNodeAt A fin rho hn D) →
  Compose.NoCollRun (digest A fin rho hn D) (simTraceNodeAt A fin rho hn D) →
    Growing.ACLocalRun (nodeAC (E := E) A hn) (honestAt A fin rho)
      ((simTraceNodeAt A fin rho hn D).HonestBlocksAt (honestAt A fin rho))
      (simTraceNodeAt A fin rho hn D).projAC ∧
    Growing.FGLocalRun (nodeAC (E := E) A hn).genesisPayload (honestAt A fin rho)
      ((simTraceNodeAt A fin rho hn D).HonestBlocksAt (honestAt A fin rho))
      (simTraceNodeAt A fin rho hn D).projFG

/-- Each export is independently available; no collision premise leaks into these outputs. -/
def IndependentExports : Prop := SimulationSuppliers A fin rho hn D →
  LocalRunExport A fin rho hn D ∧ FGReachExport A fin rho hn ∧ ReadExport A fin rho hn ∧
  OutputValidExport A fin rho hn ∧ NestedExport A fin rho hn ∧ FinalMonotoneExport A fin rho

end Consensus.Goldilocks.NodeEngine
