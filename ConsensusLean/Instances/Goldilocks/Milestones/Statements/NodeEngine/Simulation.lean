module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.NodeEngine.Wire
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Spec.Shape.Run

@[expose] public section
namespace Consensus.Goldilocks.NodeEngine
open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V) (D : TraceData)

/-- The existing growing record supplies all 21 fields, with no new fixed-honesty version. -/
structure NodeRunAt (tr : RunTrace (nodeAC (E := E) A hn)) : Prop
    extends Growing.LocalRun (proposer A fin rho hn) (digest A fin rho hn D)
      (honestAt A fin rho) (runWire (E := E) A hn).signer tr
      (fun _ => (nodeAC (E := E) A hn).initial) where
  genesis_root : ((params (pubOf E) hn (A.runtime (pubOf E) hn).genesisRoot
    (A.runtime (pubOf E) hn).δt).genesisBlock
      (nodeAC (E := E) A hn).genesisPayload).RootOk (digest A fin rho hn D)
  carried_message : ∀ y k C, y ∈ honestAt A fin rho (tr.time k) → tr.BlockCallAt y k C →
    ∀ m ∈ (runWire (E := E) A hn).payloadMsgs C.acPayload,
      (runWire (E := E) A hn).signer m ∈ honestAt A fin rho (tr.time k) →
      ∃ j < k, tr.EmitAt ((runWire (E := E) A hn).signer m) j m

inductive DeliverySeq (tr : RunTrace (nodeAC (E := E) A hn)) (hs : List (Header I × Nat))
    (y : Fin (Fintype.card V)) (t : Time) :
    List (ShapeObj (Fintype.card V) Empty I B) → Nat → Nat → Prop
  | nil (j) : DeliverySeq tr hs y t [] j j
  | event {o os j j'} (e : Node.Event (nodeAC (E := E) A hn)) :
      (runWire (E := E) A hn).canonEvent hs o = some e →
      tr.GroupAt (proposer A fin rho hn) (digest A fin rho hn D) y j t e →
      DeliverySeq tr hs y t os (j + (Node.exec (proposer A fin rho hn)
        (digest A fin rho hn D) y (tr.state y j) t e).2.length) j' →
      DeliverySeq tr hs y t (o :: os) j j'
  | drop {o os j j'} : (runWire (E := E) A hn).canonEvent hs o = none →
      DeliverySeq tr hs y t os j j' → DeliverySeq tr hs y t (o :: os) j j'
  | noCut {o os j j'} (e : Node.Event (nodeAC (E := E) A hn)) :
      (runWire (E := E) A hn).canonEvent hs o = some e →
      (Node.exec (proposer A fin rho hn) (digest A fin rho hn D) y (tr.state y j) t e).2 = [] →
      DeliverySeq tr hs y t os j j' → DeliverySeq tr hs y t (o :: os) j j'

def RelayedNode (v : V) (o : ShapeObj (Fintype.card V) Empty I B) (t : Time) : Prop :=
  ∃ cs, o ∈ cs ∧ rho.releases v (.mk .none (.data (runWire (E := E) A hn).relayBody) cs) t

/-- Full growing correspondence, not merely one-way state commutation. -/
structure SimulatesNodeAt (tr : RunTrace (nodeAC (E := E) A hn)) (ι : Nat → Nat) : Prop where
  run : NodeRunAt A fin rho hn D tr
  zero : ι 0 = 0
  mono : Monotone ι
  covered : ∀ k, tr.label k ≠ none →
    ∃ i < rho.events.length, ι i ≤ k ∧ k < ι (i + 1)
  state : ∀ v i, i ≤ rho.events.length → v ∉ rho.faultyAt (rho.cutTime i) →
    (engineState A fin rho hn v i).node = tr.state (rho.ownKey v) (ι i)
  now : ∀ v i, (engineState A fin rho hn v i).now = lastClockNode A fin rho v i
  tick_public : ∀ v i t, rho.events[i]? = some (.tick v t) →
    (params (pubOf E) hn (A.runtime (pubOf E) hn).genesisRoot
      (A.runtime (pubOf E) hn).δt).IsPublic t →
    tr.GroupAt (proposer A fin rho hn) (digest A fin rho hn D) (rho.ownKey v) (ι i) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
    ι (i + 1) = ι i + (Node.exec (proposer A fin rho hn) (digest A fin rho hn D)
      (rho.ownKey v) (tr.state (rho.ownKey v) (ι i)) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length
  tick_other : ∀ v i t, rho.events[i]? = some (.tick v t) →
    ¬ (params (pubOf E) hn (A.runtime (pubOf E) hn).genesisRoot
      (A.runtime (pubOf E) hn).δt).IsPublic t → ι (i + 1) = ι i
  deliver : ∀ v i o t, rho.events[i]? = some (.deliver v o t) →
    DeliverySeq A fin rho hn D tr (Model.digests rho.hash o) (rho.ownKey v) t
      o.parts (ι i) (ι (i + 1))
  restart : ∀ v i t, rho.events[i]? = some (.restart v t) →
    tr.GroupAt (proposer A fin rho hn) (digest A fin rho hn D) (rho.ownKey v) (ι i) t .restart ∧
    ι (i + 1) = ι i + (Node.exec (proposer A fin rho hn) (digest A fin rho hn D) (rho.ownKey v)
      (tr.state (rho.ownKey v) (ι i)) t .restart).2.length
  awake_of : ∀ y t, y ∈ honestAt A fin rho t → tr.awake y t →
    E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon
  awake_to : ∀ y t, y ∈ honestAt A fin rho t → E.awake (rho.key y) t = true →
    0 ≤ t → tr.InHorizon t → tr.awake y t
  block_released : ∀ y k C, y ∈ honestAt A fin rho (tr.time k) → tr.OwnBlockAt y k C →
    rho.releases (rho.key y) (blockObj (runWire (E := E) A hn) C) (tr.time k)
  message_released : ∀ y k m, y ∈ honestAt A fin rho (tr.time k) → tr.EmitAt y k m →
    rho.releases (rho.key y) (msgObj (runWire (E := E) A hn) m) (tr.time k)
  att_released : ∀ y k a, y ∈ honestAt A fin rho (tr.time k) → tr.SignAt y k a →
    rho.releases (rho.key y) (.mk (.signed a.val .poll)
      (.data ((runWire (E := E) A hn).encodeAtt a)) []) (tr.time k)
  block_relayed : ∀ y k C, y ∈ honestAt A fin rho (tr.time k) →
    tr.AcceptAt y k C → tr.pos k = 0 →
    RelayedNode A fin rho hn (rho.key y) (blockObj (runWire (E := E) A hn) C) (tr.time k)
  message_forwarded : ∀ y k m, y ∈ honestAt A fin rho (tr.time k) → tr.SendOrAdmitAt y k m →
    let o := Model.Obj.mk (.signed y .poll)
      (.data ((runWire (E := E) A hn).msgForwardBody (tr.time k) m))
      [msgObj (runWire (E := E) A hn) m]
    ∃ i, ι i ≤ k ∧ k < ι (i + 1) ∧ rho.SendsAt (rho.key y) i (tr.time k) ∧
      o ∈ rho.releasesAt i ∧ ∀ j < i, o ∉ rho.releasesAt j
  att_relayed : ∀ y k a, y ∈ honestAt A fin rho (tr.time k) → tr.AttCallAt y k a → tr.pos k = 0 →
    RelayedNode A fin rho hn (rho.key y)
      (.mk (.signed a.val .poll) (.data ((runWire (E := E) A hn).encodeAtt a)) []) (tr.time k)

/-- The target is the defined canonical growing trace and its actual cut map. -/
def EngineSimulatesNodeAt : Prop := rho.ExecutionValid →
  SimulatesNodeAt A fin rho hn D (simTraceNodeAt A fin rho hn D) (cutMapNode A fin rho hn D)

def NoCollTransportNodeAt : Prop := rho.ExecutionValid → ¬ rho.HashCollision →
  Compose.NoCollRun (digest A fin rho hn D) (simTraceNodeAt A fin rho hn D)

/-- Header/root facts missing from codec retracts, including refused block occurrences. -/
structure CollisionLaws : Prop where
  tag_injective : Function.Injective (D.tag (A.runtime (pubOf E) hn).genesisRoot)
  tag_ne_genesis : ∀ d, D.tag (A.runtime (pubOf E) hn).genesisRoot d ≠
    (A.runtime (pubOf E) hn).genesisRoot
  occurrence : rho.ExecutionValid → ∀ C, (simTraceNodeAt A fin rho hn D).Occurs C →
    C.parent ≠ none ∧ rho.ObservedItem ((runWire (E := E) A hn).headerOf C)
  header_digest : ∀ C, C.parent ≠ none →
    digest A fin rho hn D C.parent C.slot C.input C.fgPayload C.acPayload =
      D.tag (A.runtime (pubOf E) hn).genesisRoot (rho.hash ((runWire (E := E) A hn).headerOf C))
  header_contents : ∀ C C', C.parent ≠ none → C'.parent ≠ none →
    (runWire (E := E) A hn).headerOf C = (runWire (E := E) A hn).headerOf C' →
      C.parent = C'.parent ∧ C.slot = C'.slot ∧
      C.input = C'.input ∧ C.fgPayload = C'.fgPayload ∧ C.acPayload = C'.acPayload

/-- The real stored-clock read domain: never a freely chosen or empty Reach predicate. -/
def ReachClock (st : NodeState (nodeAC (E := E) A hn)) (t : Time) : Prop :=
  ∃ v i, rho.ExecutionValid ∧ i ≤ rho.events.length ∧
    v ∉ rho.faultyAt (rho.cutTime i) ∧ st = (engineState A fin rho hn v i).node ∧
    t = (engineState A fin rho hn v i).now

/-- Local-run export is independent of collision transport, Requirements and tip supply. -/
def LocalRunExport : Prop := rho.ExecutionValid →
  Growing.LocalRun (proposer A fin rho hn) (digest A fin rho hn D) (honestAt A fin rho)
    (runWire (E := E) A hn).signer (simTraceNodeAt A fin rho hn D)
    (fun _ => (nodeAC (E := E) A hn).initial)

/-- Reachable FG reads need no codec injectivity or collision/regime premise. -/
def FGReachExport : Prop := rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
  v ∉ rho.faultyAt (rho.cutTime i) →
    (engineState A fin rho hn v i).node.fg.Reachable (nodeAC (E := E) A hn).genesisPayload

def ReadExport : Prop := rho.ExecutionValid → ∀ v i g, i ≤ rho.events.length →
  (chainTrace rho).read g v i = outOf (runWire (E := E) A hn) (engineState A fin rho hn v i) (fin g)

/-- Only the output contracts which read AC tips take their separate, genuine Reach supplier. -/
def OutputValidExport : Prop := rho.ExecutionValid →
  StoredClockTips (nodeAC (E := E) A hn) (ReachClock A fin rho hn) → ∀ g, OutputValid rho g

def NestedExport : Prop := rho.ExecutionValid →
  StoredClockTips (nodeAC (E := E) A hn) (ReachClock A fin rho hn) →
  ∀ f c, fin f = true → fin c = false → (chainTrace rho).Nested f c

def FinalMonotoneExport : Prop := rho.ExecutionValid →
  ∀ g, fin g = true → (chainTrace rho).Monotone g 0

end Consensus.Goldilocks.NodeEngine
