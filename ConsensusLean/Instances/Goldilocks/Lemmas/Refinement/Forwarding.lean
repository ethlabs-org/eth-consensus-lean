module
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement

public section

/-! # Publication contracts for the revised publisher

OPEN implementation arguments, not paper proofs. The paper's forwarding rule motivates these
interfaces but does not prove engine candidate ordering or signed-object provenance. In
particular the current unsigned publisher does not instantiate these contracts. The Accepted
assembly must construct an implementation and discharge every field, never assume this bundle
as an additional regime premise. Parameters remain explicit until run-selected simulation lands.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model

/-- Revised publisher state, separate from the current unsigned implementation. The map
survives restarts; pending wrappers are drained in acceptance order before the event ends.
OPEN implementation: connecting this state to `State`, actual duties and own proposals. -/
structure ForwardingState (n : Nat) where
  wrappers : Nat → Option (Wire n)
  pending : List (Wire n)

/-- Revised publication transition: remember the exact wrapper and append it to the same-event
drain. Resolve the parent from the durable map, never from a raw parent object. A missing
non-genesis parent fails explicitly; proving this cannot occur on actual acceptance is OPEN.
Callers must establish canonical acceptance first. This is not an installed engine handler. -/
def ForwardingState.enqueue {sp : SA.SAParams} (st : ForwardingState sp.n)
    (origin : Fin sp.n) (t : Time) (B : Blk sp) :
    Option (ForwardingState sp.n) := do
  let root ← B.parent
  let parent ← if root = sp.genesisRoot then some none
    else (st.wrappers root).map some
  let o := forwardObj sp origin t parent B
  return ⟨Function.update st.wrappers B.root (some o), st.pending ++ [o]⟩

/-- Drain the entire event queue in one ordered engine release batch, retaining the durable
map and clearing only the queue. Parent wrappers queued earlier become available to later
guards through `releaseAll`'s seen update. Integration as an executed signed batch is OPEN. -/
noncomputable def ForwardingState.drain {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (st : ForwardingState (Fintype.card V)) (origin : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (family S)) E)) :
    ForwardingState (Fintype.card V) ×
      (Model.Node (protoOf (compiled (family S)) E) × List (Wire (Fintype.card V))) :=
  (⟨st.wrappers, []⟩,
    Model.releaseAll (protoOf (compiled (family S)) E) rho.hash origin nd st.pending)

/-- A drain clears pending traffic but keeps the canonical wrapper map. This is a local
producer-state fact, not a release guarantee or a theorem about engine restarts. -/
theorem ForwardingState.drain_persistent {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (st : ForwardingState (Fintype.card V)) (origin : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (family S)) E)) :
    (st.drain S rho origin nd).1.wrappers = st.wrappers ∧
      (st.drain S rho origin nd).1.pending = [] := by
  exact ⟨rfl, rfl⟩

/-- One successful candidate of a release batch. `batch` orders actual batches within an event;
`index` names the candidate, including candidates rejected earlier in the batch. -/
structure Publication {pub : Public} {O : Type} (P : Protocol pub O) where
  event : Nat
  batch : Nat
  index : Nat
  origin : Key pub
  before : Model.Node P
  candidates : List P.Object
  object : P.Object
  candidate : candidates[index]? = some object

/-- Lexicographic release order; equal timestamps need not imply equal occurrences. -/
def Publication.Before {pub : Public} {O : Type} {P : Protocol pub O}
    (a b : Publication P) : Prop :=
  a.event < b.event ∨ a.event = b.event ∧
    (a.batch < b.batch ∨ a.batch = b.batch ∧ a.index < b.index)

/-- The revised publisher's linkage to actual execution. `actual` must be implemented from
executed duty/release batches, not chosen to make publication claims vacuous. The concrete
instantiation is OPEN until the signed publisher replaces unsigned gossip. -/
structure PublisherExecution {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) where
  actual : Publication (protoOf (compiled (family S)) E) → Prop
  eventTime : Nat → Time
  actual_event : ∀ r, actual r → rho.SendsAt (rho.key r.origin) r.event (eventTime r.event)
  actual_success : ∀ r, actual r →
    let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true ∧
      Model.protects (protoOf (compiled (family S)) E) r.origin nd.seen r.object = true ∧
      (protoOf (compiled (family S)) E).dependencies.ready (Model.closure nd.seen) r.object = true
  actual_release : ∀ r, actual r → r.object ∈ rho.releasesAt r.event

/-- A batch input and candidate list, before applying its release guard. -/
structure ReleaseBatch {pub : Public} {O : Type} (P : Protocol pub O) where
  before : Model.Node P
  candidates : List P.Object

/-- Enumerate actual selected duty batches, threading the same `dutyStep` states as the
engine. Empty/unselected duties retain their ordinal position as an empty batch. -/
noncomputable def dutyBatches {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (v : V) :
    Model.Node (protoOf F E) → List (protoOf F E).Duty → List (ReleaseBatch (protoOf F E))
  | _, [] => []
  | nd, d :: ds =>
    let a := (protoOf F E).act nd.st d
    let batch := if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
      ⟨⟨a.1, nd.seen⟩, rho.signedCandidate v d a.2⟩ else ⟨nd, []⟩
    batch :: dutyBatches rho v (rho.dutyStep v nd d).1 ds

/-- Actual event batches, including the final gossip batch. No synthetic batch labels are
allowed: publication indices must select an entry in this list. -/
noncomputable def eventBatches {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : Family O} (rho : Model.Run F E) (i : Nat) :
    List (ReleaseBatch (protoOf F E)) :=
  match rho.events[i]? with
  | some (.tick v t) =>
    let nd := rho.stateBefore i v
    let start := ⟨(protoOf F E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
    if E.awake v t then
      let r := rho.runDuties v start ((protoOf F E).duties t)
      dutyBatches rho v start ((protoOf F E).duties t) ++
        [⟨r.1, gossipCandidates (protoOf F E) r.1.st t⟩]
    else []
  | some (.deliver v o t) =>
    let nd := rho.stateBefore i v
    let start := ⟨(protoOf F E).process nd.st o (digests rho.hash o), nd.seen ++ [o]⟩
    let r := rho.runDuties v start ((protoOf F E).deliverDuties t)
    dutyBatches rho v start ((protoOf F E).deliverDuties t) ++
      [⟨r.1, gossipCandidates (protoOf F E) r.1.st t⟩]
  | _ => []

/-- A real candidate prefix: ties both its state and candidates to the engine event. -/
def ExecutedPublication {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E)
    (r : Publication (protoOf (compiled (family S)) E)) : Prop :=
  (eventBatches rho r.event)[r.batch]? = some ⟨r.before, r.candidates⟩ ∧
  ∃ t, rho.SendsAt (rho.key r.origin) r.event t

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
  (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (cutMap : Nat → Nat)
  (pubExec : PublisherExecution S rho)

/-- OPEN: honest signed publication must originate in actual acceptance at the stamp.
Argument: only the acceptance handler queues these candidates; authentication rules out
other honest origins. This must be proved about the revised producer, not the parser. -/
def ForwardOrigin : Prop :=
  ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest → ∀ t p B,
    r.object = forwardObj (S.params (pubOf E) hn) r.origin t p B →
    ∃ k, tr.AcceptAt r.origin k B ∧ tr.time k = t ∧
      k < cutMap (r.event + 1) ∧ t = pubExec.eventTime r.event

/-- OPEN: acceptance queues and drains a wrapper in the same event, including own proposals.
The current unsigned producer cannot satisfy this contract. -/
def ForwardAtAcceptance : Prop :=
  ∀ x ∈ honestKeys S rho, ∀ k B, tr.AcceptAt x k B →
    ∃ r p, pubExec.actual r ∧ r.origin = x ∧
      cutMap r.event ≤ k ∧ k < cutMap (r.event + 1) ∧
      pubExec.eventTime r.event = tr.time k ∧
      r.object = forwardObj (S.params (pubOf E) hn) x (tr.time k) p B ∧
      decodeForward (S.params (pubOf E) hn) (Model.digests rho.hash r.object) r.object =
        some (x, tr.time k, p, B)

/-- OPEN: parent references are taken from the origin's previously released wrappers;
same-event publication order is candidate order, not strict timestamp order. -/
def ForwardParentEarlier : Prop :=
  ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest → ∀ t p B,
    r.object = forwardObj (S.params (pubOf E) hn) r.origin t (some p) B →
    ∃ q A pt pp ka kb, pubExec.actual q ∧ Publication.Before q r ∧ q.origin = r.origin ∧
      q.object = p ∧ p = forwardObj (S.params (pubOf E) hn) r.origin pt pp A ∧
      B.parent = some A.root ∧ tr.AcceptAt r.origin ka A ∧ tr.AcceptAt r.origin kb B ∧
      ka < kb ∧ tr.time ka = pt ∧ tr.time kb = t

/-- OPEN: recursive receipt processing turns prior authenticated holdings into prior calls;
own publications instead use actual acceptance. Refused calls do not establish acceptance. -/
def ForwardHeldProcessed : Prop :=
  ∀ y ∈ honestKeys S rho, ∀ i x t p B,
    x ∈ honestKeys S rho →
    forwardObj (S.params (pubOf E) hn) x t p B ∈
      Model.closure (rho.stateBefore i (rho.key y)).seen →
    ∃ k < cutMap i, t ≤ tr.time k ∧
      (tr.BlockCallAt y k B ∨ y = x ∧ tr.AcceptAt y k B)

/-- OPEN: accepted canonical objects and exact parent wrappers are in the publisher's seen
closure at the actual candidate prefix; signing and dependency guards do not suppress it. -/
def AcceptedObjectsSeen : Prop :=
  ∀ r, pubExec.actual r → rho.key r.origin ∈ rho.honest →
    let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    ∀ o ∈ r.object.carried, o ∈ Model.closure nd.seen

/-- The five obligations the concrete revised publisher must discharge. OPEN: no instance for
the current unsigned publisher is supplied, and this is not a new Accepted assumption. -/
structure ForwardingContracts : Prop where
  executed : ∀ r, pubExec.actual r → ExecutedPublication S rho r
  /-- Completeness prevents selecting only convenient successful publications. Every actual
  executed candidate passing all three guards belongs to the publication relation. -/
  complete : ∀ r, ExecutedPublication S rho r →
    let nd := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true →
    Model.protects (protoOf (compiled (family S)) E) r.origin nd.seen r.object = true →
    (protoOf (compiled (family S)) E).dependencies.ready (Model.closure nd.seen) r.object = true →
    pubExec.actual r
  origin : ForwardOrigin S rho hn tr cutMap pubExec
  atAcceptance : ForwardAtAcceptance S rho hn tr cutMap pubExec
  parentEarlier : ForwardParentEarlier S rho hn tr pubExec
  heldProcessed : ForwardHeldProcessed S rho hn tr cutMap
  objectsSeen : AcceptedObjectsSeen S rho pubExec

end Consensus.Goldilocks.Refinement
