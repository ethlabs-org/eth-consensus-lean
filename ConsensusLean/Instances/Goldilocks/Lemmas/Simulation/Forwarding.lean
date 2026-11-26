module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingWrappers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Lemmas.Model.Candidates
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox

public section

/-! # Publication contracts for the revised publisher

OPEN implementation arguments, not paper proofs. The paper's forwarding rule motivates these
interfaces but does not prove engine candidate ordering or signed-object provenance. In
particular installing the signed publisher does not prove these contracts. The obligations
assembly must construct an implementation and discharge each contract, never assume one as an
additional regime premise. Parameters remain explicit until run-selected simulation lands.
-/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape Blocks
open Consensus.Model

variable {binding : VoteBinding}

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

/-- The publisher's linkage to actual execution. `actual` must be implemented from executed
duty/release batches, not chosen to make publication claims vacuous. `publisherExecution`
below supplies that linkage without assuming any acceptance provenance. -/
structure PublisherExecution {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) where
  actual : Publication (protoOf (compiled (goldilocks S)) E) → Prop
  eventTime : Nat → Time
  actual_event : ∀ r, actual r → rho.SendsAt (rho.key r.origin) r.event (eventTime r.event)
  actual_success : ∀ r, actual r →
    let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true ∧
      (protoOf (compiled (goldilocks S)) E).dependencies.ready (Model.closure nd.seen) r.object
          =
          true
  actual_release : ∀ r, actual r → r.object ∈ rho.releasesAt r.event

/-- A batch input and candidate list, before applying its release guard. -/
structure ReleaseBatch {pub : Public} {O : Type} (P : Protocol pub O) where
  before : Model.Node P
  candidates : List P.Object

/-- Enumerate actual selected duty batches, threading the same `dutyStep` states as the
engine. Empty/unselected duties retain their ordinal position as an empty batch. -/
noncomputable def dutyBatches {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V) :
    Model.Node (protoOf F E) → List (protoOf F E).Duty → List (ReleaseBatch (protoOf F E))
  | _, [] => []
  | nd, d :: ds =>
    let a := (protoOf F E).act nd.st d
    let batch := if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
      ⟨⟨a.1, nd.seen⟩, rho.signedCandidate v d a.2⟩ else ⟨nd, []⟩
    batch :: dutyBatches rho v (rho.dutyStep v nd d).1 ds

/-- No duties produce no release batches. -/
theorem dutyBatches_nil {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V)
    (nd : Model.Node (protoOf F E)) : dutyBatches rho v nd [] = [] := by
  rfl

/-- The next batch retains its duty position even when unselected; later batches start
from the actual duty-step result. -/
theorem dutyBatches_cons {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V)
    (nd : Model.Node (protoOf F E)) (d : (protoOf F E).Duty)
    (ds : List (protoOf F E).Duty) :
    dutyBatches rho v nd (d :: ds) =
      (let a := (protoOf F E).act nd.st d
       let batch : ReleaseBatch (protoOf F E) :=
         if rho.ownKey v ∈ rho.sel ((protoOf F E).role d) then
           ⟨⟨a.1, nd.seen⟩, rho.signedCandidate v d a.2⟩ else ⟨nd, []⟩
       batch :: dutyBatches rho v (rho.dutyStep v nd d).1 ds) := by
  rfl

/-- Actual event batches, including the final gossip batch. No synthetic batch labels are
allowed: publication indices must select an entry in this list. -/
noncomputable def eventBatches {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (i : Nat) :
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

/-- Characterization by the actual event, without exposing the implementation body. -/
theorem eventBatches_eq {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (i : Nat) :
    eventBatches rho i = (match rho.events[i]? with
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
      | _ => []) := by
  rfl

/-- A real candidate prefix: ties both its state and candidates to the engine event. -/
def ExecutedPublication {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (r : Publication (protoOf (compiled (goldilocks S)) E)) : Prop :=
  (eventBatches rho r.event)[r.batch]? = some ⟨r.before, r.candidates⟩ ∧
  ∃ t, rho.SendsAt (rho.key r.origin) r.event t

/-- Characterize the actual batch and sending event without exposing the definition. -/
theorem executedPublication_iff {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (r : Publication (protoOf (compiled (goldilocks S)) E)) :
    ExecutedPublication S rho r ↔
      (eventBatches rho r.event)[r.batch]? = some ⟨r.before, r.candidates⟩ ∧
        ∃ t, rho.SendsAt (rho.key r.origin) r.event t := by rfl

/-- A successful candidate at its actual prefix occurs in the batch output. Rejected
earlier candidates still count towards the index; induction follows the engine's guard,
so the prefix state includes exactly the successful earlier releases. -/
private theorem releaseAll_candidate_success {pub : Public} {O : Type} (P : Protocol pub O)
    (hash : P.Item → Nat) (origin : Key pub) (nd : Model.Node P)
    (cs : List P.Object) (i : Nat) (o : P.Object)
    (hi : cs[i]? = some o)
    (hs : let pre := (Model.releaseAll P hash origin nd (cs.take i)).1
      Model.releasable pre.seen o = true ∧
        P.dependencies.ready (Model.closure pre.seen) o = true) :
    o ∈ (Model.releaseAll P hash origin nd cs).2 := by
  induction cs generalizing nd i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst c
      simp only [List.take_zero, Model.releaseAll] at hs
      simp only [Model.releaseAll, hs.1, hs.2, Bool.and_self, ↓reduceIte]
      exact List.mem_cons_self
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.take_succ_cons, Model.releaseAll] at hs ⊢
      split at *
      · rename_i h
        simp only [h, ↓reduceIte]
        exact List.mem_cons_of_mem _ (ih _ i hi hs)
      · rename_i h
        simp only [h]
        exact ih _ i hi hs

/-- A batch drains completely when its guards hold against the immutable candidate
prefix. Earlier candidates become actual holdings by induction, not by assumption. -/
theorem releaseAll_of_prefix_guards {pub : Public} {O : Type} (P : Protocol pub O)
    (hash : P.Item → Nat) (x : Key pub) (nd : Model.Node P) (cs : List P.Object)
    (hready : ∀ i o, cs[i]? = some o →
      Model.releasable (P := P) (nd.seen ++ cs.take i) o = true ∧
      P.dependencies.ready (Model.closure (nd.seen ++ cs.take i)) o = true) :
    (Model.releaseAll P hash x nd cs).2 = cs ∧
      (Model.releaseAll P hash x nd cs).1.seen = nd.seen ++ cs := by
  induction cs generalizing nd with
  | nil => exact ⟨rfl, (List.append_nil _).symm⟩
  | cons o cs ih =>
    have hg := hready 0 o (by simp)
    simp only [List.take_zero, List.append_nil] at hg
    simp only [Model.releaseAll, hg.1, hg.2, Bool.and_self, ↓reduceIte]
    have ht := ih
      (nd := ⟨P.recordOwn nd.st o (Model.digests hash o), nd.seen ++ [o]⟩)
      (by
        intro i c hc
        have hC := hready (i + 1) c
          (by simpa only [List.getElem?_cons_succ] using hc)
        simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using hC)
    exact ⟨congrArg (List.cons _) ht.1,
      ht.2.trans (by simp only [List.append_assoc, List.singleton_append])⟩

/-- Ordered readiness discharges every guard for a batch of canonical block envelopes. -/
private theorem forward_batch_guards {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (x : Fin (Fintype.card V))
    (seen cs : List (Wire (Fintype.card V) S.vote)) (hr : PendingReady seen cs)
    (hshape : ∀ o ∈ cs, ∃ t p B, o = forwardObj (S.params (pubOf E) hn) x t p B) :
    ∀ i o, cs[i]? = some o →
      Model.releasable (P := protoOf (compiled (goldilocks S)) E) (seen ++ cs.take i) o = true ∧
      (protoOf (compiled (goldilocks S)) E).dependencies.ready
        (Model.closure (seen ++ cs.take i)) o = true := by
  intro i o hi
  obtain ⟨t, p, B, he⟩ := hshape o (List.mem_of_getElem? hi)
  have hh := (pendingReady_iff seen cs).mp hr i o hi
  subst o
  exact forwardObj_release_guards S hn (seen ++ cs.take i) x t p B hh

/-- A ready canonical forwarding suffix is released completely from its actual
post-prefix node. This allows an ordinary poll emission to precede the block queue. -/
private theorem releaseAll_forward_batch {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (hash : Header Info → Nat) (x : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (goldilocks S)) E))
    (cs : List (protoOf (compiled (goldilocks S)) E).Object)
    (hr : PendingReady nd.seen cs)
    (hshape : ∀ o ∈ cs, ∃ t p B, o = forwardObj (S.params (pubOf E) hn) x t p B) :
    (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd cs).2 = cs ∧
      (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd cs).1.seen =
        nd.seen ++ cs := by
  apply releaseAll_of_prefix_guards
  exact forward_batch_guards S hn x nd.seen cs hr hshape

/-- Ordinary poll candidates may succeed or fail: either way they preserve holdings,
so a ready block-envelope suffix drains completely after their actual release prefix. -/
private theorem releaseAll_forward_suffix {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) (hash : Header Info → Nat) (x : Fin (Fintype.card V))
    (nd : Model.Node (protoOf (compiled (goldilocks S)) E))
    (pre cs : List (protoOf (compiled (goldilocks S)) E).Object)
    (hr : PendingReady nd.seen cs)
    (hshape : ∀ o ∈ cs, ∃ t p B, o = forwardObj (S.params (pubOf E) hn) x t p B) :
    (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd (pre ++ cs)).2 =
      (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd pre).2 ++ cs := by
  rw [Model.releaseAll_append (P := protoOf (compiled (goldilocks S)) E) hash x nd pre cs]
  have hseen := Model.releaseAll_seen (P := protoOf (compiled (goldilocks S)) E)
    hash x nd pre
  have hr' : PendingReady
      (Model.releaseAll (protoOf (compiled (goldilocks S)) E) hash x nd pre).1.seen cs := by
    rw [hseen]
    apply pendingReady_mono (h := hr)
    intro o ho
    obtain ⟨c, hc, ho⟩ := List.mem_flatMap.mp ho
    exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc, ho⟩
  rw [(releaseAll_forward_batch S hn hash x _ cs hr' hshape).1]

/-- Actual selected poll candidates retain the old signed block queue after the ordinary
emission. The self-key premise is the runtime identity, not a new service assumption. -/
theorem signedCandidate_poll_eq {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v) :
    rho.signedCandidate v (.poll t) ((protoOf (compiled (goldilocks S)) E).act nd.st
        (.poll t)).2 =
      @HAppend.hAppend _ (List (protoOf (compiled (goldilocks S)) E).Object) _ _
        (@HAppend.hAppend _ (List (protoOf (compiled (goldilocks S)) E).Object) _ _
          (pollOrdinary S rho v
            ((pollPre (shapeOf S hn nd) (S.release (pubOf E))).outbox.head?.map fun b => (b, [])))
          (pendingWrappers (shapeOf S hn nd)))
        (((shapeOf S hn nd).voteForwards.map fun q =>
          Obj.mk (.signed (rho.ownKey v) .poll) (.data (.voteForward q.1 (encodeVote q.2.1)))
            [q.2.2]) ++
          (pollFlush (shapeOf S hn nd) (S.release (pubOf E))).map fun a =>
            Obj.mk (.signed (rho.ownKey v) .poll) (.data (.att (encodeAtt a))) []) := by
  rw [signedCandidate_poll S rho hn v nd t hsel, pendingWrappers_eq, hself, List.append_assoc]
  rfl

/-- A selected actual poll releases every ready canonical pending block wrapper. The ordinary
emission may fail; later vote envelopes cannot undo releases from the block prefix. -/
theorem dutyStep_poll_pending {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hshape : ∀ o ∈ pendingWrappers (shapeOf S hn nd), ∃ τ p B,
      o = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) τ p B) :
    ∀ o ∈ pendingWrappers (shapeOf S hn nd), o ∈ (rho.dutyStep v nd (.poll t)).2 := by
  intro o ho
  unfold Model.Run.dutyStep
  simp only [show (protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [signedCandidate_poll_eq S rho hn v nd t hsel hself]
  rw [Model.releaseAll_append (P := protoOf (compiled (goldilocks S)) E)]
  apply List.mem_append_left
  erw [releaseAll_forward_suffix S hn rho.hash (rho.ownKey v)
    ⟨((protoOf (compiled (goldilocks S)) E).act nd.st (.poll t)).1, nd.seen⟩ _ _ hr hshape]
  exact List.mem_append_right _ ho

/-- Poll's block map is durable while the pending queue is cleared. -/
theorem poll_wrappers {sp : AC.ACParams}
    {ro : AC.ReplayOrder sp (List (FG.Att sp.n))} {release : Fin sp.n → Time → Bool}
    (st : State sp ro binding) (t : Time) :
    (pollBatch st t release).1.wrappers = st.wrappers ∧
      (pollBatch st t release).1.forwards = [] := by
  have key : ∀ st : State sp ro binding, (poll st t release).1.wrappers = st.wrappers ∧
      (poll st t release).1.forwards = [] := by
    intro st
    unfold poll
    have hf : (fgUpdate st release).wrappers = st.wrappers := by
      rw [fgUpdate_eq st release]
      dsimp only
      split
      · rfl
      · split
        · rfl
        · split <;> rfl
    dsimp only
    split <;> constructor
    · dsimp only; split <;> first | exact hf | rfl
    · rfl
    · dsimp only; split <;> first | exact hf | rfl
    · rfl
  rw [pollBatch_fst]
  split
  · obtain ⟨atts, h⟩ := heldDrain_eq st
    rw [h]; exact key _
  · exact key _

/-- After the real poll, every durable wrapper is held, not merely pending. -/
theorem dutyStep_poll_wrappers_held {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll) (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ∀ o ∈ pendingWrappers (shapeOf S hn nd), ∃ τ p B,
      o = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) τ p B) :
    ∀ root o, (shapeOf S hn (rho.dutyStep v nd (.poll t)).1).wrappers root = some o →
      o ∈ (rho.dutyStep v nd (.poll t)).1.seen.flatMap Obj.parts := by
  intro root o hw
  rw [dutyStep_poll S rho hn v nd t hsel, (poll_wrappers _ _).1] at hw
  have hh := wrappersAccounted_drained (sp := S.params (pubOf E) hn)
    (nd.seen : List (Wire (Fintype.card V) S.vote)) (rho.dutyStep v nd (.poll t)).2
    (shapeOf S hn nd) ha (dutyStep_poll_pending S rho hn v nd t hsel hself hr hc) root o hw
  have he : (rho.dutyStep v nd (.poll t)).1.seen = nd.seen ++ (rho.dutyStep v nd (.poll t)).2 := by
    unfold Model.Run.dutyStep
    simp only [show (protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
      hsel, ↓reduceIte]
    exact Model.releaseAll_seen _ _ _ _
  rw [he]
  exact hh

/-- Each enumerated duty batch releases only objects released by the actual duty list.
The induction threads the same intermediate node as `runDuties`, including unselected
duties, which have an empty batch and leave the state unchanged. -/
private theorem dutyBatches_release {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V)
    (nd : Model.Node (protoOf F E)) (ds : List (protoOf F E).Duty)
    (b : ReleaseBatch (protoOf F E)) (hb : b ∈ dutyBatches rho v nd ds)
    (o : (protoOf F E).Object)
    (ho : o ∈ (Model.releaseAll (protoOf F E) rho.hash (rho.ownKey v)
      b.before b.candidates).2) :
    o ∈ (rho.runDuties v nd ds).2 := by
  induction ds generalizing nd with
  | nil => simp [dutyBatches] at hb
  | cons d ds ih =>
    rw [Model.Run.runDuties_cons]
    simp only [dutyBatches, List.mem_cons] at hb
    rcases hb with rfl | hb
    · apply List.mem_append_left
      unfold Model.Run.dutyStep
      split
      · rename_i hsel
        simpa only [hsel, ↓reduceIte] using ho
      · simp_all [Model.releaseAll]
    · exact List.mem_append_right _ (ih _ hb)

/-- Actual event batches include the duty releases and final gossip, in engine order.
Thus a release from an enumerated batch is an actual event release, not a synthetic
candidate occurrence. This covers delivery events as well as awake ticks. -/
private theorem eventBatches_release {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {O : OutputSchema} {F : ProtocolFamily O} (rho : Model.Run F E) (v : V) (i : Nat) (t : Time)
    (he : rho.SendsAt v i t) (b : ReleaseBatch (protoOf F E))
    (hb : b ∈ eventBatches rho i) (o : (protoOf F E).Object)
    (ho : o ∈ (Model.releaseAll (protoOf F E) rho.hash (rho.ownKey v)
      b.before b.candidates).2) : o ∈ rho.releasesAt i := by
  rcases he with he | ⟨obj, he⟩
  · simp only [eventBatches, he] at hb
    simp only [Model.Run.releasesAt, he, Model.Run.tick]
    split at hb
    · rename_i hawake
      simp only [hawake, ↓reduceIte]
      rcases List.mem_append.mp hb with hb | hb
      · exact List.mem_append_left _ (dutyBatches_release rho v _ _ b hb o ho)
      · simp only [List.mem_singleton] at hb
        subst b
        exact List.mem_append_right _ ho
    · simp at hb
  · simp only [eventBatches, he] at hb
    simp only [Model.Run.releasesAt, he, Model.Run.deliver]
    rcases List.mem_append.mp hb with hb | hb
    · exact List.mem_append_left _ (dutyBatches_release rho v _ _ b hb o ho)
    · simp only [List.mem_singleton] at hb
      subst b
      exact List.mem_append_right _ ho

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
  (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (cutMap : Nat → Nat)
  (pubExec : PublisherExecution S rho)

/-- Concrete publication relation: all executed candidates passing the three guards at
their actual prefix, with the event's own time. No provenance or acceptance claim is used
to select publications. The batch lemmas above establish the actual release field. -/
noncomputable def publisherExecution : PublisherExecution S rho where
  actual r := ExecutedPublication S rho r ∧
    let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
      r.before (r.candidates.take r.index)).1
    Model.releasable nd.seen r.object = true ∧
      (protoOf (compiled (goldilocks S)) E).dependencies.ready (Model.closure nd.seen) r.object
          =
          true
  eventTime i := (rho.events[i]?).map Model.Event.time |>.getD 0
  actual_event r hr := by
    obtain ⟨t, ht⟩ := hr.1.2
    rcases ht with ht | ⟨o, ht⟩
    · simp only [ht, Option.map_some, Option.getD_some, Model.Event.time]
      exact Or.inl ht
    · simp only [ht, Option.map_some, Option.getD_some, Model.Event.time]
      exact Or.inr ⟨o, ht⟩
  actual_success r hr := hr.2
  actual_release r hr := by
    obtain ⟨t, ht⟩ := hr.1.2
    have ho := releaseAll_candidate_success _ rho.hash r.origin r.before r.candidates
      r.index r.object r.candidate hr.2
    have hk : rho.ownKey (rho.key r.origin) = r.origin := rho.key.symm_apply_apply _
    apply eventBatches_release rho (rho.key r.origin) r.event t ht
      ⟨r.before, r.candidates⟩ (List.mem_of_getElem? hr.1.1) r.object
    simpa only [hk] using ho

/-- The concrete relation includes every executed candidate passing its actual prefix
guards, not merely a chosen subset of successful publications. -/
theorem publisherExecution_actual_iff (r : Publication (protoOf (compiled (goldilocks S)) E)) :
    (publisherExecution S rho).actual r ↔ ExecutedPublication S rho r ∧
      let nd := (Model.releaseAll (protoOf (compiled (goldilocks S)) E) rho.hash r.origin
        r.before (r.candidates.take r.index)).1
      Model.releasable nd.seen r.object = true ∧
        (protoOf (compiled (goldilocks S)) E).dependencies.ready
          (Model.closure nd.seen) r.object = true := by
  rfl

/-- Publication time is the time of the actual indexed event. -/
theorem publisherExecution_eventTime_eq (i : Nat) :
    (publisherExecution S rho).eventTime i =
      ((rho.events[i]?).map Model.Event.time).getD 0 := by
  rfl

end Consensus.Goldilocks.Simulation
