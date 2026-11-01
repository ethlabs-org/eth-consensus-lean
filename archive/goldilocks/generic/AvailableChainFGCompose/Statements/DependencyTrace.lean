module
public import AvailableChainFGCompose.Statements.Dependency

@[expose] public section

namespace AvailableChain.FGCompose

variable {In V Body Row Latest : Type} [DecidableEq V]
variable {P : V2.ProtocolSpecD In}

/-- Epoch zero precedes any restart. A restart at index k starts epoch k+1. -/
def dependencyReceiverEpoch (rho : V2.D.Run V P) (x : V) (j : Nat) : Nat :=
  ((rho.events.take j).zipIdx).foldl (fun epoch pair =>
    match pair.1 with
    | .restart y _ => if y = x then pair.2 + 1 else epoch
    | _ => epoch) 0

/-- Immutable original receipt data. Retries keep this value in full. -/
structure FGReceiptToken (V Wire : Type) where
  receiver : V
  eventIndex : Nat
  wire : Wire
  receiptTime : Time
  receiptEpoch : Nat

/-- These observations are the driver's original wire validation and payload reads. -/
structure FGDependencyWireReads (P : V2.ProtocolSpecD In) (Body Row : Type) where
  decodeBody : P.Object → Option Body
  namedRoots : P.Object → Option (BlockId × BlockId)
  proposalErase : P.Object → Option Block
  decodedRows : P.Object → List Row
  bodyRows : Body → List Row

/-- Receipt evidence binds the receiver, exact full body, wire, time and restart epoch. -/
structure FGReceiptOrigin (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (x : V) (b : Body) (o : FGReceiptToken V P.Object) : Prop where
  receiver_eq : o.receiver = x
  delivered : rho.events[o.eventIndex]? = some (.deliver x o.wire o.receiptTime)
  decoded : W.decodeBody o.wire = some b
  authentic : P.wellFormed o.wire = true
  awake_receipt : E.awake x o.receiptTime = true
  named : W.namedRoots o.wire = some (H.root b, H.root (H.parent b))
  geometry : W.proposalErase o.wire = some (H.erase b)
  rows : W.decodedRows o.wire = W.bodyRows b
  epoch_eq : o.receiptEpoch = dependencyReceiverEpoch rho x o.eventIndex

/-- Every microstep records the operation which actually ran. -/
inductive FGDependencyOperation (Body Origin Wire : Type) where
  | arrival (b : Body) (o : Origin)
  | leaf (b : Body) (o : Origin) (result : FGDependencyOutcome)
  | inheritRefusal (b : Body) (o : Origin)
  | notification (b : Body) (o : Origin)
  | replay (b : Body) (o : Origin)
  | ordinary (wire : Wire)
  | rejected (wire : Wire)
  | ownRecord (wire : Wire)
  | clock (t : Time)
  | restore (t : Time)
  | reconstruct (t : Time)
  | rebuild (t : Time)
  | idle

def dependencyOperationKind {Origin Wire : Type} :
    FGDependencyOperation Body Origin Wire → FGDependencyStepKind
  | .arrival _ _ => .arrival
  | .leaf _ _ _ => .leafRetry
  | .inheritRefusal _ _ => .refusalPropagation
  | .notification _ _ => .notification
  | .replay _ _ => .ordinary
  | .ordinary _ => .ordinary
  | .rejected _ => .ordinary
  | .ownRecord _ => .ownRecord
  | .clock _ => .clock
  | .restore _ => .restore
  | .reconstruct _ => .ordinary
  | .rebuild _ => .ordinary
  | .idle => .ordinary

/-- Reads are commands in the executable handler, not a separate selectable read list. -/
inductive FGDependencyCommand (Body Origin Wire : Type) where
  | step (op : FGDependencyOperation Body Origin Wire)
  | read (kind : FGDependencyReadKind)

structure FGDependencyWorkRead (State : Type) where
  offset : Nat
  kind : FGDependencyReadKind
  consumed : State

structure FGDependencyWorkResult (State Body Origin Wire : Type) where
  state : State
  operations : List (FGDependencyOperation Body Origin Wire)
  reads : List (FGDependencyWorkRead State)

/-- A handler's read continuation is executable and receives the state it observes. -/
inductive FGDependencyProgram (State : Type) where
  | finish (state : State)
  | read (kind : FGDependencyReadKind) (state : State)
      (next : State → FGDependencyProgram State)

def dependencyExecuteProgram {State : Type} :
    FGDependencyProgram State → State × List (FGDependencyReadKind × State)
  | .finish st => (st, [])
  | .read kind st next =>
      let result := dependencyExecuteProgram (next st)
      (result.1, (kind, st) :: result.2)

/-- Executable hooks of the dependency driver. Raw restore and clock remain in P. -/
structure FGDependencyDriver (V Body : Type) (P : V2.ProtocolSpecD In) where
  enter : P.State → P.Object → FGReceiptToken V P.Object → P.State
  enterProgram : P.State → P.Object → FGReceiptToken V P.Object → FGDependencyProgram P.State
  hookProgram : P.State → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object →
    FGDependencyProgram P.State
  drain : P.State → P.State
  reconstruct : P.State → Time → P.State
  rebuild : P.State → Time → P.State
  retry : P.State → Body → FGReceiptToken V P.Object → FGDependencyOutcome → P.State
  work : P.State → V2.Event V P.Object →
    List (FGDependencyCommand Body (FGReceiptToken V P.Object) P.Object)
  inheritRefusal : P.State → Body → FGReceiptToken V P.Object → P.State
  notify : P.State → Body → FGReceiptToken V P.Object → P.State
  /-- Ordinary AC reconstruction of a held carrier, separate from the insertion callback.
  The hook program executes this operation and collects its reads. Step laws prohibit signing. -/
  replay : P.State → Body → FGReceiptToken V P.Object → P.State

/-- Each primitive is the actual entry, leaf, report, notification or protocol operation. -/
def dependencyExecuteOperation (F : FGDependencyDriver V Body P) (st : P.State)
    (op : FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object) : P.State :=
  (dependencyExecuteProgram (F.hookProgram st op)).1

/-- Evaluation records every read at its actual state and ordered operation boundary. -/
def dependencyExecuteWork (F : FGDependencyDriver V Body P) (st : P.State) :
    List (FGDependencyCommand Body (FGReceiptToken V P.Object) P.Object) →
      FGDependencyWorkResult P.State Body (FGReceiptToken V P.Object) P.Object
  | [] => ⟨st, [], []⟩
  | .step op :: rest =>
      let tail := dependencyExecuteWork F (dependencyExecuteOperation F st op) rest
      ⟨tail.state, op :: tail.operations,
        ((dependencyExecuteProgram (F.hookProgram st op)).2.map
          (fun r => ⟨1, r.1, r.2⟩)) ++
        tail.reads.map (fun r => { r with offset := r.offset + 1 })⟩
  | .read kind :: rest =>
      let tail := dependencyExecuteWork F st rest
      ⟨tail.state, tail.operations, ⟨0, kind, st⟩ :: tail.reads⟩

/-- All duties and gossip use this one completed post-clock state. -/
def dependencyReleased (E : Generic.Env V) (rho : V2.D.Run V P)
    (st : P.State) (x : V) (t : Time) : List P.Object :=
  if E.awake x t then
    (P.duties t).flatMap (fun d =>
      (rho.ownSeats (P.signLabel d) x).filterMap (fun i =>
        (P.act st d (rho.input x t)).map (fun p => ⟨.seat (P.signLabel d) i, p⟩))) ++
      (P.gossip st t).map (fun p => ⟨.none, p⟩)
  else []

/-- The entry is raw. Its drain is a separate operation in the event fold. -/
def dependencyEventEntry (rho : V2.D.Run V P) (F : FGDependencyDriver V Body P)
    (x : V) (j : Nat) (st : P.State) (e : V2.Event V P.Object) : P.State :=
  match e with
  | .restart y t => if y = x then P.restore (P.durable st) t else st
  | .tick y t => if y = x then P.clock st t else st
  | .deliver y wire t => if y = x then
      (dependencyExecuteProgram (F.enterProgram st wire
        ⟨x, j, wire, t, dependencyReceiverEpoch rho x j⟩)).1 else st

/-- Entry and primitive-hook reads are collected by evaluation, even without read commands. -/
def dependencyEventReads (rho : V2.D.Run V P) (F : FGDependencyDriver V Body P)
    (x : V) (j : Nat) (st : P.State) (e : V2.Event V P.Object) :
    List (FGDependencyWorkRead P.State) :=
  let entryReads := match e with
    | .deliver y wire t => if y = x then
        (dependencyExecuteProgram (F.enterProgram st wire
          ⟨x, j, wire, t, dependencyReceiverEpoch rho x j⟩)).2.map
            (fun r => ⟨0, r.1, r.2⟩) else []
    | _ => []
  let entry := dependencyEventEntry rho F x j st e
  entryReads ++ (dependencyExecuteWork F entry (F.work entry e)).reads

def dependencyEventStep (_E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (j : Nat)
    (st : P.State) (e : V2.Event V P.Object) : P.State :=
  let entry := dependencyEventEntry rho F x j st e
  (dependencyExecuteWork F entry (F.work entry e)).state

/-- This is the dependency-aware event fold; it is not the ordinary Duty fold. -/
def dependencyStateBefore (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (j : Nat) : P.State :=
  ((rho.events.take j).zipIdx).foldl
    (fun st pair => dependencyEventStep E rho F x pair.2 st pair.1) P.init

def dependencyDrainInput (F : FGDependencyDriver V Body P)
    (x : V) (st : P.State) (e : V2.Event V P.Object) : P.State :=
  match e with
  | .restart y t => if y = x then F.reconstruct st t else st
  | _ => st

def dependencyDutyState (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (j : Nat) (e : V2.Event V P.Object) :
    P.State :=
  let entry := dependencyEventEntry rho F x j (dependencyStateBefore E rho F x j) e
  F.drain (dependencyDrainInput F x entry e)

def dependencyEmits (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (wire : P.Object) (t : Time) : Prop :=
  ∃ j, rho.events[j]? = some (.tick x t) ∧
    wire ∈ dependencyReleased E rho (dependencyDutyState E rho F x j (.tick x t)) x t

def dependencyReadCode : FGDependencyReadKind → Nat
  | .fg => 0 | .proposer => 1 | .head => 2 | .ac => 3

/-- Tick interfaces use one duty state. Other handler reads come from executed commands. -/
def dependencyReadRequired (E : Generic.Env V) (_F : FGDependencyDriver V Body P)
    (x : V) (_entry : P.State) (e : V2.Event V P.Object) (_kind : FGDependencyReadKind) : Prop :=
  match e with
  | .tick y t => y = x ∧ E.awake x t = true
  | .deliver _ _ _ | .restart _ _ => False

def dependencyReadState (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (j : Nat) (e : V2.Event V P.Object) :
    P.State :=
  match e with
  | .tick _ _ => dependencyDutyState E rho F x j e
  | _ => dependencyStateBefore E rho F x (j + 1)

def dependencyActualRead (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (i : Nat) (st : P.State) : Prop :=
  ∃ j e kind, rho.events[j]? = some e ∧
    dependencyReadRequired E F x (dependencyStateBefore E rho F x j) e kind ∧
    i = 4 * j + dependencyReadCode kind ∧ st = dependencyReadState E rho F x j e

/-- Finite refinement data. The driver protocol P and the one-body leaf are separate. -/
structure FGDependencyTrace (State : Type) where
  length : Nat
  state : Nat → State
  time : Nat → Time
  start : Nat → Nat
  done : Nat → Nat
  readCut : Nat → Nat
  entryCut : Nat → Nat
  dutyCut : Nat → Nat
  hookRead : Nat → Nat → FGDependencyReadKind → Nat → State → Prop

def dependencyStrictPrefix (rho : V2.D.Run V P) (T : FGDependencyTrace P.State)
    (deadline : Time) (k : Nat) : Prop :=
  k ≤ T.length ∧ T.time k < deadline ∧
    ∀ j e, rho.events[j]? = some e → T.start j ≤ k → e.time < deadline

variable {LeafIn : Type} {Leaf : V2.ProtocolSpecD LeafIn}

/-- Production requires a simulation of this actual driver run, not the ordinary leaf fold. -/
structure FGDependencyTraceLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (x : V) (H : FGHistoricalReads P.State Body)
    (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (T : FGDependencyTrace P.State)
    (F : FGDependencyDriver V Body P)
    (Op : Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop where
  arrival_laws : FGDependencyArrivalLeafLaws H D L Arrival Notify
  initial : T.state 0 = P.init
  initial_accepted : ∀ b, D.accepted P.init b → b = L.genesis
  micro_step : ∀ k, k < T.length → ∃ kind, Step kind x (T.state k) (T.state (k + 1))
  external_step : ∀ j e, rho.events[j]? = some e →
    T.state (T.start j) = dependencyStateBefore E rho F x j ∧
    T.state (T.done j) = dependencyStateBefore E rho F x (j + 1)
  step_kind : ∀ k, k < T.length →
    Step (dependencyOperationKind (Op k)) x (T.state k) (T.state (k + 1))
  operation_bound : ∀ k, k < T.length →
    match Op k with
    | .arrival b o => Arrival (T.state k) b o (T.state (k + 1)) ∧
        T.state (k + 1) = F.enter (T.state k) o.wire o ∧
        FGReceiptOrigin E rho H W x b o ∧ k = T.start o.eventIndex
    | .leaf b o result => T.state (k + 1) = F.retry (T.state k) b o result ∧
        L.step (T.state k) b o result (T.state (k + 1)) ∧
        D.originAvailable (T.state k) b o ∧
        leafState (T.state (k + 1)) = Leaf.process (leafState (T.state k)) (leafWire o.wire)
    | .inheritRefusal b o => D.validBody b ∧ D.originAvailable (T.state k) b o ∧
        dependencyRefused H D (T.state k) (H.parent b) ∧
        dependencyRefused H D (T.state (k + 1)) b ∧
        T.state (k + 1) = F.inheritRefusal (T.state k) b o ∧
        L.report (T.state k) b o (T.state (k + 1))
    | .notification b o => Notify (T.state k) b (T.state (k + 1)) ∧
        D.originAvailable (T.state k) b o ∧ dependencyResolved H D (T.state k) b ∧
        T.state (k + 1) = F.notify (T.state k) b o ∧ D.notified (T.state (k + 1)) b
    | .replay b o => D.accepted (T.state k) b ∧ b ∈ H.acceptedBodies (T.state k) ∧
        D.originAvailable (T.state k) b o ∧ W.decodeBody o.wire = some b ∧
        T.state (k + 1) = F.replay (T.state k) b o ∧
        H.acceptedBlocks (T.state (k + 1)) = H.acceptedBlocks (T.state k) ∧
        H.acceptedBodies (T.state (k + 1)) = H.acceptedBodies (T.state k) ∧
        (∀ c, D.accepted (T.state (k + 1)) c ↔ D.accepted (T.state k) c) ∧
        (∀ c r pr, D.refused (T.state (k + 1)) c r pr ↔ D.refused (T.state k) c r pr) ∧
        (∀ c token, D.pending (T.state (k + 1)) c token ↔ D.pending (T.state k) c token) ∧
        (∀ c token, D.originAvailable (T.state (k + 1)) c token ↔
          D.originAvailable (T.state k) c token) ∧
        (∀ c token, ¬ L.callback (T.state k) c token (T.state (k + 1))) ∧
        (∀ c token, ¬ L.report (T.state k) c token (T.state (k + 1)))
    | .rejected wire => P.wellFormed wire = false ∧
        T.state (k + 1) = P.process (T.state k) wire
    | .ordinary wire => P.wellFormed wire = true ∧ W.decodeBody wire = none ∧
        T.state (k + 1) = P.process (T.state k) wire
    | .ownRecord wire => T.state (k + 1) = P.recordOwn (T.state k) wire
    | .clock t => T.state (k + 1) = P.clock (T.state k) t
    | .restore t => T.state (k + 1) = P.restore (P.durable (T.state k)) t
    | .reconstruct t =>
        T.state (k + 1) = F.reconstruct (T.state k) t ∧
        ∃ j, rho.events[j]? = some (.restart x t) ∧ k = T.entryCut j
    | .rebuild t =>
        T.state (k + 1) = F.rebuild (T.state k) t ∧
        ∃ j, rho.events[j]? = some (.restart x t) ∧ T.dutyCut j ≤ k ∧ k < T.done j ∧
          ∀ q, T.dutyCut j ≤ q → q < k → ∃ b o, Op q = .replay b o
    | .idle => T.state (k + 1) = T.state k
  delivery_entry : ∀ j wire t, rho.events[j]? = some (.deliver x wire t) →
    let o : FGReceiptToken V P.Object := ⟨x, j, wire, t, dependencyReceiverEpoch rho x j⟩
    Op (T.start j) =
      (if E.awake x t then
        if P.wellFormed wire then
          match W.decodeBody wire with
          | some b => .arrival b o
          | none => .ordinary wire
        else .rejected wire
      else .idle)
  work_execution : ∀ j e, rho.events[j]? = some e →
    let work := dependencyExecuteWork F (T.state (T.entryCut j))
      (F.work (T.state (T.entryCut j)) e)
    work.state = T.state (T.done j) ∧
    work.operations = (List.range (T.done j - T.entryCut j)).map
      (fun offset => Op (T.entryCut j + offset))
  work_step : ∀ j e k, rho.events[j]? = some e →
    T.entryCut j ≤ k → k < T.done j →
    T.state (k + 1) = dependencyExecuteOperation F (T.state k) (Op k)
  hook_correspondence : ∀ j e index kind cut st, rho.events[j]? = some e →
    (T.hookRead j index kind cut st ↔ ∃ r,
      (dependencyEventReads rho F x j (T.state (T.start j)) e)[index]? = some r ∧
      r.kind = kind ∧ cut = T.entryCut j + r.offset ∧ st = r.consumed)
  hook_reads : ∀ j e r, rho.events[j]? = some e →
    r ∈ dependencyEventReads rho F x j (T.state (T.start j)) e →
    T.entryCut j + r.offset ≤ T.done j ∧
    T.state (T.entryCut j + r.offset) = r.consumed ∧
    FGDependencySteps Step x (T.state (T.entryCut j)) r.consumed ∧
    dependencyClosed H D r.consumed
  receipt_entry : ∀ j wire t b, rho.events[j]? = some (.deliver x wire t) →
    E.awake x t = true → P.wellFormed wire = true → W.decodeBody wire = some b →
    let o : FGReceiptToken V P.Object := ⟨x, j, wire, t, dependencyReceiverEpoch rho x j⟩
    Op (T.start j) = .arrival b o ∧
    Arrival (T.state (T.start j)) b o (T.state (T.entryCut j)) ∧
    (D.timely (T.state (T.start j)) b → Effect H D (T.state (T.entryCut j)) b o)
  entry_boundary : ∀ j e, rho.events[j]? = some e →
    T.entryCut j = T.start j + 1 ∧ T.entryCut j ≤ T.dutyCut j ∧
    T.dutyCut j ≤ T.done j ∧
    T.state (T.entryCut j) =
      dependencyEventEntry rho F x j (T.state (T.start j)) e ∧
    T.state (T.dutyCut j) =
      F.drain (dependencyDrainInput F x (T.state (T.entryCut j)) e)
  drain_operations : ∀ j e k, rho.events[j]? = some e →
    T.entryCut j ≤ k → k < T.done j →
    (∃ b o result, Op k = .leaf b o result) ∨
    (∃ b o, Op k = .inheritRefusal b o) ∨
    (∃ b o, Op k = .notification b o) ∨
    (∃ b o, Op k = .replay b o) ∨
    (∃ wire t, e = .tick x t ∧ T.dutyCut j ≤ k ∧ Op k = .ownRecord wire ∧
      wire ∈ dependencyReleased E rho (T.state (T.dutyCut j)) x t ∧
      P.objSelfVisible wire = true) ∨ Op k = .idle ∨
    (∃ t, e = .restart x t ∧ k = T.entryCut j ∧ Op k = .reconstruct t) ∨
    (∃ t, e = .restart x t ∧ T.dutyCut j ≤ k ∧ Op k = .rebuild t ∧
      ∀ q, T.dutyCut j ≤ q → q < k → ∃ b o, Op q = .replay b o)
  boundary_idle : ∀ k, k < T.length →
    (¬ ∃ j e, rho.events[j]? = some e ∧ T.start j ≤ k ∧ k < T.done j) →
    Op k = .idle
  raw_restore : ∀ j t, rho.events[j]? = some (.restart x t) →
    Op (T.start j) = .restore t
  raw_clock : ∀ j t, rho.events[j]? = some (.tick x t) → Op (T.start j) = .clock t
  restore_data : ∀ st t,
    H.acceptedBlocks (P.restore (P.durable st) t) = H.acceptedBlocks st ∧
    H.acceptedBodies (P.restore (P.durable st) t) = H.acceptedBodies st ∧
    (∀ b r pr, D.refused (P.restore (P.durable st) t) b r pr ↔ D.refused st b r pr) ∧
    (∀ b o, D.pending (P.restore (P.durable st) t) b o ↔ D.pending st b o) ∧
    (∀ b o, D.originAvailable (P.restore (P.durable st) t) b o ↔ D.originAvailable st b o)
  reconstruct_program : ∀ st t,
    F.hookProgram st (.reconstruct t) = .finish (F.reconstruct st t)
  reconstruct_data : ∀ st t,
    let z := F.reconstruct st t
    H.acceptedBlocks z = H.acceptedBlocks st ∧
    H.acceptedBodies z = H.acceptedBodies st ∧
    (∀ b, D.accepted z b ↔ D.accepted st b) ∧
    (∀ b r pr, D.refused z b r pr ↔ D.refused st b r pr) ∧
    (∀ b o, D.pending z b o ↔ D.pending st b o) ∧
    (∀ b o, D.originAvailable z b o ↔ D.originAvailable st b o) ∧
    (∀ b, D.notified z b ↔ D.notified st b) ∧
    (∀ b o, ¬ L.callback st b o z) ∧
    (∀ b o, ¬ L.report st b o z)
  restart_reconstruct : ∀ j t,
    rho.events[j]? = some (.restart x t) →
    T.entryCut j < T.dutyCut j ∧ Op (T.entryCut j) = .reconstruct t
  restart_drain_closed : ∀ j t,
    rho.events[j]? = some (.restart x t) →
    dependencyClosed H D (T.state (T.dutyCut j))
  restart_replay_order : ∀ j t k b o,
    rho.events[j]? = some (.restart x t) →
    T.entryCut j ≤ k → k < T.done j → Op k = .replay b o →
    T.dutyCut j ≤ k
  rebuild_program : ∀ st t,
    F.hookProgram st (.rebuild t) = .finish (F.rebuild st t)
  rebuild_data : ∀ st t,
    let z := F.rebuild st t
    H.acceptedBlocks z = H.acceptedBlocks st ∧
    H.acceptedBodies z = H.acceptedBodies st ∧
    (∀ b, D.accepted z b ↔ D.accepted st b) ∧
    (∀ b r pr, D.refused z b r pr ↔ D.refused st b r pr) ∧
    (∀ b o, D.pending z b o ↔ D.pending st b o) ∧
    (∀ b o, D.originAvailable z b o ↔ D.originAvailable st b o) ∧
    (∀ b, D.notified z b ↔ D.notified st b) ∧
    (∀ b o, ¬ L.callback st b o z) ∧
    (∀ b o, ¬ L.report st b o z)
  /-- Every local restart has one rebuild cut r: replays only in [dutyCut, r), then the
  final dependency drain only in [r+1, done). Both intervals may be empty. -/
  restart_rebuild : ∀ j t,
    rho.events[j]? = some (.restart x t) →
    ∃ r, T.dutyCut j ≤ r ∧ r < T.done j ∧ Op r = .rebuild t ∧
      (∀ q t', T.entryCut j ≤ q → q < T.done j → Op q = .rebuild t' → q = r) ∧
      (∀ q, T.dutyCut j ≤ q → q < r → ∃ b o, Op q = .replay b o) ∧
      (∀ q, r < q → q < T.done j →
        (∃ b o result, Op q = .leaf b o result) ∨ (∃ b o, Op q = .inheritRefusal b o) ∨
        (∃ b o, Op q = .notification b o) ∨ Op q = .idle) ∧
      T.state (T.done j) = F.drain (T.state (r + 1))
  clock_no_insert : ∀ st t,
    H.acceptedBlocks (P.clock st t) = H.acceptedBlocks st ∧
    H.acceptedBodies (P.clock st t) = H.acceptedBodies st
  wire_validation : ∀ wire b, P.wellFormed wire = true →
    W.decodeBody wire = some b → D.validBody b
  origin_valid : ∀ k b o, k ≤ T.length → D.originAvailable (T.state k) b o →
    FGReceiptOrigin E rho H W x b o ∧ T.start o.eventIndex < k
  leaf_step : ∀ k b o st', k < T.length →
    L.step (T.state k) b o .accepted st' → st' = T.state (k + 1) →
    FGReceiptOrigin E rho H W x b o ∧ T.start o.eventIndex < k ∧
    leafState st' = Leaf.process (leafState (T.state k)) (leafWire o.wire)
  refusal_creation : ∀ k b, k < T.length →
    dependencyRefused H D (T.state (k + 1)) b → ¬ dependencyRefused H D (T.state k) b →
    (∃ o, Op k = .leaf b o .definitiveRefused ∧
      L.step (T.state k) b o .definitiveRefused (T.state (k + 1)) ∧
      L.report (T.state k) b o (T.state (k + 1)) ∧
      D.validBody b ∧ D.priorChecks (T.state k) b ∧ D.timely (T.state k) b ∧
      ¬ D.accepted (T.state k) b ∧ D.accepted (T.state k) (H.parent b) ∧
      D.conflictsFinal (T.state k) b) ∨
    (∃ o, (Op k = .inheritRefusal b o ∨ Op k = .arrival b o) ∧
      D.validBody b ∧ D.originAvailable (T.state (k + 1)) b o ∧
      dependencyRefused H D (T.state k) (H.parent b) ∧
      L.report (T.state k) b o (T.state (k + 1)))
  refusal_history : ∀ k b, k ≤ T.length → dependencyRefused H D (T.state k) b →
    ∃ first o, first ≤ k ∧ D.originAvailable (T.state k) b o ∧
      FGDependencyRefusalEvidence H D L T.state
        (fun q c token => q < T.length ∧ Op q = .leaf c token .definitiveRefused ∧
          FGReceiptOrigin E rho H W x c token ∧ T.start token.eventIndex < q ∧
          leafState (T.state (q + 1)) =
            Leaf.process (leafState (T.state q)) (leafWire token.wire))
        (fun q c token => q < T.length ∧
          (Op q = .inheritRefusal c token ∨ Op q = .arrival c token) ∧
          FGReceiptOrigin E rho H W x c token ∧ T.start token.eventIndex ≤ q ∧
          L.report (T.state q) c token (T.state (q + 1))) first b o
  notification_creation : ∀ k b, k < T.length →
    D.notified (T.state (k + 1)) b → ¬ D.notified (T.state k) b →
    ∃ o, Op k = .notification b o ∧ Notify (T.state k) b (T.state (k + 1)) ∧
      ∃ q, q < k ∧
        ((D.accepted (T.state k) b ∧ L.callback (T.state q) b o (T.state (q + 1)) ∧
          Op q = .leaf b o .accepted) ∨
        (dependencyRefused H D (T.state k) b ∧
          L.report (T.state q) b o (T.state (q + 1)) ∧
          (Op q = .leaf b o .definitiveRefused ∨ Op q = .inheritRefusal b o ∨
            Op q = .arrival b o)))
  origin_attribution : ∀ k b, k < T.length →
    D.accepted (T.state (k + 1)) b → ¬ D.accepted (T.state k) b → ∃ o,
    L.step (T.state k) b o .accepted (T.state (k + 1)) ∧
    D.originAvailable (T.state (k + 1)) b o ∧
    Op k = .leaf b o .accepted ∧
    W.proposalErase o.wire = some (H.erase b) ∧ W.decodedRows o.wire = W.bodyRows b
  actual_read : ∀ i st, ActualRead x i st ↔ dependencyActualRead E rho F x i st
  read_order : ∀ j e kind, rho.events[j]? = some e →
    dependencyReadRequired E F x (dependencyStateBefore E rho F x j) e kind →
    let i := 4 * j + dependencyReadCode kind
    T.entryCut j ≤ T.readCut i ∧ T.readCut i ≤ T.done j ∧
    (match e with | .tick _ _ => T.readCut i = T.dutyCut j | _ => T.readCut i = T.done j) ∧
    FGDependencySteps Step x (T.state (T.entryCut j)) (T.state (T.readCut i))
  read_correspondence : ∀ i st, ActualRead x i st →
    T.readCut i ≤ T.length ∧ T.state (T.readCut i) = st ∧ dependencyClosed H D st
  order_and_time : ∀ (i j : Nat) (ei ej : V2.Event V P.Object),
    rho.events[i]? = some ei → rho.events[j]? = some ej →
    i ≤ j → ei.time ≤ ej.time
  finite_segment : ∀ j e, rho.events[j]? = some e →
    T.start j ≤ T.done j ∧ T.done j ≤ T.length
  event_drain : ∀ j y wire t, rho.events[j]? = some (.deliver y wire t) →
    dependencyClosed H D (T.state (T.done j))
  entry_drain : ∀ j e, rho.events[j]? = some e →
    dependencyClosed H D (T.state (T.done j))
  segment_time : ∀ j e k, rho.events[j]? = some e →
    T.start j ≤ k → k ≤ T.done j → T.time k = e.time
  event_order : ∀ (i j : Nat) (ei ej : V2.Event V P.Object),
    rho.events[i]? = some ei → rho.events[j]? = some ej →
    i < j → T.done i < T.start j
  completion_cut : ∀ j e deadline, rho.events[j]? = some e → e.time < deadline →
    dependencyStrictPrefix rho T deadline (T.done j)
  tick_records : ∀ j t, rho.events[j]? = some (.tick x t) →
    T.state (T.done j) = F.drain
      (((dependencyReleased E rho (T.state (T.dutyCut j)) x t).filter
        P.objSelfVisible).foldl P.recordOwn (T.state (T.dutyCut j)))
  atomic_tick : ∀ (j : Nat) (t : Time), rho.events[j]? = some (.tick x t) →
    T.entryCut j ≤ T.dutyCut j ∧ T.dutyCut j ≤ T.done j ∧
    T.state (T.dutyCut j) = dependencyDutyState E rho F x j (.tick x t) ∧
    dependencyClosed H D (T.state (T.dutyCut j)) ∧
    FGDependencySteps Step x (T.state (T.dutyCut j)) (T.state (T.done j))

/-- Public completion sites must name the actual event, kind and trace boundaries. -/
structure FGDependencyReadClosureLaws (E : Generic.Env V) (rho : V2.D.Run V P) (x : V)
    (H : FGHistoricalReads P.State Body)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (T : FGDependencyTrace P.State) (F : FGDependencyDriver V Body P)
    (site : Nat → FGDependencyReadSite P.State)
    (Read : V → Nat → P.State → Prop)
    (W : FGDependencyWireReads P Body Row)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Op : Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object) : Prop where
  trace_bound : FGDependencyTraceLaws E rho x H W D L Step T F Op Arrival Notify
    leafState leafWire Read
  actual_read : ∀ i st, Read x i st ↔ dependencyActualRead E rho F x i st
  site_correspondence : ∀ i st, Read x i st → ∃ e,
    rho.events[(site i).eventIndex]? = some e ∧
    dependencyReadRequired E F x
      (dependencyStateBefore E rho F x (site i).eventIndex) e (site i).kind ∧
    i = 4 * (site i).eventIndex + dependencyReadCode (site i).kind ∧
    (site i).entryCut = T.entryCut (site i).eventIndex ∧
    (site i).consumedCut = T.readCut i ∧
    (match e with
      | .tick _ _ => (site i).consumedCut = T.dutyCut (site i).eventIndex
      | _ => (site i).consumedCut = T.done (site i).eventIndex)
  hook_correspondence : ∀ j e index kind cut st, rho.events[j]? = some e →
    (T.hookRead j index kind cut st ↔ ∃ r,
      (dependencyEventReads rho F x j (T.state (T.start j)) e)[index]? = some r ∧
      r.kind = kind ∧ cut = T.entryCut j + r.offset ∧ st = r.consumed)
  hook_completion : ∀ j e r, rho.events[j]? = some e →
    r ∈ dependencyEventReads rho F x j (T.state (T.start j)) e →
    T.entryCut j + r.offset ≤ T.done j ∧
    T.state (T.entryCut j + r.offset) = r.consumed ∧
    FGDependencySteps Step x (T.state (T.entryCut j)) r.consumed ∧
    dependencyClosed H D r.consumed
  read_closed : ∀ i st, Read x i st → dependencyClosed H D st
  finite_completion : ∀ i st, Read x i st →
    (site i).entryCut ≤ (site i).consumedCut ∧ (site i).consumedCut ≤ T.length ∧
    (site i).consumed = st ∧ T.state (site i).consumedCut = st ∧
    FGDependencySteps Step x (T.state (site i).entryCut) st ∧ dependencyClosed H D st

/-- Network facts are consumed under the original awake, horizon and old-send guards. -/
structure FGDependencyDeliveryLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (x : V) (H : FGHistoricalReads P.State Body)
    (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (T : FGDependencyTrace P.State)
    (F : FGDependencyDriver V Body P)
    (Outstanding : P.Object → Time → Time → Prop) : Prop where
  old_send : ∀ sender wire sent wake deadline b,
    sender ∈ rho.honest → dependencyEmits E rho F sender wire sent →
    W.decodeBody wire = some b → D.validBody b → Outstanding wire sent wake →
    sent < deadline → wake ≤ deadline →
    (∀ t, wake ≤ t → t ≤ deadline → E.awake x t = true) →
    (∀ (j : Nat) (t : Time), rho.events[j]? = some (.restart x t) →
      wake < t → deadline < t) →
    deadline ≤ rho.horizon →
    max (max sent E.t_GST) wake + E.Δ ≤ deadline →
    ∃ j o, FGReceiptOrigin E rho H W x b o ∧ o.eventIndex = j ∧
      o.receiptTime < max (max sent E.t_GST) wake + E.Δ ∧
      Effect H D (T.state (T.done j)) b o

end AvailableChain.FGCompose
end
