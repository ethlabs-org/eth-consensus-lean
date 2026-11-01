module
public import AvailableChainFGCompose.Statements.DependencyTrace

@[expose] public section

/-! Shared observation interface of one execution (route B of the X0 audit).

The interface exposes the event-prefix states, the receiver-local cuts, the cut maps of
each event, the actual released objects and the accepting microsteps. Two folds instantiate
it: the ordinary Duty fold and the dependency-driver fold. A local cut number of one
receiver is not a global event index; only the stated maps relate them. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]

/-- The original receipt token of a delivery event at its receiver. -/
def fgEventToken (rho : V2.D.Run V P) (x : V) (j : Nat) (wire : P.Object) (t : Time) :
    FGReceiptToken V P.Object :=
  ⟨x, j, wire, t, dependencyReceiverEpoch rho x j⟩

theorem fgEventToken_def (rho : V2.D.Run V P) (x : V) (j : Nat) (wire : P.Object)
    (t : Time) :
    fgEventToken rho x j wire t = ⟨x, j, wire, t, dependencyReceiverEpoch rho x j⟩ := rfl

/-- Actual execution data. `start`, `entry`, `duty` and `done` map an event index to the
local cuts of a receiver: before the event, after the raw entry (clock, raw restore or
raw delivery entry), the duty state (clock and first drain complete, before own records)
and the completed event. `accepts x k o` says that the microstep from local cut `k`
accepts the body of the original receipt token `o`. `ownWrites x k` lists the own records
that the microstep from cut `k` writes, in order (empty for every other microstep). -/
structure FGExecutionObs (V : Type) (P : V2.ProtocolSpecD In) where
  stateBefore : Nat → V → P.State
  cutLength : V → Nat
  cutState : V → Nat → P.State
  cutTime : V → Nat → Time
  start : V → Nat → Nat
  entry : V → Nat → Nat
  duty : V → Nat → Nat
  done : V → Nat → Nat
  released : V → Nat → List P.Object
  finish : V → P.State → P.State
  accepts : V → Nat → FGReceiptToken V P.Object → Prop
  ownWrites : V → Nat → List P.Object

variable (O : FGExecutionObs V P)

/-- The released objects that the receiver records as its own writes. -/
def obsOwnReleased (x : V) (j : Nat) : List P.Object :=
  (O.released x j).filter P.objSelfVisible

omit [DecidableEq V] in
theorem obsOwnReleased_def (x : V) (j : Nat) :
    obsOwnReleased O x j = (O.released x j).filter P.objSelfVisible := rfl

/-- An emission is an actual release at the receiver's own tick event. -/
def obsEmits (rho : V2.D.Run V P) (x : V) (o : P.Object) (t : Time) : Prop :=
  ∃ j, rho.events[j]? = some (.tick x t) ∧ o ∈ O.released x j

omit [DecidableEq V] in
theorem obsEmits_def (rho : V2.D.Run V P) (x : V) (o : P.Object) (t : Time) :
    obsEmits O rho x o t = ∃ j, rho.events[j]? = some (.tick x t) ∧ o ∈ O.released x j :=
  rfl

/-- The duty state of an event (the state that selection reads). -/
def obsDutyState (x : V) (j : Nat) : P.State := O.cutState x (O.duty x j)

omit [DecidableEq V] in
theorem obsDutyState_def (x : V) (j : Nat) :
    obsDutyState O x j = O.cutState x (O.duty x j) := rfl

/-- Strict-time prefix read: events with time `< t`. -/
def obsStrictState (rho : V2.D.Run V P) (x : V) (t : Time) : P.State :=
  O.stateBefore (V2.D.Run.idxBefore rho t) x

omit [DecidableEq V] in
theorem obsStrictState_def (rho : V2.D.Run V P) (x : V) (t : Time) :
    obsStrictState O rho x t = O.stateBefore (V2.D.Run.idxBefore rho t) x := rfl

/-- After-ticks prefix read: event keys `≤ (t, 1)`. -/
def obsAfterTicksState (rho : V2.D.Run V P) (x : V) (t : Time) : P.State :=
  O.stateBefore (afterTicksIdx rho t) x

omit [DecidableEq V] in
theorem obsAfterTicksState_def (rho : V2.D.Run V P) (x : V) (t : Time) :
    obsAfterTicksState O rho x t = O.stateBefore (afterTicksIdx rho t) x := rfl

/-- Inclusive prefix read: events with time `≤ t`. -/
def obsInclusiveState (rho : V2.D.Run V P) (x : V) (t : Time) : P.State :=
  O.stateBefore (timeIdx rho t) x

omit [DecidableEq V] in
theorem obsInclusiveState_def (rho : V2.D.Run V P) (x : V) (t : Time) :
    obsInclusiveState O rho x t = O.stateBefore (timeIdx rho t) x := rfl

/-- Prefix, cut, release and acceptance-origin laws. No service, safety, reset, shield
or finality conclusion is part of these laws. -/
structure FGExecutionObsLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (O : FGExecutionObs V P) : Prop where
  init_state : ∀ x, O.stateBefore 0 x = P.init
  start_state : ∀ j e x, rho.events[j]? = some e →
    O.cutState x (O.start x j) = O.stateBefore j x
  done_state : ∀ j e x, rho.events[j]? = some e →
    O.cutState x (O.done x j) = O.stateBefore (j + 1) x
  cut_order : ∀ j e x, rho.events[j]? = some e →
    O.start x j < O.entry x j ∧ O.entry x j ≤ O.duty x j ∧ O.duty x j ≤ O.done x j ∧
      O.done x j ≤ O.cutLength x
  event_order : ∀ (i j : Nat) (ei ej : V2.Event V P.Object) x,
    rho.events[i]? = some ei → rho.events[j]? = some ej → i < j → O.done x i < O.start x j
  segment_time : ∀ j e x k, rho.events[j]? = some e →
    O.start x j ≤ k → k ≤ O.done x j → O.cutTime x k = e.time
  tick_entry : ∀ j x t, rho.events[j]? = some (.tick x t) →
    O.cutState x (O.entry x j) = P.clock (O.cutState x (O.start x j)) t
  restart_entry : ∀ j x t, rho.events[j]? = some (.restart x t) →
    O.cutState x (O.entry x j) = P.restore (P.durable (O.cutState x (O.start x j))) t
  released_tick : ∀ j x t, rho.events[j]? = some (.tick x t) →
    O.released x j = dependencyReleased E rho (O.cutState x (O.duty x j)) x t
  released_other : ∀ j x, (∀ t, rho.events[j]? ≠ some (.tick x t)) → O.released x j = []
  tick_done : ∀ j x t, rho.events[j]? = some (.tick x t) →
    O.cutState x (O.done x j) =
      O.finish x ((obsOwnReleased O x j).foldl P.recordOwn (O.cutState x (O.duty x j)))
  accept_origin : ∀ x k o, O.accepts x k o →
    k < O.cutLength x ∧ o.receiver = x ∧
      rho.events[o.eventIndex]? = some (.deliver x o.wire o.receiptTime) ∧
      o.receiptEpoch = dependencyReceiverEpoch rho x o.eventIndex ∧
      O.start x o.eventIndex ≤ k
  accept_time : ∀ x k o, O.accepts x k o → o.receiptTime ≤ O.cutTime x k
  tail_state : ∀ j x, rho.events.length ≤ j →
    O.stateBefore j x = O.stateBefore rho.events.length x
  own_source : ∀ x k, O.ownWrites x k ≠ [] → k < O.cutLength x ∧
    ∃ j t, rho.events[j]? = some (.tick x t) ∧ O.duty x j ≤ k ∧ k < O.done x j
  own_state : ∀ x k, O.ownWrites x k ≠ [] →
    O.cutState x (k + 1) = (O.ownWrites x k).foldl P.recordOwn (O.cutState x k)
  own_complete : ∀ j x t, rho.events[j]? = some (.tick x t) →
    (List.range (O.done x j - O.duty x j)).flatMap (fun i => O.ownWrites x (O.duty x j + i)) =
      obsOwnReleased O x j

variable {n : Nat} {Base Proposal Wire : Type}

/-- Reachable TF laws at the cuts actually used. Raw restore keeps TF equality. -/
structure FGObservedCoreLaws (R : FGCoreReads P n Base Proposal Wire)
    (rho : V2.D.Run V P) (O : FGExecutionObs V P) : Prop where
  tf_step : ∀ x k, k < O.cutLength x →
    (R.core (O.cutState x k)).fg.TF ⊆ (R.core (O.cutState x (k + 1))).fg.TF
  restore_tf : ∀ j x t, rho.events[j]? = some (.restart x t) →
    (R.core (O.cutState x (O.entry x j))).fg.TF = (R.core (O.cutState x (O.start x j))).fg.TF
  head_mem : ∀ j x t s, rho.events[j]? = some (.tick x t) →
    ∃ B ∈ (R.core (O.cutState x (O.duty x j))).fg.TF,
      R.erase B = R.headVote (O.cutState x (O.duty x j)) s
  parent_closed : ∀ x k, k ≤ O.cutLength x → ∀ B ∈ (R.core (O.cutState x k)).fg.TF,
    B.parent ∈ (R.core (O.cutState x k)).fg.TF

/-- F prefix monotonicity through every microstep; raw restore keeps F. -/
structure FGObservedFinalityLaws (R : FGCoreReads P n Base Proposal Wire)
    (rho : V2.D.Run V P) (O : FGExecutionObs V P) : Prop where
  f_step : ∀ x k, k < O.cutLength x →
    FGBlock.Preceq (R.core (O.cutState x k)).fg.F (R.core (O.cutState x (k + 1))).fg.F
  restore_f : ∀ j x t, rho.events[j]? = some (.restart x t) →
    (R.core (O.cutState x (O.entry x j))).fg.F = (R.core (O.cutState x (O.start x j))).fg.F

/-! ### Ordinary Duty fold instance (three local cuts per event) -/

/-- The raw entry of one event at receiver `x`. -/
def ordinaryEntryStep (x : V) (st : P.State) : V2.Event V P.Object → P.State
  | .restart y t => if y = x then P.restore (P.durable st) t else st
  | .tick y t => if y = x then P.clock st t else st
  | .deliver y o _ => if y = x then P.process st o else st

theorem ordinaryEntryStep_def (x : V) (st : P.State) (e : V2.Event V P.Object) :
    ordinaryEntryStep x st e =
      V2.Event.rec (motive := fun _ => P.State)
        (fun y t => if y = x then P.restore (P.durable st) t else st)
        (fun y t => if y = x then P.clock st t else st)
        (fun y o _ => if y = x then P.process st o else st) e := by
  cases e <;> rfl

/-- The ordinary release of one event at receiver `x`, read after the clock. -/
def ordinaryReleaseStep (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (st : P.State) :
    V2.Event V P.Object → List P.Object
  | .tick y t => if y = x then dependencyReleased E rho (P.clock st t) x t else []
  | _ => []

theorem ordinaryReleaseStep_def (E : Generic.Env V) (rho : V2.D.Run V P) (x : V)
    (st : P.State) (e : V2.Event V P.Object) :
    ordinaryReleaseStep E rho x st e =
      V2.Event.rec (motive := fun _ => List P.Object) (fun _ _ => [])
        (fun y t => if y = x then dependencyReleased E rho (P.clock st t) x t else [])
        (fun _ _ _ => []) e := by
  cases e <;> rfl

/-- The raw entry state of event `j` at receiver `x`. -/
def ordinaryEntry (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (j : Nat) : P.State :=
  ((rho.events[j]?).map (ordinaryEntryStep x (V2.D.Run.stateBefore E rho j x))).getD
    (V2.D.Run.stateBefore E rho j x)

theorem ordinaryEntry_def (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (j : Nat) :
    ordinaryEntry E rho x j =
      ((rho.events[j]?).map (ordinaryEntryStep x (V2.D.Run.stateBefore E rho j x))).getD
        (V2.D.Run.stateBefore E rho j x) := rfl

/-- Local cut `3j` is before event `j`, `3j+1` its raw entry, `3j+2` its completion. -/
def ordinaryCutState (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (k : Nat) :
    P.State :=
  if k % 3 = 0 then V2.D.Run.stateBefore E rho (k / 3) x
  else if k % 3 = 1 then ordinaryEntry E rho x (k / 3)
  else V2.D.Run.stateBefore E rho (k / 3 + 1) x

theorem ordinaryCutState_def (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (k : Nat) :
    ordinaryCutState E rho x k =
      if k % 3 = 0 then V2.D.Run.stateBefore E rho (k / 3) x
      else if k % 3 = 1 then ordinaryEntry E rho x (k / 3)
      else V2.D.Run.stateBefore E rho (k / 3 + 1) x := rfl

/-- The ordinary Duty fold as an execution observation. Own records complete in one
microstep, and no drain runs (`finish = id`). A delivery is accepted at its entry. -/
def ordinaryFGExecutionObs (E : Generic.Env V) (rho : V2.D.Run V P) :
    FGExecutionObs V P where
  stateBefore j x := V2.D.Run.stateBefore E rho j x
  cutLength _ := 3 * rho.events.length
  cutState x k := ordinaryCutState E rho x k
  cutTime _ k := ((rho.events[k / 3]?).map V2.Event.time).getD 0
  start _ j := 3 * j
  entry _ j := 3 * j + 1
  duty _ j := 3 * j + 1
  done _ j := 3 * j + 2
  released x j :=
    ((rho.events[j]?).map (ordinaryReleaseStep E rho x (V2.D.Run.stateBefore E rho j x))).getD []
  finish _ st := st
  accepts x k o := ∃ j wire t, rho.events[j]? = some (.deliver x wire t) ∧ k = 3 * j ∧
    o = fgEventToken rho x j wire t
  ownWrites x k := if k % 3 = 1 then (((rho.events[k / 3]?).map (ordinaryReleaseStep E rho x
    (V2.D.Run.stateBefore E rho (k / 3) x))).getD []).filter P.objSelfVisible else []

theorem ordinaryFGExecutionObs_def (E : Generic.Env V) (rho : V2.D.Run V P) :
    ordinaryFGExecutionObs E rho =
      { stateBefore := fun j x => V2.D.Run.stateBefore E rho j x
        cutLength := fun _ => 3 * rho.events.length
        cutState := fun x k => ordinaryCutState E rho x k
        cutTime := fun _ k => ((rho.events[k / 3]?).map V2.Event.time).getD 0
        start := fun _ j => 3 * j
        entry := fun _ j => 3 * j + 1
        duty := fun _ j => 3 * j + 1
        done := fun _ j => 3 * j + 2
        released := fun x j => ((rho.events[j]?).map
          (ordinaryReleaseStep E rho x (V2.D.Run.stateBefore E rho j x))).getD []
        finish := fun _ st => st
        accepts := fun x k o => ∃ j wire t, rho.events[j]? = some (.deliver x wire t) ∧
          k = 3 * j ∧ o = fgEventToken rho x j wire t
        ownWrites := fun x k => if k % 3 = 1 then (((rho.events[k / 3]?).map
          (ordinaryReleaseStep E rho x (V2.D.Run.stateBefore E rho (k / 3) x))).getD []).filter
            P.objSelfVisible else [] } := rfl

/-! ### Dependency-driver fold instance (statement only; E1F proves it) -/

/-- The driver release of one event at receiver `x`, read at the drained duty state. -/
def driverReleaseStep {Body : Type} (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (j : Nat) :
    V2.Event V P.Object → List P.Object
  | .tick y t => if y = x then
      dependencyReleased E rho (dependencyDutyState E rho F x j (.tick x t)) x t else []
  | _ => []

theorem driverReleaseStep_def {Body : Type} (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (x : V) (j : Nat) (e : V2.Event V P.Object) :
    driverReleaseStep E rho F x j e =
      V2.Event.rec (motive := fun _ => List P.Object) (fun _ _ => [])
        (fun y t => if y = x then
          dependencyReleased E rho (dependencyDutyState E rho F x j (.tick x t)) x t else [])
        (fun _ _ _ => []) e := by
  cases e <;> rfl

/-- The own record written by one executed driver operation. -/
def driverOwnWrite {Body Origin : Type} :
    FGDependencyOperation Body Origin P.Object → List P.Object
  | .ownRecord wire => [wire]
  | _ => []

theorem driverOwnWrite_def {Body Origin : Type}
    (op : FGDependencyOperation Body Origin P.Object) :
    driverOwnWrite op = FGDependencyOperation.rec (motive := fun _ => List P.Object)
      (fun _ _ => []) (fun _ _ _ => []) (fun _ _ => []) (fun _ _ => []) (fun _ _ => [])
      (fun _ => []) (fun _ => []) (fun wire => [wire]) (fun _ => []) (fun _ => [])
      (fun _ => []) (fun _ => []) [] op := by
  cases op <;> rfl

/-- The canonical driver observation of the c3 dependency fold. `T x` and `Op x` are the
finite trace and the executed operations of receiver `x`. Releases are read at the canonical
drained duty state, own records are followed by the second drain, and a delivery body is
accepted at its actual accepted leaf step. -/
def driverFGExecutionObs {Body : Type} (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object) :
    FGExecutionObs V P where
  stateBefore j x := dependencyStateBefore E rho F x j
  cutLength x := (T x).length
  cutState x k := (T x).state k
  cutTime x k := (T x).time k
  start x j := (T x).start j
  entry x j := (T x).entryCut j
  duty x j := (T x).dutyCut j
  done x j := (T x).done j
  released x j := ((rho.events[j]?).map (driverReleaseStep E rho F x j)).getD []
  finish _ st := F.drain st
  accepts x k o := k < (T x).length ∧ ∃ b, Op x k = .leaf b o .accepted
  ownWrites x k := if k < (T x).length then driverOwnWrite (Op x k) else []

theorem driverFGExecutionObs_def {Body : Type} (E : Generic.Env V) (rho : V2.D.Run V P)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object) :
    driverFGExecutionObs E rho F T Op =
      { stateBefore := fun j x => dependencyStateBefore E rho F x j
        cutLength := fun x => (T x).length
        cutState := fun x k => (T x).state k
        cutTime := fun x k => (T x).time k
        start := fun x j => (T x).start j
        entry := fun x j => (T x).entryCut j
        duty := fun x j => (T x).dutyCut j
        done := fun x j => (T x).done j
        released := fun x j => ((rho.events[j]?).map (driverReleaseStep E rho F x j)).getD []
        finish := fun _ st => F.drain st
        accepts := fun x k o => k < (T x).length ∧ ∃ b, Op x k = .leaf b o .accepted
        ownWrites := fun x k => if k < (T x).length then driverOwnWrite (Op x k) else [] } :=
  rfl

variable {LeafIn Body Row Latest : Type} {Leaf : V2.ProtocolSpecD LeafIn}

/-- The c3 trace laws of every receiver of the driver run. -/
def DriverTraceLaws (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop :=
  ∀ x, FGDependencyTraceLaws E rho x H W D L Step (T x) F (Op x) Arrival Notify
    leafState leafWire ActualRead

theorem DriverTraceLaws_def (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) :
    DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead =
      ∀ x, FGDependencyTraceLaws E rho x H W D L Step (T x) F (Op x) Arrival Notify
        leafState leafWire ActualRead := rfl

/-- Additive own-write trace of the driver run (the c3 run and read construction supplies
it): at each tick of a receiver the executed own-record operations over `[dutyCut, done)`
are exactly the self-visible release list at the drained duty state, in order; no other
operation of that receiver, in particular none at another receiver's entry, is an own
record. `DriverTraceLaws` alone does not imply these laws. -/
structure DriverOwnTraceLaws {Body : Type} (E : Generic.Env V) (rho : V2.D.Run V P)
    (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object) :
    Prop where
  own_ops : ∀ x j t, rho.events[j]? = some (.tick x t) →
    (List.range ((T x).done j - (T x).dutyCut j)).flatMap
        (fun i => driverOwnWrite (Op x ((T x).dutyCut j + i))) =
      (dependencyReleased E rho ((T x).state ((T x).dutyCut j)) x t).filter P.objSelfVisible
  own_only_ticks : ∀ x k, k < (T x).length → driverOwnWrite (Op x k) ≠ [] →
    ∃ j t, rho.events[j]? = some (.tick x t) ∧ (T x).dutyCut j ≤ k ∧ k < (T x).done j

/-- E1F obligation (PC line): the driver trace laws of every receiver and the additive
own-write trace give the shared execution laws of the canonical driver observation.
Stated here; not proved in X1a. -/
def DriverExecutionObsStatement (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) : Prop :=
  DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  DriverOwnTraceLaws E rho T Op →
  FGExecutionObsLaws E rho (driverFGExecutionObs E rho F T Op)

theorem DriverExecutionObsStatement_def (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) :
    DriverExecutionObsStatement E rho H W D L Step F T Op Arrival Notify leafState leafWire
        ActualRead =
      (DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire
        ActualRead →
      DriverOwnTraceLaws E rho T Op →
      FGExecutionObsLaws E rho (driverFGExecutionObs E rho F T Op)) := rfl

/-- Local step laws that the driver core obligation consumes. `Good` is a reachable
invariant; every executed microstep kind keeps TF and F and preserves `Good`; closed
`Good` states (the drained duty states) hold a HEAD in TF. -/
structure DriverCoreStepLaws (R : FGCoreReads P n Base Proposal Wire)
    (H : FGHistoricalReads P.State Body)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (Good : P.State → Prop) : Prop where
  good_init : Good P.init
  good_step : ∀ kind x st st', Step kind x st st' → Good st → Good st'
  tf_step : ∀ kind x st st', Step kind x st st' →
    (R.core st).fg.TF ⊆ (R.core st').fg.TF
  f_step : ∀ kind x st st', Step kind x st st' →
    FGBlock.Preceq (R.core st).fg.F (R.core st').fg.F
  parent_closed : ∀ st, Good st → ∀ B ∈ (R.core st).fg.TF, B.parent ∈ (R.core st).fg.TF
  head_mem : ∀ st s, Good st → dependencyClosed H D st →
    ∃ B ∈ (R.core st).fg.TF, R.erase B = R.headVote st s
  restore_tf : ∀ st t, (R.core (P.restore (P.durable st) t)).fg.TF = (R.core st).fg.TF
  restore_f : ∀ st t, (R.core (P.restore (P.durable st) t)).fg.F = (R.core st).fg.F

/-- E1F obligation (PC line): trace laws plus local step laws give the observed core and
finality laws of the canonical driver observation. Stated here; not proved in X1a. -/
def DriverObservedCoreStatement (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) (Good : P.State → Prop) : Prop :=
  DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire ActualRead →
  DriverCoreStepLaws R H D Step Good →
  FGObservedCoreLaws R rho (driverFGExecutionObs E rho F T Op) ∧
    FGObservedFinalityLaws R rho (driverFGExecutionObs E rho F T Op)

theorem DriverObservedCoreStatement_def (R : FGCoreReads P n Base Proposal Wire)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (H : FGHistoricalReads P.State Body) (W : FGDependencyWireReads P Body Row)
    (D : FGDependencyReads P.State Body (FGReceiptToken V P.Object) Latest)
    (L : FGDependencyLeaf P.State Body (FGReceiptToken V P.Object))
    (Step : FGDependencyStepKind → V → P.State → P.State → Prop)
    (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
    (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
    (Arrival : P.State → Body → FGReceiptToken V P.Object → P.State → Prop)
    (Notify : P.State → Body → P.State → Prop)
    (leafState : P.State → Leaf.State) (leafWire : P.Object → Leaf.Object)
    (ActualRead : V → Nat → P.State → Prop) (Good : P.State → Prop) :
    DriverObservedCoreStatement R E rho H W D L Step F T Op Arrival Notify leafState
        leafWire ActualRead Good =
      (DriverTraceLaws E rho H W D L Step F T Op Arrival Notify leafState leafWire
        ActualRead →
      DriverCoreStepLaws R H D Step Good →
      FGObservedCoreLaws R rho (driverFGExecutionObs E rho F T Op) ∧
        FGObservedFinalityLaws R rho (driverFGExecutionObs E rho F T Op)) := rfl

end AvailableChain.FGCompose
end
