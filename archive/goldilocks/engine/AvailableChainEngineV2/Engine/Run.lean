module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Logic.Function.Basic
public import AvailableChainModel.Generic.Env
public import AvailableChainEngineV2.Engine.Spec

@[expose] public section

namespace AvailableChain.V2

open AvailableChain

/-- A scheduler event at a node: a restart, its local clock tick, or the
delivery of one object (design §2 E6). -/
inductive Event (V Object : Type) where
  | restart (v : V) (t : Time)
  | tick (v : V) (t : Time)
  | deliver (v : V) (object : Object) (t : Time)
  deriving DecidableEq

namespace Event
variable {V Object : Type}
def time : Event V Object → Time
  | .restart _ t => t
  | .tick _ t => t
  | .deliver _ _ t => t
def node : Event V Object → V
  | .restart v _ => v
  | .tick v _ => v
  | .deliver v _ _ => v
def object? : Event V Object → Option Object
  | .restart _ _ => none
  | .tick _ _ => none
  | .deliver _ object _ => some object
def phase : Event V Object → Nat
  | .restart _ _ => 0
  | .tick _ _ => 1
  | .deliver _ _ _ => 2
/-- Event order is lexicographic by time and phase. At one time, restarts come
first, then ticks, then deliveries; equal-phase events keep their list
order. -/
def key (e : Event V Object) : Lex (Time × Nat) := toLex (e.time, e.phase)
end Event

/-- Every node's local state. -/
abbrev World (V : Type) {In : Type} (P : ProtocolSpec In) := V → P.State

/-- The initial world: every node is in the initial state. -/
def World.init {V : Type} {In : Type} {P : ProtocolSpec In} : World V P := fun _ => P.init

/-- A run: the honest set, the horizon, the event list, and the hidden
run data. `seatOf ℓ i` is the validator that holds seat `i` of label `ℓ`; it
need not be a bijection (committee models are conditions, design §2 E2).
`input v t` is the input of validator `v` at time `t`. Claims quantify over
all runs, so over all seat maps and all inputs. -/
structure Run (V : Type) {In : Type} (P : ProtocolSpec In) where
  honest : Finset V
  horizon : Time
  events : List (Event V P.Object)
  seatOf : (ℓ : P.Label) → Fin (P.seats ℓ) → V
  input : V → Time → In

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- The seats of label `ℓ` that `v` holds in this run, in seat order. -/
def Run.ownSeats (rho : Run V P) (ℓ : P.Label) (v : V) : List (Fin (P.seats ℓ)) :=
  (List.finRange (P.seats ℓ)).filter (fun i => decide (rho.seatOf ℓ i = v))

/-- The atomic tick of `v` at time `t` from state `st` (design §2 E5). It
returns the state after the tick and the released objects.

First the clock runs. An asleep node then releases nothing. An awake node
signs, with each of its seats of each due label, the label's payload from the
post-clock state and its input; the objects come in label order, then seat
order, and then unsigned gossip. Then the own record (`recordOwn`) is folded
over the released self-visible objects, in release order. -/
def tick (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    P.State × List P.Object :=
  let st' := P.clock st t
  let released : List P.Object :=
    if E.awake v t then
      (P.duties t).flatMap (fun ℓ =>
          (rho.ownSeats ℓ v).filterMap (fun i =>
            (P.act st' ℓ (rho.input v t)).map (fun p => ⟨.seat ℓ i, p⟩))) ++
        (P.gossip st' t).map (fun p => ⟨.none, p⟩)
    else []
  ((released.filter P.objSelfVisible).foldl P.recordOwn st', released)

namespace World
/-- A restart restores the durable part; a tick runs the atomic `tick`; a
delivery runs `process`. -/
def step (E : Generic.Env V) (rho : Run V P) (w : World V P) :
    Event V P.Object → World V P
  | .restart v t => Function.update w v (P.restore (P.durable (w v)) t)
  | .tick v t => Function.update w v (tick E rho (w v) v t).1
  | .deliver v o _ => Function.update w v (P.process (w v) o)
end World

namespace Run

/-- Events before index `i` have been folded into the returned world. A
restart at the time of event `i` (phase 0) is therefore included when it
comes before index `i`. -/
def stateBefore (E : Generic.Env V) (rho : Run V P) (i : Nat) : World V P :=
  (rho.events.take i).foldl (World.step E rho) World.init

def actionCut (rho : Run V P) (a : Time) : Nat :=
  (rho.events.filter (fun e =>
    decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))).length

def stateAfterRestartsAt (E : Generic.Env V) (rho : Run V P)
    (a : Time) : World V P :=
  stateBefore E rho (actionCut rho a)

/-- The returned world includes events strictly before time `t`. -/
def stateBeforeTime (E : Generic.Env V) (rho : Run V P) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time < t))).foldl (World.step E rho) World.init
/-- The returned world includes events up to and including time `t`. -/
def readAt (E : Generic.Env V) (rho : Run V P) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldl (World.step E rho) World.init
/-- The returned world includes the complete event list. -/
def final (E : Generic.Env V) (rho : Run V P) : World V P :=
  rho.events.foldl (World.step E rho) World.init

/-- The objects that the event at index `i` releases: the released objects of
the atomic tick, from the state just before that event, if it is a tick;
otherwise nothing. -/
def emitsAt (E : Generic.Env V) (rho : Run V P) (i : Nat) : List P.Object :=
  match rho.events[i]? with
  | some (.tick v t) => (tick E rho (stateBefore E rho i v) v t).2
  | _ => []

/-- The index of the first tick of `v` at time `t`, if any. -/
def tickIdx? (rho : Run V P) (v : V) (t : Time) : Option Nat :=
  rho.events.findIdx? (fun e => match e with
    | .tick v' t' => decide (v' = v ∧ t' = t)
    | _ => false)

/-- The objects that the (first) tick of `v` at time `t` releases; nothing if
there is no such tick. -/
def emittedAt (E : Generic.Env V) (rho : Run V P) (v : V) (t : Time) : List P.Object :=
  match tickIdx? rho v t with
  | some i => emitsAt E rho i
  | none => []

/-- An object appears in the output of a tick of `v` at time `t`. -/
def emits (E : Generic.Env V) (rho : Run V P) (v : V) (o : P.Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧ o ∈ emitsAt E rho i

/-- A delivery of the object to the node. Delivery records the handler call
even when the handler rejects; carried children are covered by
`handlesAt`. -/
def processes (rho : Run V P) (v : V) (o : P.Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.deliver v o t)

/-- The handler call recorded at index `i`. A handler call may reject the object;
the false-to-true `processed` transition belongs to `acceptsAt`. -/
def handlesAt (E : Generic.Env V) (rho : Run V P) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  ∃ o', rho.events[i]? = some (.deliver v o' t) ∧
    P.handles (stateBefore E rho i v) o' o

/-- An accepted call is a handler call that flips `processed` from `false` to
`true`. -/
def acceptsAt (E : Generic.Env V) (rho : Run V P) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  handlesAt E rho i v o t ∧ P.processed (stateBefore E rho i v) o = false ∧
    P.processed (stateBefore E rho (i + 1) v) o = true

/-- The validator that holds an authentication in this run, if any. -/
def holder (rho : Run V P) : Auth P.Label P.seats → Option V
  | .seat ℓ i => some (rho.seatOf ℓ i)
  | .none => none

/-! Laws of the atomic tick and of emission (plan 2a, Task 1). -/

/-- The world after event `i` is one step of that event from the world
before it. -/
theorem stateBefore_succ (E : Generic.Env V) (rho : Run V P) {i : Nat}
    {e : Event V P.Object} (h : rho.events[i]? = some e) :
    stateBefore E rho (i + 1) = World.step E rho (stateBefore E rho i) e := by
  simp [stateBefore, List.take_add_one, h, List.foldl_append]

/-- Emission equals the actual tick (Astra A01): after the tick event at
index `i`, the state of `v` is the post-tick state of `tick`, from the state
before that event, and the event releases the objects of the same `tick`. -/
theorem step_tick_eq (E : Generic.Env V) (rho : Run V P) {i : Nat} {v : V} {t : Time}
    (h : rho.events[i]? = some (.tick v t)) :
    stateBefore E rho (i + 1) v = (tick E rho (stateBefore E rho i v) v t).1 ∧
      emitsAt E rho i = (tick E rho (stateBefore E rho i v) v t).2 := by
  refine ⟨?_, ?_⟩
  · rw [stateBefore_succ E rho h]
    simp [World.step]
  · simp [emitsAt, h]

end Run

/-- The post-tick state is the own record folded over the released
self-visible objects, from the post-clock state. -/
theorem tick_decomp (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V)
    (t : Time) :
    (tick E rho st v t).1 =
      ((tick E rho st v t).2.filter P.objSelfVisible).foldl P.recordOwn (P.clock st t) :=
  rfl

/-- An asleep node releases nothing and records nothing: only its clock
runs. -/
theorem tick_asleep (E : Generic.Env V) (rho : Run V P) (st : P.State) {v : V}
    {t : Time} (h : E.awake v t = false) :
    tick E rho st v t = (P.clock st t, []) := by
  simp [tick, h]

namespace Run

/-- `tickIdx?` finds a tick of `v` at time `t`. -/
theorem tickIdx?_spec {rho : Run V P} {v : V} {t : Time} {i : Nat}
    (h : tickIdx? rho v t = some i) : rho.events[i]? = some (.tick v t) := by
  rw [tickIdx?, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, hp, -⟩ := h
  rw [List.getElem?_eq_getElem hi]
  revert hp
  cases rho.events[i] with
  | tick v' t' => simp only [decide_eq_true_eq]; rintro ⟨rfl, rfl⟩; rfl
  | restart _ _ => simp
  | deliver _ _ _ => simp

/-- With no second equal event (`hnodup`, the `nodup` field of the schedule
condition), the tick of `v` at time `t` at index `i` is the one that
`emittedAt` reads. -/
theorem emittedAt_eq_emitsAt (E : Generic.Env V) {rho : Run V P} {v : V} {t : Time}
    {i : Nat} (hnodup : rho.events.Nodup) (h : rho.events[i]? = some (.tick v t)) :
    emittedAt E rho v t = emitsAt E rho i := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp h).1
  have hpi : (match rho.events[i] with
      | .tick v' t' => decide (v' = v ∧ t' = t)
      | _ => false) = true := by
    rw [(List.getElem?_eq_some_iff.mp h).2]; simp
  obtain ⟨j, hj⟩ : ∃ j, tickIdx? rho v t = some j := by
    rw [tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
    exact ⟨rho.events[i], List.getElem_mem hi, hpi⟩
  have hj' := tickIdx?_spec hj
  have hji : j = i := by
    have hjl : j < rho.events.length := (List.getElem?_eq_some_iff.mp hj').1
    refine (hnodup.getElem_inj_iff (hi := hjl) (hj := hi)).mp ?_
    rw [(List.getElem?_eq_some_iff.mp hj').2, (List.getElem?_eq_some_iff.mp h).2]
  simp [emittedAt, hj, hji]

/-- With no second equal event (`hnodup`), `emittedAt` reports exactly the
objects that some tick of `v` at time `t` releases. Plan 2a Task 2 gives
`hnodup` from `ScheduleWellFormed`. -/
theorem mem_emittedAt_iff_emits (E : Generic.Env V) {rho : Run V P} {v : V}
    {o : P.Object} {t : Time} (hnodup : rho.events.Nodup) :
    o ∈ emittedAt E rho v t ↔ emits E rho v o t := by
  constructor
  · intro ho
    cases hj : tickIdx? rho v t with
    | none => simp [emittedAt, hj] at ho
    | some j =>
        refine ⟨j, tickIdx?_spec hj, ?_⟩
        simpa [emittedAt, hj] using ho
  · rintro ⟨i, hi, ho⟩
    rwa [emittedAt_eq_emitsAt E hnodup hi]

end Run

end AvailableChain.V2

end
