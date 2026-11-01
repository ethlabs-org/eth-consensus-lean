module
public import Mathlib.Data.Finset.Basic -- shake: keep (re-export)
public import Mathlib.Data.Prod.Lex -- shake: keep (re-export)
public import Mathlib.Logic.Function.Basic -- shake: keep (re-export)
public import AvailableChainModel.Generic.Env -- shake: keep (re-export)
public import AvailableChainEngineV2.Engine.Run
public import AvailableChainEngineV2.Engine.Duty.Spec

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

abbrev World (V : Type) {In : Type} (P : ProtocolSpecD In) := V → P.State

def World.init {V : Type} {In : Type} {P : ProtocolSpecD In} : World V P := fun _ => P.init

structure Run (V : Type) {In : Type} (P : ProtocolSpecD In) where
  honest : Finset V
  horizon : Time
  events : List (Event V P.Object)
  seatOf : (ℓ : P.Label) → Fin (P.seats ℓ) → V
  input : V → Time → In

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

def Run.ownSeats (rho : Run V P) (ℓ : P.Label) (v : V) : List (Fin (P.seats ℓ)) :=
  (List.finRange (P.seats ℓ)).filter (fun i => decide (rho.seatOf ℓ i = v))

def tick (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    P.State × List P.Object :=
  let st' := P.clock st t
  let released : List P.Object :=
    if E.awake v t then
      (P.duties t).flatMap (fun d =>
          (rho.ownSeats (P.signLabel d) v).filterMap (fun i =>
            (P.act st' d (rho.input v t)).map (fun p => ⟨.seat (P.signLabel d) i, p⟩))) ++
        (P.gossip st' t).map (fun p => ⟨.none, p⟩)
    else []
  ((released.filter P.objSelfVisible).foldl P.recordOwn st', released)

namespace World

def step (E : Generic.Env V) (rho : Run V P) (w : World V P) :
    Event V P.Object → World V P
  | .restart v t => Function.update w v (P.restore (P.durable (w v)) t)
  | .tick v t => Function.update w v (tick E rho (w v) v t).1
  | .deliver v o _ => Function.update w v (P.process (w v) o)
end World

namespace Run

def stateBefore (E : Generic.Env V) (rho : Run V P) (i : Nat) : World V P :=
  (rho.events.take i).foldl (World.step E rho) World.init

def actionCut (rho : Run V P) (a : Time) : Nat :=
  (rho.events.filter (fun e =>
    decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))).length

def stateAfterRestartsAt (E : Generic.Env V) (rho : Run V P)
    (a : Time) : World V P :=
  stateBefore E rho (actionCut rho a)


def stateBeforeTime (E : Generic.Env V) (rho : Run V P) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time < t))).foldl (World.step E rho) World.init

def readAt (E : Generic.Env V) (rho : Run V P) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldl (World.step E rho) World.init

def final (E : Generic.Env V) (rho : Run V P) : World V P :=
  rho.events.foldl (World.step E rho) World.init

def emitsAt (E : Generic.Env V) (rho : Run V P) (i : Nat) : List P.Object :=
  match rho.events[i]? with
  | some (.tick v t) => (tick E rho (stateBefore E rho i v) v t).2
  | _ => []

def tickIdx? (rho : Run V P) (v : V) (t : Time) : Option Nat :=
  rho.events.findIdx? (fun e => match e with
    | .tick v' t' => decide (v' = v ∧ t' = t)
    | _ => false)

def emittedAt (E : Generic.Env V) (rho : Run V P) (v : V) (t : Time) : List P.Object :=
  match tickIdx? rho v t with
  | some i => emitsAt E rho i
  | none => []

def emits (E : Generic.Env V) (rho : Run V P) (v : V) (o : P.Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧ o ∈ emitsAt E rho i

def processes (rho : Run V P) (v : V) (o : P.Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.deliver v o t)

def handlesAt (E : Generic.Env V) (rho : Run V P) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  ∃ o', rho.events[i]? = some (.deliver v o' t) ∧
    P.handles (stateBefore E rho i v) o' o

def acceptsAt (E : Generic.Env V) (rho : Run V P) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  handlesAt E rho i v o t ∧ P.processed (stateBefore E rho i v) o = false ∧
    P.processed (stateBefore E rho (i + 1) v) o = true

def holder (rho : Run V P) : Auth P.Label P.seats → Option V
  | .seat ℓ i => some (rho.seatOf ℓ i)
  | .none => none

theorem stateBefore_succ (E : Generic.Env V) (rho : Run V P) {i : Nat}
    {e : Event V P.Object} (h : rho.events[i]? = some e) :
    stateBefore E rho (i + 1) = World.step E rho (stateBefore E rho i) e := by
  simp [stateBefore, List.take_add_one, h, List.foldl_append]

theorem step_tick_eq (E : Generic.Env V) (rho : Run V P) {i : Nat} {v : V} {t : Time}
    (h : rho.events[i]? = some (.tick v t)) :
    stateBefore E rho (i + 1) v = (tick E rho (stateBefore E rho i v) v t).1 ∧
      emitsAt E rho i = (tick E rho (stateBefore E rho i v) v t).2 := by
  refine ⟨?_, ?_⟩
  · rw [stateBefore_succ E rho h]
    simp [World.step]
  · simp [emitsAt, h]

end Run

theorem tick_decomp (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V)
    (t : Time) :
    (tick E rho st v t).1 =
      ((tick E rho st v t).2.filter P.objSelfVisible).foldl P.recordOwn (P.clock st t) :=
  rfl

theorem tick_asleep (E : Generic.Env V) (rho : Run V P) (st : P.State) {v : V}
    {t : Time} (h : E.awake v t = false) :
    tick E rho st v t = (P.clock st t, []) := by
  simp [tick, h]

namespace Run

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

end AvailableChain.V2.D

end
