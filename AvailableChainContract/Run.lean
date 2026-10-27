module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Defs
public import AvailableChainModel.Generic.Env
public import AvailableChainContract.Protocol

@[expose] public section

/-! # Runs and the engine

A run fixes everything that the protocol does not choose: the honest set, the
horizon, the scheduler's events, the committee seats, the slot proposers and
the inputs. The engine runs the protocol on these events. It keeps, for each
node, the protocol state and the `seen` log of every object the node released
or received.

At a tick the engine signs, for an awake node, in this order:
1. the proposal of every slot whose proposal time is now and whose proposer is
   the node: the block `node parent s (own input) aux`, from the protocol's
   choice of `parent` and `aux`, signed with the proposer key of the slot;
2. the node's seat of every due duty;
3. unsigned gossip.
All candidates are built from the state after the clock update. The engine then
goes through them in this order and releases a candidate only if every object
it carries is already in the closure of `seen`, so honest code never passes on
an object it has not seen (in particular, no honest signature that it did not
receive or make). A released object enters `seen` before the next candidate is
checked, so a candidate can carry an object released earlier in the same tick
(for example gossip carrying the node's own vote, but not a proposal carrying a
vote of the same tick), and the protocol records it with `recordOwn`. -/

namespace AvailableChain.Contract

open AvailableChain.Generic

/-- A scheduler event at a node: a tick, the delivery of an object, or a
restart (which the conditions allow only at a wake). -/
inductive Event (V O : Type) where
  | tick (v : V) (t : Time)
  | deliver (v : V) (o : O) (t : Time)
  | restart (v : V) (t : Time)
  deriving DecidableEq

namespace Event
variable {V O : Type}
def time : Event V O → Time
  | tick _ t => t
  | deliver _ _ t => t
  | restart _ t => t
def node : Event V O → V
  | tick v _ => v
  | deliver v _ _ => v
  | restart v _ => v
/-- Restarts come first at a time, then ticks, then deliveries. -/
def phase : Event V O → Nat
  | restart _ _ => 0
  | tick _ _ => 1
  | deliver _ _ _ => 2
def key (e : Event V O) : Time × Nat := (e.time, e.phase)
/-- Lexicographic order of keys. -/
def keyLe (e f : Event V O) : Prop :=
  e.time < f.time ∨ (e.time = f.time ∧ e.phase ≤ f.phase)
end Event

/-- The public parameters of an environment. -/
def pubOf {V : Type} [Fintype V] (E : Env V) : Public :=
  ⟨Fintype.card V, E.Δ, E.Δ_pos⟩

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The protocol that family `F` runs in environment `E`. -/
abbrev protoOf (F : Family) (E : Env V) : Protocol (pubOf E) := F (pubOf E)

/-- A run of family `F` in environment `E`. -/
structure Run (F : Family) (E : Env V) where
  honest : Finset V
  horizon : Time
  events : List (Event V (protoOf F E).Object)
  /-- The committee of every label: a bijection from its seats to validators. -/
  seat : (protoOf F E).Label → Fin (Fintype.card V) ≃ V
  /-- The proposer of every slot. -/
  proposer : Slot → V
  /-- The application input of every validator at every time. -/
  input : V → Time → Nat

variable {F : Family} {E : Env V}

/-- An engine node: the protocol state and the `seen` log. -/
structure Node {pub : Public} (P : Protocol pub) where
  st : P.State
  seen : List P.Object

/-- The initial world. -/
def initWorld (F : Family) (E : Env V) : V → Node (protoOf F E) :=
  fun _ => ⟨(protoOf F E).init, []⟩

/-- The closure of a list of objects: the objects and everything they carry. -/
def closure {pub : Public} {P : Protocol pub} (l : List P.Object) : List P.Object :=
  l.flatMap Obj.parts

/-- Release candidates in order: a candidate is released if everything it
carries is in the closure of `seen`; released objects join `seen` at once. -/
def releaseAll {pub : Public} {P : Protocol pub} :
    Node P → List P.Object → Node P × List P.Object
  | nd, [] => (nd, [])
  | nd, c :: cs =>
    if c.carried.all (fun x => decide (x ∈ closure nd.seen)) then
      let nd' : Node P := ⟨P.recordOwn nd.st c, nd.seen ++ [c]⟩
      let r := releaseAll nd' cs
      (r.1, c :: r.2)
    else releaseAll nd cs

namespace Run

variable (rho : Run F E)

/-- The candidates of node `v` at time `t` in state `st`. -/
def candidates (st : (protoOf F E).State) (v : V) (t : Time) :
    List (protoOf F E).Object :=
  let P := protoOf F E
  let props : List P.Object :=
    match P.slotAt? t with
    | some s =>
      if rho.proposer s = v then
        match P.propose st s with
        | some (par, aux, cs) => [.mk (.proposer s) (.prop (.node par s (rho.input v t) aux)) cs]
        | none => []
      else []
    | none => []
  let votes : List P.Object :=
    (P.duties t).filterMap (fun d =>
      (P.act st d).map (fun bc =>
        .mk (.vote (P.label d) ((rho.seat (P.label d)).symm v)) (.data bc.1) bc.2))
  let gossip : List P.Object :=
    (P.gossip st t).map (fun bc => .mk .none (.data bc.1) bc.2)
  props ++ votes ++ gossip

/-- A tick: the clock, then (if awake) signing and release. -/
def tick (nd : Node (protoOf F E)) (v : V) (t : Time) :
    Node (protoOf F E) × List (protoOf F E).Object :=
  let nd₁ : Node (protoOf F E) := ⟨(protoOf F E).clock nd.st t, nd.seen⟩
  if E.awake v t then releaseAll nd₁ (rho.candidates nd₁.st v t) else (nd₁, [])

/-- One event. -/
def step (w : V → Node (protoOf F E)) : Event V (protoOf F E).Object → V → Node (protoOf F E)
  | .tick v t => Function.update w v (rho.tick (w v) v t).1
  | .deliver v o _ =>
      Function.update w v ⟨(protoOf F E).process (w v).st o, (w v).seen ++ [o]⟩
  | .restart v t =>
      Function.update w v
        ⟨(protoOf F E).restore ((protoOf F E).durable (w v).st) t, (w v).seen⟩


/-- The world before event `i`. -/
def stateBefore (i : Nat) : V → Node (protoOf F E) :=
  (rho.events.take i).foldl rho.step (initWorld F E)

/-- The world after every event up to and including time `t`. -/
def readAt (t : Time) : V → Node (protoOf F E) :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldl rho.step (initWorld F E)

/-- The objects released by the tick at index `i`. -/
def releasesAt (i : Nat) : List (protoOf F E).Object :=
  match rho.events[i]? with
  | some (.tick v t) => (rho.tick (rho.stateBefore i v) v t).2
  | _ => []

/-- Node `v` released `o` at its tick at `t`. -/
def releases (v : V) (o : (protoOf F E).Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (Event.tick v t) ∧ o ∈ rho.releasesAt i

/-- Node `v` received `o` at `t`. -/
def receives (v : V) (o : (protoOf F E).Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (Event.deliver v o t)

/-- What node `v` has seen by time `t`: every object it released or received
by `t`, with everything those objects carry. -/
def View (v : V) (t : Time) : Set (protoOf F E).Object :=
  {o | ∃ o₀ t₀, t₀ ≤ t ∧ (rho.releases v o₀ t₀ ∨ rho.receives v o₀ t₀) ∧ Obj.Contains o₀ o}

/-- What node `v` has seen before event `i` (the event cut `i`): every object
it released or received at an event with index `< i`, with everything those
objects carry. -/
def ViewIdx (v : V) (i : Nat) : Set (protoOf F E).Object :=
  {o | ∃ k o₀, k < i ∧
    ((∃ t, rho.events[k]? = some (Event.tick v t) ∧ o₀ ∈ rho.releasesAt k) ∨
      ∃ t, rho.events[k]? = some (Event.deliver v o₀ t)) ∧ Obj.Contains o₀ o}

/-- Everything the honest nodes saw in the run. -/
def Observed : Set (protoOf F E).Object :=
  {o | ∃ v ∈ rho.honest, o ∈ rho.ViewIdx v rho.events.length}

/-- The number of events before time `t`. On a time-sorted run the events
before time `t` are exactly the first `cutAt t` events. -/
def cutAt (t : Time) : Nat := (rho.events.filter (fun e => decide (e.time < t))).length

/-- The time of event cut `i`: the time of the last event before it (`0` for
the empty cut). -/
def cutTime (i : Nat) : Time :=
  match i with
  | 0 => 0
  | k + 1 => match rho.events[k]? with
    | some e => e.time
    | none => 0

/-- The validator that holds an authentication. -/
def holder : Auth (protoOf F E).Label (Fintype.card V) → Option V
  | .vote ℓ i => some (rho.seat ℓ i)
  | .proposer s => some (rho.proposer s)
  | .none => none

/-- An output of node `v` at time `t`. -/
def readOut (g : (protoOf F E).State → CBlock) (v : V) (t : Time) : CBlock :=
  g (rho.readAt t v).st

/-- An output of node `v` at event cut `i`: after the first `i` events. A
client can expose the state between any two events, so safety is stated at
event cuts. -/
def readIdx (g : (protoOf F E).State → CBlock) (v : V) (i : Nat) : CBlock :=
  g (rho.stateBefore i v).st

/-- `B` is the honest proposal of slot `s`: the proposer of `s` is honest and
released, at the proposal time, a proposal of `B` under the slot's key. -/
def HonestProposal (s : Slot) (B : CBlock) : Prop :=
  rho.proposer s ∈ rho.honest ∧
    ∃ cs, rho.releases (rho.proposer s) (.mk (.proposer s) (.prop B) cs)
      ((protoOf F E).proposalTime s)

end Run

end AvailableChain.Contract

end
