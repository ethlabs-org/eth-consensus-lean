module
public import AvailableChainEngineV2.TestSupport.Engine

@[expose] public section

/-! Tests of the engine v2 core (plan 2a, Task 1 Step 6).

(a) A two-label spec with one seat per label and three events: emission and
the own record. (b) A restart and then a tick at the same time: the emission
comes from the state before the tick event, after the restart (Review Focus
1). (c) The input is a type parameter, and a protocol can ignore it (Review
Focus 5); the field list of `ProtocolSpec` is pinned. An asleep node releases
and records nothing (Review Focus 2). A tick reads the input of its node and
the post-clock state, in label order and then seat order. -/

namespace AvailableChain.V2.Tests

open AvailableChain AvailableChain.V2

/-- An environment in which every node is awake at every time. -/
def envAwake (V : Type) : Generic.Env V :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

/-- An environment in which every node is asleep at every time. -/
def envAsleep (V : Type) : Generic.Env V :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => false⟩

/-! ### (a) Two labels, one seat each -/

/-- Validator 0 holds both seats. Validator 0 ticks at 0, validator 1 gets an
object at 0, and validator 0 ticks at 1. -/
def rhoA : Run (Fin 2) specA where
  honest := ∅
  horizon := 1
  events := [.tick 0 0, .deliver 1 ⟨.seat false 0, 5⟩ 0, .tick 0 1]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

-- The tick at index 0 signs label `false` with seat 0; the payload is the state 0.
example : Run.emitsAt (envAwake _) rhoA 0 = [⟨.seat false 0, 0⟩] := rfl
-- A delivery event releases nothing.
example : Run.emitsAt (envAwake _) rhoA 1 = [] := rfl
-- Label `false` is not self-visible: the tick does not change the state.
example : Run.stateBefore (envAwake _) rhoA 1 0 = 0 := rfl
-- The delivery adds 5 + 1 at validator 1 only.
example : Run.stateBefore (envAwake _) rhoA 2 1 = 6 := rfl
example : Run.stateBefore (envAwake _) rhoA 2 0 = 0 := rfl
-- The tick at index 2 signs label `true` and records it (self-visible): 0 + 10.
example : Run.emitsAt (envAwake _) rhoA 2 = [⟨.seat true 0, 0⟩] := rfl
example : Run.stateBefore (envAwake _) rhoA 3 0 = 10 := rfl
example : Run.final (envAwake _) rhoA 0 = 10 ∧ Run.final (envAwake _) rhoA 1 = 6 :=
  ⟨rfl, rfl⟩
-- `emittedAt` finds the tick by node and time.
example : Run.emittedAt (envAwake _) rhoA 0 1 = [⟨.seat true 0, 0⟩] := rfl
example : Run.emittedAt (envAwake _) rhoA 1 1 = [] := rfl
-- Validator 1 holds no seat: its tick would release nothing.
example : (tick (envAwake _) rhoA 7 1 1).2 = [] := rfl
example : Run.holder rhoA (.seat true 0) = some 0 := rfl

/-! ### Review Focus 2: an asleep node releases and records nothing -/

example : Run.emitsAt (envAsleep _) rhoA 2 = [] := rfl
example : Run.stateBefore (envAsleep _) rhoA 3 0 = 0 := rfl
example : Run.emittedAt (envAsleep _) rhoA 0 1 = [] := rfl

/-! ### Tick semantics: input, post-clock state, seat order, label order -/

/-- The duties of `specM`: labels `true` and `false` at time 3, in this order. -/
def dutiesM (t : Time) : List Bool := if t = 3 then [true, false] else []

/-- Label `true` has two seats, label `false` one; both are due at time 3. The
clock adds the time, and `act` adds the input to the state. -/
abbrev specM : ProtocolSpec Int where
  State := Int
  Label := Bool
  seats := fun b => if b then 2 else 1
  Payload := Int
  Durable := Unit
  init := 0
  clock := fun s t => s + t
  actTime := fun _ => 3
  duties := dutiesM
  duties_spec := by
    intro ℓ t
    by_cases h : t = 3
    · cases ℓ <;> simp [dutiesM, h]
    · simp [dutiesM, h, eq_comm]
  duties_nodup := by
    intro t
    unfold dutiesM
    split_ifs <;> simp
  act := fun s _ x => some (s + x)
  gossip := fun _ _ => []
  process := fun s _ => s
  selfVisible := fun _ => false
  recordOwn := fun s _ => s
  durable := fun _ => ()
  restore := fun _ _ => 0
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-- Validator 1 holds every seat and ticks at time 3; its input is `100 * v + t`. -/
def rhoM : Run (Fin 2) specM where
  honest := ∅
  horizon := 3
  events := [.tick 1 3]
  seatOf := fun _ _ => 1
  input := fun v t => 100 * (v : Int) + t

-- Every payload is 106 = (0 + 3) + 103: the post-clock state (not 0) plus the
-- input of validator 1 at time 3 (not 3, validator 0's input). Label `true`
-- comes first (the order of `duties 3`), and its seats come in seat order.
example : Run.emitsAt (envAwake _) rhoM 0 =
    [⟨.seat true ⟨0, by decide⟩, 106⟩, ⟨.seat true ⟨1, by decide⟩, 106⟩,
      ⟨.seat false ⟨0, by decide⟩, 106⟩] := rfl

/-! ### (b) Restart, then a tick at the same time (Review Focus 1) -/

/-- The duties of `specB`: its one label at time 5. -/
def dutiesB (t : Time) : List Unit := if t = 5 then [()] else []

/-- One label with one seat, due at time 5. The clock keeps the state, `act`
emits the state, a delivery sets the state to the payload, and a restart
restores 0. -/
abbrev specB : ProtocolSpec Unit where
  State := Nat
  Label := Unit
  seats := fun _ => 1
  Payload := Nat
  Durable := Unit
  init := 0
  clock := fun s _ => s
  actTime := fun _ => 5
  duties := dutiesB
  duties_spec := by
    intro ℓ t
    by_cases h : t = 5 <;> simp [dutiesB, h, eq_comm]
  duties_nodup := by
    intro t
    unfold dutiesB
    split_ifs <;> simp
  act := fun s _ _ => some s
  gossip := fun _ _ => []
  process := fun _ o => o.payload
  selfVisible := fun _ => false
  recordOwn := fun s _ => s
  durable := fun _ => ()
  restore := fun _ _ => 0
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-- The state becomes 1 at time 4; at time 5 a restart (phase 0) comes before
the tick (phase 1). -/
def rhoB : Run Unit specB where
  honest := ∅
  horizon := 5
  events := [.deliver () ⟨.none, 1⟩ 4, .restart () 5, .tick () 5]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

-- The state before time 5 is 1, but the tick emits 0: the restart at the same
-- time comes before the tick event, and emission reads the state at its index.
example : Run.stateBeforeTime (envAwake _) rhoB 5 () = 1 := rfl
example : Run.stateBefore (envAwake _) rhoB 2 () = 0 := rfl
example : Run.emittedAt (envAwake _) rhoB () 5 = [⟨.seat () 0, 0⟩] := rfl
example : Run.emitsAt (envAwake _) rhoB 2 = [⟨.seat () 0, 0⟩] := rfl
-- The same through the laws.
example : Run.emittedAt (envAwake _) rhoB () 5 =
    (tick (envAwake _) rhoB (Run.stateBefore (envAwake _) rhoB 2 ()) () 5).2 := by
  rw [Run.emittedAt_eq_emitsAt _ (by decide) (i := 2) rfl]
  exact (Run.step_tick_eq _ rhoB (i := 2) rfl).2

/-! ### (c) The input is a type parameter -/

/-- A spec that ignores its input, at every input type. -/
abbrev ignoring (In : Type) : ProtocolSpec In :=
  { specB with act := fun s _ _ => some s }

example : ProtocolSpec Nat := ignoring Nat
example : ProtocolSpec Unit := ignoring Unit

/-- The run of (b) for `ignoring Nat`, with the input stream `f`. -/
def rhoC (f : Unit → Time → Nat) : Run Unit (ignoring Nat) where
  honest := ∅
  horizon := 5
  events := [.deliver () ⟨.none, 1⟩ 4, .restart () 5, .tick () 5]
  seatOf := fun _ _ => ()
  input := f

-- Two different input streams give the same emission: the protocol ignores
-- its input, although the run supplies one.
example : Run.emittedAt (envAwake _) (rhoC fun _ _ => 3) () 5 =
    Run.emittedAt (envAwake _) (rhoC fun _ _ => 7) () 5 := rfl

-- The input type is the parameter of `ProtocolSpec`, and no field is named `input`.
/-- info: ProtocolSpec : Type → Type 1 -/
#guard_msgs in
#check (ProtocolSpec : Type → Type 1)
/-- error: Unknown constant `AvailableChain.V2.ProtocolSpec.input` -/
#guard_msgs in
#check @ProtocolSpec.input

-- The field list of `ProtocolSpec`, pinned (plan 2a, Task 1 Interfaces).
run_cmd do
  let fs := Lean.getStructureFields (← Lean.getEnv) ``ProtocolSpec
  unless fs.toList == [`State, `Label, `seats, `Payload, `Durable, `init, `clock, `actTime,
      `duties, `duties_spec, `duties_nodup, `act, `gossip, `process, `selfVisible, `recordOwn,
      `durable, `restore, `wellFormed, `depsPresent, `processed, `excludes, `handles,
      `carries] do
    throwError "unexpected ProtocolSpec fields: {fs}"

end AvailableChain.V2.Tests

end
