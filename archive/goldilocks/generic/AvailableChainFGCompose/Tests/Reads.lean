module
public import AvailableChainFGCompose.Statements.EventReads

public section

namespace AvailableChain.FGCompose.Tests

abbrev toy : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Unit
  signLabel := id
  seats := fun _ => 1
  Payload := Unit
  Durable := Unit
  init := 5
  clock := fun st _ => st + 10
  actTime := fun _ => 1
  duties := fun t => if t = 1 then [()] else []
  duties_spec := by intro d t; cases d; simp [eq_comm]
  duties_nodup := by intro t; split <;> simp
  act := fun _ _ _ => some ()
  gossip := fun _ _ => []
  process := fun st _ => st + 100
  selfVisible := fun _ => true
  recordOwn := fun st _ => st + 1
  durable := fun _ => ()
  restore := fun _ _ => 0
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

def env : Generic.Env (Fin 2) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

abbrev object : toy.Object := ⟨.none, ()⟩

abbrev trace : V2.D.Run (Fin 2) toy where
  honest := {0, 1}
  horizon := 2
  events := [.restart 0 1, .tick 0 1, .tick 1 1, .deliver 0 object 1]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

-- The cut after the ticks contains the restart and both ticks.
theorem reads_after_ticks : afterTicksIdx trace 1 = 3 := by decide
example : timeIdx trace 1 = 4 := by decide
example : afterTicks env trace 1 0 = 11 := by decide
example : afterTicks env trace 1 1 = 15 := by decide
example : preTick env trace 0 1 = some 0 := by decide
example : postClock env trace 0 1 = some 10 := by decide
example : postTick env trace 0 1 = some 11 := by decide
example : preTick env trace 0 2 = none := by decide
example : postClock env trace 0 2 = none := by decide
example : postTick env trace 0 2 = none := by decide
example : V2.D.Run.stateBefore env trace 99 0 = 111 := by decide
example : afterTicks env trace 99 0 = 111 := by decide

end AvailableChain.FGCompose.Tests

end
