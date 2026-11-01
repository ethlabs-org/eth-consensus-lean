module
public import AvailableChainFGSAClaims.Statements.Reads -- shake: keep (example-only read checks)

@[expose] public section

/-! The three reads differ on real v2 types (P3 §4.1.4). -/

namespace AvailableChain.FGSA.Run.Tests.Reads

/-- No duties: only the clock and delivery change the numeric state. -/
abbrev readSpec : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Empty
  Duty := Empty
  signLabel := fun d => nomatch d
  seats := fun _ => 0
  Payload := Unit
  Durable := Nat
  init := 0
  clock := fun st _ => st + 1
  actTime := fun ℓ => nomatch ℓ
  duties := fun _ => []
  duties_spec := fun ℓ => nomatch ℓ
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ ℓ => nomatch ℓ
  gossip := fun _ _ => []
  process := fun st _ => st + 10
  selfVisible := fun ℓ => nomatch ℓ
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

def readEnv : Generic.Env Unit :=
  ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩

def readRun : V2.D.Run Unit readSpec where
  honest := {()}
  horizon := 0
  events := [.tick () 0, .deliver () ⟨.none, ()⟩ 0]
  seatOf := fun ℓ => nomatch ℓ
  input := fun _ _ => ()

example : V2.D.Run.stateBeforeTime readEnv readRun 0 () = 0 := by decide +kernel
example : afterTicks readEnv readRun 0 () = 1 := by decide +kernel
example : V2.D.Run.readAt readEnv readRun 0 () = 11 := by decide +kernel

-- The cut excludes the delivery; the inclusive index includes it.
example : afterTicksIdx readRun 0 = 1 ∧ timeIdx readRun 0 = 2 := by decide +kernel
example : preTick readEnv readRun () 0 = some 0 := by decide +kernel
example : postClock readEnv readRun () 0 = some 1 := by decide +kernel
example : postTick readEnv readRun () 0 = some 1 := by decide +kernel
example : preTick readEnv readRun () 1 = none := by decide +kernel
example : postClock readEnv readRun () 1 = none := by decide +kernel
example : postTick readEnv readRun () 1 = none := by decide +kernel

end AvailableChain.FGSA.Run.Tests.Reads

end
