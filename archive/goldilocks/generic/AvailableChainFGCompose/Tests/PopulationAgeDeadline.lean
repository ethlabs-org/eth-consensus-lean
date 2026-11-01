module
public import AvailableChainFGCompose.Statements.Channels -- shake: keep (Compose test scope)

set_option linter.privateModule false

public section
noncomputable section

/-! Ordinary receipt-cut control. The only changed datum is delivery time.
This tests the strict receipt reader, not an ExecutionValid producer. -/
namespace AvailableChain.FGCompose.Tests.PopulationAgeDeadline
open AvailableChain.SimplexFG

private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Bool
  Label := Time
  Duty := Time
  signLabel := id
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := Bool
  init := false
  clock := fun st _ => st
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun _ _ _ => none
  gossip := fun _ _ => []
  process := fun _ _ => true
  selfVisible := fun _ => true
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False
private abbrev wire : protocol.Object := ⟨.seat 6 0, row⟩
private abbrev env : Generic.Env Nat := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev run (t : Time) : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 38
  events := [.deliver 7 wire t]
  seatOf := fun _ _ => 9
  input := fun _ _ => ()

private theorem receipt_premises_sat (t : Time) (ht : t ∈ ({20, 21} : Finset Time)) :
    (run t).honest = {7, 9} ∧ (run t).horizon = 38 ∧
    (run t).events = [.deliver 7 wire t] ∧
    V2.D.Run.holder (run t) wire.auth = some 9 ∧
    V2.D.Run.stateBefore env (run t) 0 7 = false ∧
    V2.D.Run.stateBefore env (run t) 1 7 = true ∧
    t ≤ (run t).horizon := by
  have ht' : t = 20 ∨ t = 21 := by simpa using ht
  rcases ht' with rfl | rfl <;> decide +kernel

#print axioms receipt_premises_sat

/-- A receipt exactly at the deadline is excluded solely by the strict time cut. -/
private theorem receipt_deadline_strict :
    Gen.V2.Duty.HoldsBefore env (run 20) (fun st => st = true) 21 7 ∧
    ¬ Gen.V2.Duty.HoldsBefore env (run 21) (fun st => st = true) 21 7 ∧
    Gen.V2.Duty.HoldsBefore env (run 21) (fun st => st = true) 22 7 := by
  unfold Gen.V2.Duty.HoldsBefore
  decide +kernel

#print axioms receipt_deadline_strict
end AvailableChain.FGCompose.Tests.PopulationAgeDeadline
end
