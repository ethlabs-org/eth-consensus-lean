module
public import AvailableChainEngineV2.Conditions.Duty.Lift -- shake: keep (axioms)

@[expose] public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.V2.D.Tests.Duties

/-- Two FG duties at times 0 and 1 use the same signing label and seat. -/
abbrev toy : ProtocolSpecD Unit where
  State := List Bool
  Label := Unit
  Duty := Bool
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Bool
  Durable := List Bool
  init := []
  clock := fun st _ => st
  actTime := fun d => if d then 1 else 0
  duties := fun t => if t = 0 then [false] else if t = 1 then [true] else []
  duties_spec := by
    intro d t
    cases d <;> split_ifs <;> simp_all [eq_comm]
  duties_nodup := by intro t; split_ifs <;> simp
  act := fun st d _ => if d ∈ st then none else some d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st o => o.payload :: st
  durable := id
  restore := fun d _ => d
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

abbrev env : Generic.Env (Fin 1) := ⟨1, by decide, 0, by decide, fun _ _ => true⟩

abbrev run : D.Run (Fin 1) toy where
  honest := {0}
  horizon := 1
  events := [.tick 0 0, .tick 0 1]
  seatOf := fun _ i => i
  input := fun _ _ => ()

theorem early_tick : D.tick env run [] 0 0 =
    ([false], [⟨.seat () 0, false⟩]) := by decide

theorem late_tick : D.tick env run [false] 0 1 =
    ([true, false], [⟨.seat () 0, true⟩]) := by decide

theorem both_run_emissions :
    D.Run.emitsAt env run 0 = [⟨.seat () 0, false⟩] ∧
    D.Run.emitsAt env run 1 = [⟨.seat () 0, true⟩] := by decide

theorem suppress_sent_content : (D.tick env run [true, false] 0 1).2 = [] := by decide

theorem sleep_releases_nothing :
    D.tick { env with awake := fun _ _ => false } run [false] 0 1 = ([false], []) := by
  decide

theorem due_labels_injective (t : Time) : D.DutiesInjectiveAt toy t := by
  intro d d' hd hd' _
  have ht := hd.trans hd'.symm
  cases d <;> cases d'
  · rfl
  · exact (show (0 : Time) ≠ 1 by decide) ht |>.elim
  · exact (show (0 : Time) ≠ 1 by decide) ht.symm |>.elim
  · rfl

/-- Simultaneous duties can sign two contents before the own record runs. -/
abbrev simultaneous : ProtocolSpecD Unit := { toy with
  actTime := fun _ => 0
  duties := fun t => if t = 0 then [false, true] else []
  duties_spec := by intro d t; cases d <;> split_ifs <;> simp_all [eq_comm]
  duties_nodup := by intro t; split_ifs <;> simp }

abbrev simultaneousRun : D.Run (Fin 1) simultaneous where
  honest := {0}
  horizon := 0
  events := [.tick 0 0]
  seatOf := fun _ i => i
  input := fun _ _ => ()

theorem simultaneous_two_contents :
    D.tick env simultaneousRun [] 0 0 =
      ([true, false], [⟨.seat () 0, false⟩, ⟨.seat () 0, true⟩]) := by decide

theorem simultaneous_not_injective : ¬ D.DutiesInjectiveAt simultaneous 0 := by
  intro h
  have hf := h false true rfl rfl rfl
  contradiction

end AvailableChain.V2.D.Tests.Duties

#print axioms AvailableChain.V2.D.Tests.Duties.early_tick
#print axioms AvailableChain.V2.D.Tests.Duties.late_tick
#print axioms AvailableChain.V2.D.Tests.Duties.both_run_emissions
#print axioms AvailableChain.V2.D.Tests.Duties.suppress_sent_content
#print axioms AvailableChain.V2.D.Tests.Duties.sleep_releases_nothing
#print axioms AvailableChain.V2.D.Tests.Duties.due_labels_injective
#print axioms AvailableChain.V2.D.Tests.Duties.simultaneous_two_contents
#print axioms AvailableChain.V2.D.Tests.Duties.simultaneous_not_injective
