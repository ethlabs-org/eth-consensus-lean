module
public import AvailableChainKitV2.DutyEmission
public import AvailableChainKitV2.DutyLinked
public import AvailableChainKitV2.DutyEngineClock
public import AvailableChainKitV2.DutyRecord
public import AvailableChainKitV2.EngineClock

@[expose] public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.V2.D.Engine.Tests.Duties

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

theorem exact_emission (st : toy.State) (v : Fin 1) (t : Time) (p : Bool) :
    (⟨.seat () 0, p⟩ : toy.Object) ∈ (D.tick env run st v t).2 ↔
      env.awake v t = true ∧ run.seatOf () 0 = v ∧
        ∃ d, toy.signLabel d = () ∧ toy.actTime d = t ∧
          toy.act (toy.clock st t) d (run.input v t) = some p :=
  mem_tick_seat_iff env run st v t () 0 p

theorem same_label_two_times :
    (⟨.seat () 0, false⟩ : toy.Object) ∈ (D.tick env run [] 0 0).2 ∧
    (⟨.seat () 0, true⟩ : toy.Object) ∈ (D.tick env run [false] 0 1).2 := by
  constructor
  · exact (mem_tick_seat_iff env run [] 0 0 () 0 false).mpr
      ⟨rfl, rfl, false, rfl, rfl, rfl⟩
  · exact (mem_tick_seat_iff env run [false] 0 1 () 0 true).mpr
      ⟨rfl, rfl, true, rfl, rfl, rfl⟩

theorem single_bijection : D.Linked (fun ℓ => ℓ = ()) run :=
  (linked_singleton_iff run ()).mpr ⟨Equiv.refl (Fin 1), fun _ => rfl⟩

theorem exact_bijective_seat (st : toy.State) (v : Fin 1) (t : Time) (p : Bool) :
    (⟨.seat () 0, p⟩ : toy.Object) ∈ (D.tick env run st v t).2 ↔
      0 = v ∧ env.awake v t = true ∧
        ∃ d, toy.signLabel d = () ∧ toy.actTime d = t ∧
          toy.act (toy.clock st t) d (run.input v t) = some p :=
  emits_bijSeat env run (Equiv.refl (Fin 1)) (fun _ => rfl) st v t 0 p

end AvailableChain.V2.D.Engine.Tests.Duties

#print axioms AvailableChain.V2.D.Engine.Tests.Duties.exact_emission
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.same_label_two_times
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.single_bijection
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.exact_bijective_seat

namespace AvailableChain.V2.D.Engine.Tests.Duties.Lift

variable {In V : Type} [DecidableEq V] {P : ProtocolSpec In}

/-- The clock laws keep the same fields under the identity lift. -/
abbrev clockLift (C : V2.Engine.ClockLaws P) : D.Engine.ClockLaws P.toD :=
  ⟨C.now, C.init, C.clock, C.process, C.recordOwn_now⟩

theorem clockLaws_agrees :
    Nonempty (D.Engine.ClockLaws P.toD) ↔ Nonempty (V2.Engine.ClockLaws P) :=
  ⟨fun ⟨C⟩ => ⟨⟨C.now, C.init, C.clock, C.process, C.recordOwn_now⟩⟩,
    fun ⟨C⟩ => ⟨clockLift C⟩⟩

/-- Compare complete law statements, including all remaining premises. -/
def statementOf {p : Prop} (_ : p) : Prop := p

variable (E : Generic.Env V) (rho : V2.Run V P)

theorem ownReleasedAt_agrees (v : V) (k : Nat) :
    D.Engine.ownReleasedAt E rho.toD v k = V2.Engine.ownReleasedAt E rho v k := by
  simp only [D.Engine.ownReleasedAt_def, V2.Engine.ownReleasedAt,
    D.emitsAt_toD, D.objSelfVisible_toD]

theorem ownReleased_agrees (v : V) (i j : Nat) :
    D.Engine.ownReleased E rho.toD v i j = V2.Engine.ownReleased E rho v i j := by
  rw [D.Engine.ownReleased_def]
  unfold V2.Engine.ownReleased
  congr 1
  funext k
  exact ownReleasedAt_agrees E rho v k

variable (C : V2.Engine.ClockLaws P)

theorem now_foldl_recordOwn_agrees :
    statementOf (D.Engine.ClockLaws.now_foldl_recordOwn (P := P.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.ClockLaws.now_foldl_recordOwn (P := P) (C := C)) := by
  simp only [statementOf]

theorem now_tick_agrees :
    statementOf (D.Engine.ClockLaws.now_tick (P := P.toD) (V := V) (E := E) (rho := rho.toD) (C :=
      clockLift C)) ↔
      statementOf (V2.Engine.ClockLaws.now_tick (P := P) (V := V) (E := E) (rho := rho) (C := C))
        := by
  simp only [statementOf, D.tick_toD]

omit [DecidableEq V] in
theorem eventIndex_lt_of_time_lt_agrees {i j : Nat} {e f : Event V P.Object} :
    statementOf (D.Engine.eventIndex_lt_of_time_lt (P := P.toD) (i := i) (j := j) (e := e) (f :=
      f) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.eventIndex_lt_of_time_lt (P := P) (i := i) (j := j) (e := e) (f := f)
        (E := E) (rho := rho)) := by
  simp only [statementOf, D.scheduleWellFormed_toD_iff]

omit [DecidableEq V] in
theorem time_le_of_key_le_agrees :
    statementOf (D.Engine.time_le_of_key_le (P := P.toD) (V := V)) ↔
      statementOf (V2.Engine.time_le_of_key_le (P := P) (V := V)) := by
  simp only [statementOf]

omit [DecidableEq V] in
theorem filter_eq_take_agrees :
    statementOf (D.Engine.filter_eq_take (P := P.toD) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.filter_eq_take (P := P) (E := E) (rho := rho)) := by
  simp only [statementOf, D.scheduleWellFormed_toD_iff]

omit [DecidableEq V] in
theorem filter_false_of_index_ge_agrees {j : Nat} {e : Event V P.Object} :
    statementOf (D.Engine.filter_false_of_index_ge (P := P.toD) (j := j) (e := e) (E := E) (rho :=
      rho.toD)) ↔
      statementOf (V2.Engine.filter_false_of_index_ge (P := P) (j := j) (e := e) (E := E) (rho :=
        rho)) := by
  simp only [statementOf, D.scheduleWellFormed_toD_iff]

omit [DecidableEq V] in
theorem index_lt_read_length_iff_agrees {i : Nat} {e : Event V P.Object} :
    statementOf (D.Engine.index_lt_read_length_iff (P := P.toD) (i := i) (e := e) (E := E) (rho :=
      rho.toD)) ↔
      statementOf (V2.Engine.index_lt_read_length_iff (P := P) (i := i) (e := e) (E := E) (rho :=
        rho)) := by
  simp only [statementOf, D.scheduleWellFormed_toD_iff]

omit [DecidableEq V] in
theorem read_length_mono_agrees :
    statementOf (D.Engine.read_length_mono (P := P.toD) (rho := rho.toD)) ↔
      statementOf (V2.Engine.read_length_mono (P := P) (rho := rho)) := by
  simp only [statementOf]

omit [DecidableEq V] in
theorem tick_index_lt_delivery_agrees {i j : Nat} {v w : V} {o : P.Object} {a t : Time} :
    statementOf (D.Engine.tick_index_lt_delivery (P := P.toD) (i := i) (j := j) (v := v) (w := w)
      (o := o) (a := a) (t := t) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.tick_index_lt_delivery (P := P) (i := i) (j := j) (v := v) (w := w)
        (o := o) (a := a) (t := t) (E := E) (rho := rho)) := by
  simp only [statementOf, D.scheduleWellFormed_toD_iff]

theorem readAt_eq_stateBefore_agrees :
    statementOf (D.Engine.readAt_eq_stateBefore (P := P.toD) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.readAt_eq_stateBefore (P := P) (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD, D.readAt_toD, D.scheduleWellFormed_toD_iff]

theorem stateBefore_other_node_agrees {v : V} {a b : Nat} :
    statementOf (D.Engine.stateBefore_other_node (P := P.toD) (v := v) (a := a) (b := b) (E := E)
      (rho := rho.toD)) ↔
      statementOf (V2.Engine.stateBefore_other_node (P := P) (v := v) (a := a) (b := b) (E := E)
        (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD]

theorem stateBefore_tick_eq_stateBeforeTime_agrees {i : Nat} {v : V} {t : Time} :
    statementOf (D.Engine.stateBefore_tick_eq_stateBeforeTime (P := P.toD) (i := i) (v := v) (t :=
      t) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.stateBefore_tick_eq_stateBeforeTime (P := P) (i := i) (v := v) (t :=
        t) (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD, D.stateBeforeTime_toD, D.scheduleWellFormed_toD_iff,
    D.noRestart_toD_iff]

theorem foldl_recordOwn_preserve_agrees :
    statementOf (D.Engine.foldl_recordOwn_preserve (P := P.toD)) ↔
      statementOf (V2.Engine.foldl_recordOwn_preserve (P := P)) := by
  simp only [statementOf]

theorem tick_preserve_agrees {st : P.State} {v : V} {t : Time} :
    statementOf (D.Engine.tick_preserve (P := P.toD) (st := st) (v := v) (t := t) (E := E) (rho :=
      rho.toD)) ↔
      statementOf (V2.Engine.tick_preserve (P := P) (st := st) (v := v) (t := t) (E := E) (rho :=
        rho)) := by
  simp only [statementOf, D.tick_toD]

theorem stateBefore_step_induction_agrees {i j : Nat} :
    statementOf (D.Engine.stateBefore_step_induction (P := P.toD) (i := i) (j := j) (E := E) (rho
      := rho.toD)) ↔
      statementOf (V2.Engine.stateBefore_step_induction (P := P) (i := i) (j := j) (E := E) (rho
        := rho)) := by
  simp only [statementOf, D.world_step_toD, D.stateBefore_toD]

theorem stateBefore_stable_agrees {i j : Nat} :
    statementOf (D.Engine.stateBefore_stable (P := P.toD) (i := i) (j := j) (E := E) (rho :=
      rho.toD)) ↔
      statementOf (V2.Engine.stateBefore_stable (P := P) (i := i) (j := j) (E := E) (rho := rho))
        := by
  simp only [statementOf, D.stateBefore_toD, D.restartFree_toD_iff]

theorem stateBefore_now_source_agrees :
    statementOf (D.Engine.stateBefore_now_source (P := P.toD) (E := E) (rho := rho.toD) (C :=
      clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_now_source (P := P) (E := E) (rho := rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD]

theorem stateBefore_now_source_noRestart_agrees :
    statementOf (D.Engine.stateBefore_now_source_noRestart (P := P.toD) (E := E) (rho := rho.toD)
      (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_now_source_noRestart (P := P) (E := E) (rho := rho) (C :=
        C)) := by
  simp only [statementOf, D.stateBefore_toD, D.noRestart_toD_iff]

theorem stateBefore_now_le_event_agrees {i : Nat} {e : Event V P.Object} :
    statementOf (D.Engine.stateBefore_now_le_event (P := P.toD) (i := i) (e := e) (E := E) (rho :=
      rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_now_le_event (P := P) (i := i) (e := e) (E := E) (rho :=
        rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff]

theorem stateBefore_now_le_event_noRestart_agrees {i : Nat} {e : Event V P.Object} :
    statementOf (D.Engine.stateBefore_now_le_event_noRestart (P := P.toD) (i := i) (e := e) (E :=
      E) (rho := rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_now_le_event_noRestart (P := P) (i := i) (e := e) (E :=
        E) (rho := rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff, D.noRestart_toD_iff]

theorem stateBefore_now_mono_agrees {i j : Nat} :
    statementOf (D.Engine.stateBefore_now_mono (P := P.toD) (i := i) (j := j) (E := E) (rho :=
      rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_now_mono (P := P) (i := i) (j := j) (E := E) (rho := rho)
        (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff, D.restartFree_toD_iff]

theorem stateBefore_now_mono_noRestart_agrees {i j : Nat} :
    statementOf (D.Engine.stateBefore_now_mono_noRestart (P := P.toD) (i := i) (j := j) (E := E)
      (rho := rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_now_mono_noRestart (P := P) (i := i) (j := j) (E := E)
        (rho := rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff, D.noRestart_toD_iff]

theorem delivery_now_ge_public_agrees {i : Nat} {v : V} {o : P.Object} {a t : Time} :
    statementOf (D.Engine.delivery_now_ge_public (P := P.toD) (i := i) (v := v) (o := o) (a := a)
      (t := t) (E := E) (rho := rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.delivery_now_ge_public (P := P) (i := i) (v := v) (o := o) (a := a)
        (t := t) (E := E) (rho := rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff, D.noRestart_toD_iff]

theorem stateBefore_invariant_agrees :
    statementOf (D.Engine.stateBefore_invariant (P := P.toD) (E := E) (rho := rho.toD) (C :=
      clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_invariant (P := P) (E := E) (rho := rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff]

theorem stateBefore_invariant_noRestart_agrees :
    statementOf (D.Engine.stateBefore_invariant_noRestart (P := P.toD) (E := E) (rho := rho.toD)
      (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_invariant_noRestart (P := P) (E := E) (rho := rho) (C :=
        C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff, D.noRestart_toD_iff]

theorem stateBefore_stable_clock_agrees {i j : Nat} :
    statementOf (D.Engine.stateBefore_stable_clock (P := P.toD) (i := i) (j := j) (E := E) (rho :=
      rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_stable_clock (P := P) (i := i) (j := j) (E := E) (rho :=
        rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff, D.restartFree_toD_iff]

theorem stateBefore_stable_clock_restore_agrees {i j : Nat} :
    statementOf (D.Engine.stateBefore_stable_clock_restore (P := P.toD) (i := i) (j := j) (E := E)
      (rho := rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_stable_clock_restore (P := P) (i := i) (j := j) (E := E)
        (rho := rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff]

theorem stateBefore_stable_clock_noRestart_agrees {i j : Nat} :
    statementOf (D.Engine.stateBefore_stable_clock_noRestart (P := P.toD) (i := i) (j := j) (E :=
      E) (rho := rho.toD) (C := clockLift C)) ↔
      statementOf (V2.Engine.stateBefore_stable_clock_noRestart (P := P) (i := i) (j := j) (E :=
        E) (rho := rho) (C := C)) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff, D.noRestart_toD_iff]

theorem clock_field_origin_agrees {α : Type} :
    statementOf (D.Engine.clock_field_origin (P := P.toD) (α := α) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.clock_field_origin (P := P) (α := α) (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD]

theorem clock_field_origin_noRestart_agrees {α : Type} :
    statementOf (D.Engine.clock_field_origin_noRestart (P := P.toD) (α := α) (E := E) (rho :=
      rho.toD)) ↔
      statementOf (V2.Engine.clock_field_origin_noRestart (P := P) (α := α) (E := E) (rho := rho))
        := by
  simp only [statementOf, D.stateBefore_toD, D.noRestart_toD_iff]

theorem clock_field_origin_of_subset_agrees {α : Type} :
    statementOf (D.Engine.clock_field_origin_of_subset (P := P.toD) (α := α) (E := E) (rho :=
      rho.toD)) ↔
      statementOf (V2.Engine.clock_field_origin_of_subset (P := P) (α := α) (E := E) (rho := rho))
        := by
  simp only [statementOf, D.stateBefore_toD]

theorem stateBefore_field_prefix_agrees {α : Type} {i j : Nat} :
    statementOf (D.Engine.stateBefore_field_prefix (P := P.toD) (α := α) (i := i) (j := j) (E :=
      E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.stateBefore_field_prefix (P := P) (α := α) (i := i) (j := j) (E := E)
        (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD, D.restartFree_toD_iff]

theorem stateBefore_field_prefix_restore_agrees {α : Type} {i j : Nat} :
    statementOf (D.Engine.stateBefore_field_prefix_restore (P := P.toD) (α := α) (i := i) (j := j)
      (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.stateBefore_field_prefix_restore (P := P) (α := α) (i := i) (j := j)
        (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD]

theorem ownReleased_self_agrees :
    statementOf (D.Engine.ownReleased_self (P := P.toD) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.ownReleased_self (P := P) (E := E) (rho := rho)) := by
  simp only [statementOf, ownReleased_agrees]

theorem ownReleased_succ_agrees {i j : Nat} :
    statementOf (D.Engine.ownReleased_succ (P := P.toD) (i := i) (j := j) (E := E) (rho :=
      rho.toD)) ↔
      statementOf (V2.Engine.ownReleased_succ (P := P) (i := i) (j := j) (E := E) (rho := rho)) :=
        by
  simp only [statementOf, ownReleased_agrees, ownReleasedAt_agrees]

theorem ownRecord_fold_interval_agrees {β : Type} {i j : Nat} :
    statementOf (D.Engine.ownRecord_fold_interval (P := P.toD) (β := β) (i := i) (j := j) (E := E)
      (rho := rho.toD)) ↔
      statementOf (V2.Engine.ownRecord_fold_interval (P := P) (β := β) (i := i) (j := j) (E := E)
        (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD, D.restartFree_toD_iff, ownReleased_agrees]

theorem ownRecord_fold_agrees {β : Type} :
    statementOf (D.Engine.ownRecord_fold (P := P.toD) (β := β) (E := E) (rho := rho.toD)) ↔
      statementOf (V2.Engine.ownRecord_fold (P := P) (β := β) (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD, D.noRestart_toD_iff, ownReleased_agrees]

theorem recordOwn_preserve_of_base_agrees {F : V2.LabelFamilies P}
    (iso : V2.Isolation P F) :
    statementOf (D.Engine.recordOwn_preserve_of_base iso.toD) ↔
      statementOf (V2.Engine.recordOwn_preserve_of_base iso) := Iff.rfl

/-- The restart law has the same record equation on the old run. -/
theorem ownRecord_fold_interval_restart_agrees {β : Type}
    (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    {i j : Nat} (hij : i ≤ j) (v : V) :
    statementOf (D.Engine.ownRecord_fold_interval_restart (P := P.toD)
      proj g hclock hprocess hrecord E rho.toD hij v) ↔
      ((∀ k t, i ≤ k → k < j → rho.events[k]? = some (.restart v t) →
        proj (P.restore (P.durable (V2.Run.stateBefore E rho k v)) t) =
          proj (V2.Run.stateBefore E rho k v)) →
      proj (V2.Run.stateBefore E rho j v) =
        (V2.Engine.ownReleased E rho v i j).foldl g
          (proj (V2.Run.stateBefore E rho i v))) := by
  simp only [statementOf, D.stateBefore_toD, ownReleased_agrees]

theorem ownRecord_fold_restore_agrees {β : Type}
    (proj : P.State → β) (g : β → P.Object → β)
    (hclock : ∀ st t, proj (P.clock st t) = proj st)
    (hprocess : ∀ st o, proj (P.process st o) = proj st)
    (hrecord : ∀ st o, proj (P.recordOwn st o) = g (proj st) o)
    (hrestore : ∀ st t, proj (P.restore (P.durable st) t) = proj st)
    (i : Nat) (v : V) :
    statementOf (D.Engine.ownRecord_fold_restore (P := P.toD)
      proj g hclock hprocess hrecord hrestore E rho.toD i v) ↔
      proj (V2.Run.stateBefore E rho i v) =
        (V2.Engine.ownReleased E rho v 0 i).foldl g (proj P.init) := by
  simp only [statementOf, D.stateBefore_toD, ownReleased_agrees]

end AvailableChain.V2.D.Engine.Tests.Duties.Lift

namespace AvailableChain.V2.D.Engine.Tests.Duties

/-- Four duties share one signing seat. The last three request the same content. -/
abbrev durableToy : ProtocolSpecD Unit := { toy with
  Duty := Fin 4
  signLabel := fun _ => ()
  actTime := fun d => (d.val : Time)
  duties := fun t => (List.finRange 4).filter (fun d => decide ((d.val : Time) = t))
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; exact (List.nodup_finRange 4).filter _
  act := fun st d _ =>
    let p := decide (d.val ≠ 0)
    if p ∈ st then none else some p }

abbrev sleepEnv : Generic.Env (Fin 1) := { env with
  awake := fun _ t => decide (t ≠ 1) }

abbrev restartRun : D.Run (Fin 1) durableToy where
  honest := {0}
  horizon := 3
  events := [.tick 0 0, .restart 0 1, .tick 0 1, .tick 0 2, .restart 0 3, .tick 0 3]
  seatOf := fun _ i => i
  input := fun _ _ => ()

theorem restartRun_schedule : D.ScheduleWellFormed sleepEnv restartRun where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by simp [Event.time]
  honest_only := by simp [Event.node]
  tick_public := by
    intro v t h
    simp only [List.mem_cons, List.not_mem_nil, or_false,
      Event.tick.injEq, reduceCtorEq, false_or] at h
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  tick_total := by
    intro v _ t _ h0 h3 _
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by
      change t ≤ 3 at h3
      dsimp only [Time] at *
      omega
    rcases ht with rfl | rfl | rfl | rfl <;> simp

theorem durable_duties_injective (t : Time) : D.DutiesInjectiveAt durableToy t := by
  intro d d' hd hd' _
  apply Fin.ext
  have h : (d.val : Time) = d'.val := hd.trans hd'.symm
  exact Int.ofNat_inj.mp h

/-- The specified-duty iff applies even though all duties share a label. -/
theorem exact_durable_duty (st : durableToy.State) (d : Fin 4) (p : Bool) :
    (⟨.seat () 0, p⟩ : durableToy.Object) ∈
        (D.tick sleepEnv restartRun st 0 d.val).2 ↔
      sleepEnv.awake 0 d.val = true ∧ restartRun.seatOf () 0 = 0 ∧
        durableToy.act (durableToy.clock st d.val) d () = some p :=
  mem_tick_duty_iff sleepEnv restartRun st 0 d.val d rfl
    (durable_duties_injective _) 0 p

/-- Sleep and each restart keep the durable record. -/
theorem record_survives_sleep_restart :
    D.Run.stateBefore sleepEnv restartRun 1 0 = [false] ∧
    D.Run.stateBefore sleepEnv restartRun 2 0 = [false] ∧
    D.Run.stateBefore sleepEnv restartRun 3 0 = [false] ∧
    D.Run.stateBefore sleepEnv restartRun 4 0 = [true, false] ∧
    D.Run.stateBefore sleepEnv restartRun 5 0 = [true, false] ∧
    D.Run.stateBefore sleepEnv restartRun 6 0 = [true, false] := by decide

/-- Sleep omits a due emission; a later duty can emit it. A restart then
keeps the record that suppresses the same content. -/
theorem releases_across_sleep_restart :
    D.Run.emitsAt sleepEnv restartRun 0 = [⟨.seat () 0, false⟩] ∧
    D.Run.emitsAt sleepEnv restartRun 2 = [] ∧
    D.Run.emitsAt sleepEnv restartRun 3 = [⟨.seat () 0, true⟩] ∧
    D.Run.emitsAt sleepEnv restartRun 5 = [] := by decide

theorem restart_record_fold (i : Nat) :
    D.Run.stateBefore sleepEnv restartRun i 0 =
      (ownReleased sleepEnv restartRun 0 0 i).foldl
        (fun st o => o.payload :: st) [] :=
  ownRecord_fold_restore (P := durableToy) id (fun st o => o.payload :: st)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    sleepEnv restartRun i 0

end AvailableChain.V2.D.Engine.Tests.Duties

-- Kernel dependencies of the lift and trace tests.
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.clockLaws_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownReleasedAt_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownReleased_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.now_foldl_recordOwn_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.now_tick_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.eventIndex_lt_of_time_lt_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.time_le_of_key_le_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.filter_eq_take_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.filter_false_of_index_ge_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.index_lt_read_length_iff_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.read_length_mono_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.tick_index_lt_delivery_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.readAt_eq_stateBefore_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_other_node_agrees
#print axioms
  AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_tick_eq_stateBeforeTime_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.foldl_recordOwn_preserve_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.tick_preserve_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_step_induction_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_stable_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_now_source_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_now_source_noRestart_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_now_le_event_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_now_le_event_noRestart_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_now_mono_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_now_mono_noRestart_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.delivery_now_ge_public_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_invariant_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_invariant_noRestart_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_stable_clock_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_stable_clock_restore_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_stable_clock_noRestart_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.clock_field_origin_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.clock_field_origin_noRestart_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.clock_field_origin_of_subset_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_field_prefix_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.stateBefore_field_prefix_restore_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownReleased_self_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownReleased_succ_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownRecord_fold_interval_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownRecord_fold_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.recordOwn_preserve_of_base_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownRecord_fold_interval_restart_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.Lift.ownRecord_fold_restore_agrees
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.restartRun_schedule
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.durable_duties_injective
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.exact_durable_duty
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.record_survives_sleep_restart
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.releases_across_sleep_restart
#print axioms AvailableChain.V2.D.Engine.Tests.Duties.restart_record_fold
