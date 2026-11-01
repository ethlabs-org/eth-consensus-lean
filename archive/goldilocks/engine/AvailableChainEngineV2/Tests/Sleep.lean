module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import AvailableChainEngineV2.TestSupport.Sleep
public import AvailableChainEngineV2.Conditions.Duty.Lift -- shake: keep (examples)

@[expose] public section

namespace AvailableChain.V2.Tests.Sleep

open AvailableChain

def second : toy.Object := ⟨.none, 2⟩

/-- Both nodes sleep before zero. Node 0 also sleeps on [2,5) and [7,10). -/
def env : Generic.Env (Fin 2) :=
  ⟨4, by decide, 5, by decide,
    fun v t => decide (0 ≤ t ∧ (v = 1 ∨ t < 2 ∨ (5 ≤ t ∧ t < 7) ∨ 10 ≤ t))⟩

/-- The sender emits before sleep and during sleep. Both receipts follow the wake. -/
def run : Run (Fin 2) toy where
  honest := Finset.univ
  horizon := 10
  events := [.tick 0 0, .tick 1 0, .tick 1 4, .restart 0 5,
    .deliver 0 first 5, .deliver 0 second 5, .tick 1 8, .restart 0 10]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

-- Test 1: each local event at an asleep time contradicts its sleep field.
example : ¬ SleepWellFormed env { run with events := [.tick 0 3] } := by
  intro h
  have := h.tick_awake 0 3 (by simp)
  contradiction

example : ¬ SleepWellFormed env { run with events := [.deliver 0 first 3] } := by
  intro h
  have := h.deliver_awake 0 first 3 (by simp)
  contradiction

example : ¬ SleepWellFormed env { run with events := [.restart 0 3] } := by
  intro h
  have := h.restart_awake 0 3 (by simp)
  contradiction

example : ¬ D.SleepWellFormed env { run.toD with events := [.tick 0 3] } := by
  intro h
  have := h.tick_awake 0 3 (by simp)
  contradiction

example : ¬ D.SleepWellFormed env { run.toD with events := [.deliver 0 first 3] } := by
  intro h
  have := h.deliver_awake 0 first 3 (by simp)
  contradiction

example : ¬ D.SleepWellFormed env { run.toD with events := [.restart 0 3] } := by
  intro h
  have := h.restart_awake 0 3 (by simp)
  contradiction

private theorem engine_sleep_valid : SleepWellFormed env run := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.tick.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro v o t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.deliver.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
  · intro v t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.restart.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro v _ t h0 hh hw
    fin_cases v <;> simp [Wakes, env] at hw
    · have ht : t = 5 ∨ t = 10 := by dsimp [Time] at *; omega
      rcases ht with rfl | rfl <;> simp [run]
    · dsimp [Time] at *; omega

private theorem engine_run_valid : ExecutionValid env run := by
  refine { toSleepWellFormed := engine_sleep_valid, toScheduleWellFormed := ?_,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e _; exact Finset.mem_univ _
    · intro v t h
      simp only [run, List.mem_cons, List.not_mem_nil, or_false,
        Event.tick.injEq, reduceCtorEq, or_false, false_or] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · intro v _ t ⟨k, hk⟩ h0 hh ha
      have ht : t = 0 ∨ t = 4 ∨ t = 8 := by
        simp [env] at hk
        simp [run] at hh
        dsimp [Time] at *
        omega
      fin_cases v <;> rcases ht with rfl | rfl | rfl <;>
        first | contradiction | decide
  · refine ⟨by intros; rfl, by intros; rfl, ?_⟩
    intro i v o t hi
    have he := List.mem_of_getElem? hi
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      Event.deliver.injEq, reduceCtorEq, or_false, false_or] at he
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have : i = 4 := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp [run] at this
        interval_cases i <;> simp_all [run, first, second]
      subst i; decide
    · have : i = 5 := by
        have := (List.getElem?_eq_some_iff.mp hi).1
        simp [run] at this
        interval_cases i <;> simp_all [run, first, second]
      subst i; decide
  · refine ⟨?_, ?_⟩
    · rintro v o t ⟨i, hi⟩ u _ hu
      have he := List.mem_of_getElem? hi
      simp only [run, List.mem_cons, List.not_mem_nil, or_false,
        Event.deliver.injEq, reduceCtorEq, or_false, false_or] at he
      rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [Run.holder, first, second] at hu
    · intro v o t _ o' hc; exact hc.elim

-- Tests 2 and 9: a valid run freezes the sleeping node, in both twins.
example : ExecutionValid env run ∧
    Run.stateBefore env run 2 0 = Run.stateBefore env run 3 0 := ⟨engine_run_valid, by decide⟩

example : D.ExecutionValid env run.toD ∧
    D.Run.stateBefore env run.toD 2 0 = D.Run.stateBefore env run.toD 3 0 := by
  exact ⟨(D.executionValid_toD_iff env run).mpr engine_run_valid, by decide⟩

example : D.ExecutionValid env run.toD ↔ ExecutionValid env run :=
  D.executionValid_toD_iff env run

-- The invalid local tick changes the sleeping node's clock.
private def asleepTick : Run (Fin 2) toy :=
  { run with events := run.events.set 2 (.tick 0 4) }

example : (Run.stateBefore env asleepTick 2 0).1 = 0 ∧
    (Run.stateBefore env asleepTick 3 0).1 = 4 ∧ ¬ SleepWellFormed env asleepTick := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have := h.tick_awake 0 4 (by decide)
  contradiction

example : (D.Run.stateBefore env asleepTick.toD 2 0).1 = 0 ∧
    (D.Run.stateBefore env asleepTick.toD 3 0).1 = 4 ∧
    ¬ D.SleepWellFormed env asleepTick.toD := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  have := h.tick_awake 0 4 (by decide)
  contradiction

-- Test 3: a missing restart at a positive wake, including the horizon, is invalid.
example : ¬ SleepWellFormed env { run with events := [] } := by
  intro h
  exact (by simp : Event.restart 0 5 ∉ ([] : List (Event (Fin 2) toy.Object)))
    (h.wake_restart 0 (by simp [run]) 5 (by decide) (by decide) (by unfold Wakes; decide))

example : ¬ SleepWellFormed env { run with events := [.restart 0 5] } := by
  intro h
  have := h.wake_restart 0 (by simp [run]) 10 (by decide) (by decide) (by unfold Wakes; decide)
  simp at this

example : ¬ D.SleepWellFormed env { run.toD with events := [] } := by
  intro h
  have := h.wake_restart 0 (by simp [run]) 5
    (by decide) (by decide) (by unfold D.Wakes; decide)
  simp at this

example : ¬ D.SleepWellFormed env { run.toD with events := [.restart 0 5] } := by
  intro h
  have := h.wake_restart 0 (by simp [run]) 10
    (by decide) (by decide) (by unfold D.Wakes; decide)
  simp at this

-- Test 4: zero is a wake, but the valid run has no restart there.
example : Wakes env 0 0 ∧ Event.restart 0 0 ∉ run.events ∧
    ExecutionValid env run := ⟨by unfold Wakes; decide, by decide, engine_run_valid⟩

example : D.Wakes env 0 0 ∧ Event.restart 0 0 ∉ run.toD.events ∧
    D.ExecutionValid env run.toD :=
  ⟨by unfold D.Wakes; decide, by decide, (D.executionValid_toD_iff env run).mpr engine_run_valid⟩

-- Test 5: same-time phases and the action cut include only the restart.
private def sameTime : Run (Fin 2) toy :=
  { run with events := [.restart 0 5, .tick 0 5, .deliver 0 first 5] }

example : sameTime.events.Pairwise (fun e f => e.key ≤ f.key) ∧
    Run.actionCut sameTime 5 = 1 ∧ D.Run.actionCut sameTime.toD 5 = 1 := by decide

-- Test 6: 5 is not a public tick time; both restore clocks still read exactly 5.
example : ¬ PublicTime env 5 := by rintro ⟨k, hk⟩; simp [env] at hk; dsimp [Time] at *; omega

example : (Run.stateAfterRestartsAt env run 5 0).1 = 5 ∧
    (D.Run.stateAfterRestartsAt env run.toD 5 0).1 = 5 := by decide

-- Test 7: these are real emissions before sleep and during sleep.
example : Run.emits env run 1 first 0 := ⟨1, rfl, by decide⟩
example : Run.emits env run 1 second 4 := ⟨2, rfl, by decide⟩

private theorem sleep_demand (o : toy.Object) (ho : o = first ∨ o = second) (send : Time) :
    DeliveryDemand env run 1 0 o send (fun a => max a 5 + 2) 10 := by
  intro a _ _ hlt _ hh hr _
  have ha : a = 5 := by
    have hs := hr a le_rfl hlt
    have h2 := hr 2
    have h7 := hr 7
    simp only [LinkReadyOn, AwakeOn] at hr
    simp [env] at hs h2 h7
    simp only [run] at hh
    dsimp [Time] at *
    omega
  subst a
  apply Or.inr
  rcases ho with rfl | rfl
  · exact ⟨5, by decide, by decide, 4, first, rfl, rfl⟩
  · exact ⟨5, by decide, by decide, 5, second, rfl, rfl⟩

example : DeliveryDemand env run 1 0 first 0 (fun a => max a 5 + 2) 10 :=
  sleep_demand first (Or.inl rfl) 0

example : DeliveryDemand env run 1 0 second 4 (fun a => max a 5 + 2) 10 :=
  sleep_demand second (Or.inr rfl) 4

example : D.DeliveryDemand env run.toD 1 0 first 0 (fun a => max a 5 + 2) 10 :=
  (D.deliveryDemand_toD_iff env run 1 0 first 0 _ 10).mpr (sleep_demand first (Or.inl rfl) 0)

example : D.DeliveryDemand env run.toD 1 0 second 4 (fun a => max a 5 + 2) 10 :=
  (D.deliveryDemand_toD_iff env run 1 0 second 4 _ 10).mpr (sleep_demand second (Or.inr rfl) 4)

-- Anchor 5 meets every demand guard, for both send times and both objects.
example (o : toy.Object) (send : Time) (hs : send = 0 ∨ send = 4) :
    send ≤ 5 ∧ (0 : Time) ≤ 5 ∧ (5 : Time) < max 5 5 + 2 ∧
    (max 5 5 + 2 : Time) ≤ 10 ∧ (max 5 5 + 2 : Time) ≤ run.horizon ∧
    LinkReadyOn env run 1 0 5 (max 5 5 + 2) ∧
    toy.excludes (Run.stateBeforeTime env run (max 5 5 + 2) 0) o = false := by
  refine ⟨by rcases hs with rfl | rfl <;> decide, by decide, by decide,
    by decide, by decide, ?_, rfl⟩
  intro t h5 h7
  simp [env]
  dsimp [Time] at *; omega

-- With the main fixture's Δ = 4, PartialSynchrony has no ready window for node 0:
-- [5,9) includes sleep at 7. The separate fixture below tests full delivery records.
example : ¬ LinkReadyOn env run 1 0 5 (max 5 env.t_GST + env.Δ) := by
  intro h
  have := h 7 (by decide) (by decide)
  contradiction

-- The second sleep cancels the anchor at 6 (deadline 8).
example : ¬ LinkReadyOn env run 1 0 6 8 := by
  intro h
  have := h 7 (by decide) (by decide)
  contradiction

example : ¬ D.LinkReadyOn env run.toD 1 0 6 8 := by
  intro h
  have := h 7 (by decide) (by decide)
  contradiction

-- Test 8: a pre-restart receipt meets service even when the restart erases it.
example : toy.processed (Run.stateAfterRestartsAt env run 10 0) first = false ∧
    DeliveryService env run 0 first 10 12 := by
  refine ⟨by decide, Or.inl ⟨5, by decide, by decide⟩⟩

example : toy.toD.processed (D.Run.stateAfterRestartsAt env run.toD 10 0) first = false ∧
    D.DeliveryService env run.toD 0 first 10 12 := by
  refine ⟨by decide, Or.inl ⟨5, by decide, by decide⟩⟩

-- Both honest nodes emit and accept at zero. The deadline 2 is within the run.
private def servedEnv : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun _ t => decide (0 ≤ t)⟩

private def servedRun : Run (Fin 2) toy :=
  { run with horizon := 2, events := [.tick 0 0, .tick 1 0,
      .deliver 0 first 0, .deliver 1 first 0, .tick 0 2, .tick 1 2] }

private theorem served_valid : ExecutionValid servedEnv servedRun := by
  refine { toScheduleWellFormed := ?_, toSleepWellFormed := ?_,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp only [servedRun, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e _; exact Finset.mem_univ _
    · intro v t h
      simp only [servedRun, List.mem_cons, List.not_mem_nil, or_false,
        Event.tick.injEq, reduceCtorEq, false_or, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨1, rfl⟩
    · intro v _ t ⟨k, hk⟩ h0 hh _
      have ht : t = 0 ∨ t = 2 := by
        simp [servedEnv] at hk
        simp [servedRun] at hh
        dsimp [Time] at *; omega
      fin_cases v <;> rcases ht with rfl | rfl <;> decide
  · refine ⟨by intros; rfl, by intros; rfl, ?_⟩
    intro i v o t hi
    have hb := (List.getElem?_eq_some_iff.mp hi).1
    simp [servedRun] at hb
    interval_cases i <;> simp [servedRun] at hi
    all_goals rcases hi with ⟨rfl, rfl, rfl⟩; decide
  · refine ⟨?_, ?_⟩
    · rintro v o t ⟨i, hi⟩ u _ hu
      have h := List.mem_of_getElem? hi
      simp only [servedRun, List.mem_cons, List.not_mem_nil, or_false,
        Event.deliver.injEq, reduceCtorEq, false_or, or_false] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp [Run.holder, first] at hu
    · intro v o t _ o' hc; exact hc.elim
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v t h
      simp only [servedRun, List.mem_cons, List.not_mem_nil, or_false,
        Event.tick.injEq, reduceCtorEq, false_or, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · intro v o t h
      simp only [servedRun, List.mem_cons, List.not_mem_nil, or_false,
        Event.deliver.injEq, reduceCtorEq, false_or, or_false] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    · intro v t h; simp [servedRun] at h
    · intro v _ t h0 _ hw
      simp [Wakes, servedEnv] at hw
      dsimp [Time] at *; omega

private theorem served_emits {v o t} (h : Run.emits servedEnv servedRun v o t) :
    o = first := by
  rcases h with ⟨i, hi, ho⟩
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  simp [servedRun] at hb
  interval_cases i <;> first
    | exact List.mem_singleton.mp ho
    | exact (List.not_mem_nil ho).elim

private theorem served_accepts {i v o t}
    (h : Run.acceptsAt servedEnv servedRun i v o t) : o = first := by
  rcases h.1 with ⟨o', hi, he⟩
  have hm := List.mem_of_getElem? hi
  simp only [servedRun, List.mem_cons, List.not_mem_nil, or_false,
    Event.deliver.injEq, reduceCtorEq, false_or, or_false] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> exact he.symm

private theorem served_demand (v w : Fin 2) (send : Time) (dl : Time → Time)
    (hd : ∀ a, 0 ≤ a → dl a = a + 2) :
    DeliveryDemand servedEnv servedRun v w first send dl 2 := by
  intro a _ ha _ hc _ _ _
  have ha0 : a = 0 := by rw [hd a ha] at hc; dsimp [Time] at *; omega
  subst a
  rw [hd 0 (by decide)]
  apply Or.inr
  fin_cases w
  · exact ⟨0, by decide, by decide, 2, first, rfl, rfl⟩
  · exact ⟨0, by decide, by decide, 3, first, rfl, rfl⟩

private theorem served_partial : PartialSynchrony servedEnv servedRun := by
  constructor
  · intro v _ o t he w _
    rw [served_emits he]
    exact served_demand v w t _ (fun a ha => by simp [servedEnv, max_eq_left ha])
  · intro v _ i o t he w _
    rw [served_accepts he]
    exact served_demand v w t _ (fun a ha => by simp [servedEnv, max_eq_left ha])

private theorem served_healthy : HealthyPrefixDelivery servedEnv servedRun 2 := by
  constructor
  · intro v _ o t he w _
    rw [served_emits he]
    exact served_demand v w t _ (by intros; rfl)
  · intro v _ i o t he w _
    rw [served_accepts he]
    exact served_demand v w t _ (by intros; rfl)

example : D.ExecutionValid servedEnv servedRun.toD ∧
    D.PartialSynchrony servedEnv servedRun.toD ∧
    D.HealthyPrefixDelivery servedEnv servedRun.toD 2 :=
  ⟨(D.executionValid_toD_iff servedEnv servedRun).mpr served_valid,
    (D.partialSynchrony_toD_iff servedEnv servedRun).mpr served_partial,
    (D.healthyPrefixDelivery_toD_iff servedEnv servedRun 2).mpr served_healthy⟩

-- An actual broadcast, acceptance, and all demand guards at anchor zero.
example : Run.emits servedEnv servedRun 0 first 0 ∧
    Run.acceptsAt servedEnv servedRun 2 0 first 0 ∧
    (0 : Fin 2) ∈ servedRun.honest ∧ (1 : Fin 2) ∈ servedRun.honest ∧
    (0 : Time) ≤ 0 ∧ (0 : Time) < 2 ∧ (2 : Time) ≤ servedRun.horizon ∧
    LinkReadyOn servedEnv servedRun 0 1 0 2 ∧
    toy.excludes (Run.stateBeforeTime servedEnv servedRun 2 1) first = false := by
  refine ⟨⟨0, rfl, by decide⟩, ?_, by decide, by decide,
    by decide, by decide, by decide, ?_, rfl⟩
  · exact ⟨⟨first, rfl, rfl⟩, by decide, by decide⟩
  · intro t ht _; simpa [servedEnv] using ht

-- Positive sleep premises include real restarts at both open interval endpoints.
private theorem sleep_restarts : RestartsAtWakes env run := by
  intro v t h
  simp only [run, List.mem_cons, List.not_mem_nil, or_false,
    Event.restart.injEq, reduceCtorEq, false_or, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, by unfold Wakes; decide⟩

example : D.RestartsAtWakes env run.toD := (D.restartsAtWakes_toD_iff env run).mpr sleep_restarts

private theorem noRestartOn : NoRestartOn run 0 5 10 := by
  intro i t hi ha hb
  have h := List.mem_of_getElem? hi
  simp only [run, List.mem_cons, List.not_mem_nil, or_false,
    Event.restart.injEq, reduceCtorEq, false_or, or_false] at h
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> dsimp [Time] at * <;> omega

example : D.NoRestartOn run.toD 0 5 10 := (D.noRestartOn_toD_iff run 0 5 10).mpr noRestartOn

-- The cut 10 is below horizon 11. Only the negative variant restarts after the cut.
private def extendedRun : Run (Fin 2) toy := { run with horizon := 11 }

private theorem extended_valid : ExecutionValid env extendedRun := by
  refine { engine_run_valid with
    horizon_nonneg := by decide, in_horizon := ?_,
    tick_total := ?_, wake_restart := ?_ }
  · intro e he
    have h := engine_run_valid.in_horizon e he
    exact ⟨h.1, le_trans h.2 (by decide)⟩
  · intro v hv t ⟨k, hk⟩ h0 hh ha
    have ht : t ≤ run.horizon := by
      simp [env] at hk
      simp [extendedRun] at hh
      dsimp [run, Time] at *; omega
    exact engine_run_valid.tick_total v hv t ⟨k, hk⟩ h0 ht ha
  · intro v hv t h0 hh hw
    have ht : t = 5 ∨ t = 10 := by
      fin_cases v <;> simp [Wakes, env] at hw <;> dsimp [Time] at * <;> omega
    exact engine_run_valid.wake_restart v hv t h0 (by rcases ht with rfl | rfl <;> decide) hw

private def lateRestart : Run (Fin 2) toy :=
  { extendedRun with events := run.events ++ [.restart 0 11] }

private theorem late_valid : ExecutionValid env lateRestart := by
  refine { extended_valid with
    sorted := by decide, nodup := by decide,
    in_horizon := ?_, honest_only := ?_, tick_public := ?_, tick_total := ?_,
    wire := by intros; rfl, deps := by intros; rfl, fresh := ?_,
    unforgeable := ?_, carried := ?_, tick_awake := ?_, deliver_awake := ?_,
    restart_awake := ?_, wake_restart := ?_ }
  · intro e he
    simp only [lateRestart, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact extended_valid.in_horizon e he
    · decide
  · intro e _; exact Finset.mem_univ _
  · intro v t h
    apply engine_run_valid.tick_public v t
    simpa [lateRestart] using h
  · intro v hv t hp h0 hh ha
    exact List.mem_append_left _ (extended_valid.tick_total v hv t hp h0 hh ha)
  · intro i v o t hi
    have hb := (List.getElem?_eq_some_iff.mp hi).1
    simp [lateRestart, run] at hb
    interval_cases i <;> simp [lateRestart, run] at hi
    all_goals rcases hi with ⟨rfl, rfl, rfl⟩; decide
  · rintro v o t ⟨i, hi⟩ u _ hu
    have he := List.mem_of_getElem? hi
    simp only [lateRestart, run, List.mem_append, List.mem_cons, List.not_mem_nil,
      Event.deliver.injEq, reduceCtorEq, false_or, or_false] at he
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [Run.holder, first, second] at hu
  · intro v o t _ o' hc; exact hc.elim
  · intro v t h
    apply engine_run_valid.tick_awake v t
    simpa [lateRestart] using h
  · intro v o t h
    apply engine_run_valid.deliver_awake v o t
    simpa [lateRestart] using h
  · intro v t h
    simp only [lateRestart, List.mem_append, List.mem_singleton, Event.restart.injEq] at h
    rcases h with h | ⟨rfl, rfl⟩
    · exact engine_run_valid.restart_awake v t h
    · decide
  · intro v hv t h0 hh hw
    exact List.mem_append_left _ (extended_valid.wake_restart v hv t h0 hh hw)

private theorem noRestartAfter : NoRestartAfter extendedRun 0 10 := by
  intro i t hi
  have h := List.mem_of_getElem? hi
  simp only [extendedRun, run, List.mem_cons, List.not_mem_nil,
    Event.restart.injEq, reduceCtorEq, false_or, or_false] at h
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide

example : 10 < extendedRun.horizon ∧ ExecutionValid env extendedRun ∧
    NoRestartAfter extendedRun 0 10 := ⟨by decide, extended_valid, noRestartAfter⟩

example : 10 < extendedRun.toD.horizon ∧ D.ExecutionValid env extendedRun.toD ∧
    D.NoRestartAfter extendedRun.toD 0 10 :=
  ⟨by decide, (D.executionValid_toD_iff env extendedRun).mpr extended_valid,
    (D.noRestartAfter_toD_iff extendedRun 0 10).mpr noRestartAfter⟩

example : 10 < lateRestart.horizon ∧ ExecutionValid env lateRestart ∧
    ¬ NoRestartAfter lateRestart 0 10 := by
  refine ⟨by decide, late_valid, ?_⟩
  intro h
  have := h 8 11 (by rfl)
  contradiction

example : 10 < lateRestart.toD.horizon ∧ D.ExecutionValid env lateRestart.toD ∧
    ¬ D.NoRestartAfter lateRestart.toD 0 10 := by
  refine ⟨by decide, (D.executionValid_toD_iff env lateRestart).mpr late_valid, ?_⟩
  intro h
  have := h 8 11 (by rfl)
  contradiction

example : AwakeOnClosed env 0 5 6 ∧ D.AwakeOnClosed env 0 5 6 := by
  constructor <;> intro t ha hb <;> simp [env] <;> dsimp [Time] at * <;> omega

end AvailableChain.V2.Tests.Sleep

end
