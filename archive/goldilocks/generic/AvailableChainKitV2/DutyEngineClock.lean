module
public import AvailableChainKitV2.DutySleep
public import AvailableChainKitV2.DutyClockLaws
public import AvailableChainKitV2.DutyStable -- shake: keep (re-export)

public section

/-! Clock source, clock bounds, invariants, and field laws for duty runs.
Each law keeps its recordOwn and restore premises. Time is Int, so a
restored clock can be negative. -/

namespace AvailableChain.V2.D.Engine

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

private theorem stateBefore_zero (E : Generic.Env V) (rho : Run V P) (v : V) :
    Run.stateBefore E rho 0 v = P.init := by
  rfl

/-! ### The clock source and the clock bound -/

/-- The clock source, for a property `R` of restored clocks. -/
private theorem now_source_aux (C : ClockLaws P) (E : Generic.Env V) (rho : Run V P) (v : V)
    (R : Time → Prop) (hR0 : R 0)
    (hR : ∀ k t, rho.events[k]? = some (.restart v t) →
      R (C.now (P.restore (P.durable (Run.stateBefore E rho k v)) t))) (i : Nat) :
    R (C.now (Run.stateBefore E rho i v)) ∨
      ∃ j < i, rho.events[j]? = some (.tick v (C.now (Run.stateBefore E rho i v))) := by
  induction i with
  | zero => left; rw [stateBefore_zero, C.init]; exact hR0
  | succ i ih =>
      have ih' : R (C.now (Run.stateBefore E rho i v)) ∨
          ∃ j < i + 1, rho.events[j]? = some (.tick v (C.now (Run.stateBefore E rho i v))) :=
        ih.imp_right fun ⟨j, hj, he⟩ => ⟨j, Nat.lt_succ_of_lt hj, he⟩
      cases hi : rho.events[i]? with
      | none => simpa [Run.stateBefore, List.take_add_one, hi] using ih'
      | some e =>
          rw [Run.stateBefore_succ E rho hi]
          by_cases hv : e.node = v
          · cases e with
            | restart u t =>
                dsimp only [Event.node] at hv; subst u
                left
                simpa only [World.step, Function.update_self] using hR i t hi
            | tick u t =>
                dsimp only [Event.node] at hv; subst u
                right
                simp only [World.step, Function.update_self, C.now_tick]
                exact ⟨i, Nat.lt_succ_self i, hi⟩
            | deliver u o t =>
                dsimp only [Event.node] at hv; subst u
                simpa only [World.step, Function.update_self, C.process] using ih'
          · rwa [World.step_apply_of_node_ne E rho _ hv]

/-- A stored clock value is at most `0` or comes from an earlier local tick
(Astra re-check 2, M1: `Time` is `Int`, and a restore may give a negative
clock, so the first case is `≤ 0`, not `= 0`). -/
theorem stateBefore_now_source (C : ClockLaws P) (hrestore_now : ∀ d t, C.now (P.restore d t) ≤ 0)
    (E : Generic.Env V) (rho : Run V P) (i : Nat) (v : V) :
    C.now (Run.stateBefore E rho i v) ≤ 0 ∨
      ∃ j < i, rho.events[j]? = some (.tick v (C.now (Run.stateBefore E rho i v))) :=
  now_source_aux C E rho v (· ≤ 0) le_rfl (fun _ _ _ => hrestore_now _ _) i

/-- Without restarts, a stored clock value is zero or comes from an earlier
local tick (the v1 statement). -/
theorem stateBefore_now_source_noRestart (C : ClockLaws P) (E : Generic.Env V)
    (rho : Run V P) (hnr : NoRestart rho) (i : Nat) (v : V) :
    C.now (Run.stateBefore E rho i v) = 0 ∨
      ∃ j < i, rho.events[j]? = some (.tick v (C.now (Run.stateBefore E rho i v))) :=
  now_source_aux C E rho v (· = 0) rfl (fun k t h => absurd h (hnr k v t)) i

/-- The clock bound, for restores that give a clock at most `0`. -/
private theorem now_le_event_aux (C : ClockLaws P) (E : Generic.Env V) (rho : Run V P)
    (hs : ScheduleWellFormed E rho) (v : V)
    (hR : ∀ k t, rho.events[k]? = some (.restart v t) →
      C.now (P.restore (P.durable (Run.stateBefore E rho k v)) t) ≤ 0)
    {i : Nat} {e : Event V P.Object} (hi : rho.events[i]? = some e) :
    C.now (Run.stateBefore E rho i v) ≤ e.time := by
  rcases now_source_aux C E rho v (· ≤ 0) le_rfl hR i with hz | ⟨j, hj, ht⟩
  · exact le_trans hz (hs.in_horizon e (List.mem_of_getElem? hi)).1
  · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ht
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hj
    rw [hje, hie] at hk
    exact time_le_of_key_le _ _ hk

/-- No reader's clock can exceed the next event time. The fact depends on the
whole prefix, so it takes `hrestore_now` and holds across restarts. -/
theorem stateBefore_now_le_event (C : ClockLaws P)
    (hrestore_now : ∀ d t, C.now (P.restore d t) ≤ 0)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V P.Object}
    (hi : rho.events[i]? = some e) (v : V) :
    C.now (Run.stateBefore E rho i v) ≤ e.time :=
  now_le_event_aux C E rho hs v (fun _ _ _ => hrestore_now _ _) hi

/-- `stateBefore_now_le_event` without restarts. -/
theorem stateBefore_now_le_event_noRestart (C : ClockLaws P)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (hnr : NoRestart rho) {i : Nat} {e : Event V P.Object}
    (hi : rho.events[i]? = some e) (v : V) :
    C.now (Run.stateBefore E rho i v) ≤ e.time :=
  now_le_event_aux C E rho hs v (fun k t h => absurd h (hnr k v t)) hi

/-! ### Monotone clocks -/

private theorem now_mono_aux (C : ClockLaws P) (E : Generic.Env V) (rho : Run V P)
    (hs : ScheduleWellFormed E rho) (v : V)
    (hR : ∀ k t, rho.events[k]? = some (.restart v t) →
      C.now (P.restore (P.durable (Run.stateBefore E rho k v)) t) ≤ 0)
    {i j : Nat} (hij : i ≤ j) (hrf : restartFree rho v i j) :
    C.now (Run.stateBefore E rho i v) ≤ C.now (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho (fun st => C.now (Run.stateBefore E rho i v) ≤ C.now st)
    hij v ?_ le_rfl
  intro k e hik hkj he hv hk
  cases e with
  | restart u t =>
      dsimp only [Event.node] at hv; subst u
      exact absurd he (hrf k t hik hkj)
  | tick u t =>
      dsimp only [Event.node] at hv; subst u
      simp only [World.step, Function.update_self, C.now_tick]
      exact le_trans hk (now_le_event_aux C E rho hs v hR he)
  | deliver u o t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [World.step, Function.update_self, C.process] using hk

/-- Local clock values increase on a restart-free interval of a valid run.
The interval must be restart-free (a restart lowers `now`), and the ticks in
it use the clock bound, so the lemma also takes `hrestore_now`. -/
theorem stateBefore_now_mono (C : ClockLaws P) (hrestore_now : ∀ d t, C.now (P.restore d t) ≤ 0)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    {i j : Nat} (hij : i ≤ j) (v : V) (hrf : restartFree rho v i j) :
    C.now (Run.stateBefore E rho i v) ≤ C.now (Run.stateBefore E rho j v) :=
  now_mono_aux C E rho hs v (fun _ _ _ => hrestore_now _ _) hij hrf

/-- `stateBefore_now_mono` without restarts. -/
theorem stateBefore_now_mono_noRestart (C : ClockLaws P)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (hnr : NoRestart rho) {i j : Nat} (hij : i ≤ j) (v : V) :
    C.now (Run.stateBefore E rho i v) ≤ C.now (Run.stateBefore E rho j v) :=
  now_mono_aux C E rho hs v (fun k t h => absurd h (hnr k v t)) hij (hnr.restartFree v i j)

/-- A delivery after a required local public tick has a clock at least
that tick time. The reader is awake at that tick. It needs `NoRestart`: a
restart of the reader between the tick and the delivery lowers its clock. -/
theorem delivery_now_ge_public (C : ClockLaws P)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (hnr : NoRestart rho)
    {i : Nat} {v : V} {o : P.Object} {a t : Time}
    (hi : rho.events[i]? = some (.deliver v o t))
    (ha : PublicTime E a) (ha0 : 0 ≤ a) (hat : a ≤ t)
    (hawake : E.awake v a = true) :
    a ≤ C.now (Run.stateBefore E rho i v) := by
  have hm := List.mem_of_getElem? hi
  have hv := hs.honest_only _ hm
  have ht := (hs.in_horizon _ hm).2
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
    (hs.tick_total v hv a ha ha0 (hat.trans ht) hawake)
  have hji := tick_index_lt_delivery E rho hs hj hi hat
  have hb := stateBefore_now_mono_noRestart C E rho hs hnr (Nat.succ_le_of_lt hji) v
  rw [Run.stateBefore_succ E rho hj] at hb
  simpa [World.step, C.now_tick] using hb

/-- A clock value comes from initialization, a tick, or a restart. -/
theorem stateBefore_now_source_atRestart (C : ClockLaws P) (R : RestoreTimeLaw C)
    (E : Generic.Env V) (rho : Run V P) (i : Nat) (v : V) :
    C.now (Run.stateBefore E rho i v) = 0 ∨
      ∃ j < i, rho.events[j]? = some (.tick v (C.now (Run.stateBefore E rho i v))) ∨
        rho.events[j]? = some (.restart v (C.now (Run.stateBefore E rho i v))) := by
  induction i with
  | zero => exact Or.inl C.init
  | succ i ih =>
      have ih' : C.now (Run.stateBefore E rho i v) = 0 ∨
          ∃ j < i + 1, rho.events[j]? = some (.tick v (C.now (Run.stateBefore E rho i v))) ∨
            rho.events[j]? = some (.restart v (C.now (Run.stateBefore E rho i v))) :=
        ih.imp_right fun ⟨j, hj, he⟩ => ⟨j, Nat.lt_succ_of_lt hj, he⟩
      cases hi : rho.events[i]? with
      | none => simpa [Run.stateBefore, List.take_add_one, hi] using ih'
      | some e =>
          rw [Run.stateBefore_succ E rho hi]
          by_cases hv : e.node = v
          · cases e with
            | restart u t =>
                change u = v at hv; subst u
                simp only [World.step, Function.update_self, R.restore_now]
                exact Or.inr ⟨i, Nat.lt_succ_self i, Or.inr hi⟩
            | tick u t =>
                change u = v at hv; subst u
                simp only [World.step, Function.update_self, C.now_tick]
                exact Or.inr ⟨i, Nat.lt_succ_self i, Or.inl hi⟩
            | deliver u o t =>
                change u = v at hv; subst u
                simpa only [World.step, Function.update_self, C.process] using ih'
          · rwa [World.step_apply_of_node_ne E rho _ hv]

/-- The exact wake clock is at most the next event time. -/
theorem stateBefore_now_le_event_atRestart (C : ClockLaws P) (R : RestoreTimeLaw C)
    (E : Generic.Env V) (rho : Run V P) (hS : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V P.Object} (he : rho.events[i]? = some e) (v : V) :
    C.now (Run.stateBefore E rho i v) ≤ e.time := by
  rcases stateBefore_now_source_atRestart C R E rho i v with hz | ⟨j, hj, h⟩
  · rw [hz]; exact (hS.in_horizon _ (List.mem_of_getElem? he)).1
  · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp he
    rcases h with h | h <;>
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp h <;>
      have hk := (List.pairwise_iff_getElem.mp hS.sorted) j i hjl hil hj <;>
      rw [hje, hie] at hk <;> exact time_le_of_key_le _ _ hk

/-- The clock is monotone through ticks and exact-time restarts. -/
theorem stateBefore_now_mono_atRestart (C : ClockLaws P) (R : RestoreTimeLaw C)
    (E : Generic.Env V) (rho : Run V P) (hS : ScheduleWellFormed E rho)
    {i j : Nat} (hij : i ≤ j) (v : V) :
    C.now (Run.stateBefore E rho i v) ≤ C.now (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho
    (fun st => C.now (Run.stateBefore E rho i v) ≤ C.now st) hij v ?_ le_rfl
  intro k e _ _ he hv hk
  have hb := stateBefore_now_le_event_atRestart C R E rho hS he v
  cases e with
  | restart u t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self, R.restore_now, Event.time] using hk.trans hb
  | tick u t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self, C.now_tick, Event.time] using hk.trans hb
  | deliver u o t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self, C.process] using hk

/-- Delivery after a public time has passed that time, even through sleep. -/
theorem delivery_now_ge_public_atRestart (C : ClockLaws P) (R : RestoreTimeLaw C)
    (E : Generic.Env V) (rho : Run V P) (hV : ExecutionValid E rho)
    {i : Nat} {v : V} {o : P.Object} {a t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (ha : PublicTime E a) (ha0 : 0 ≤ a) (hat : a ≤ t) :
    a ≤ C.now (Run.stateBefore E rho i v) := by
  have hm := List.mem_of_getElem? he
  have hv := hV.honest_only _ hm
  have hh := (hV.in_horizon _ hm).2
  cases haw : E.awake v a with
  | true =>
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
        (hV.tick_total v hv a ha ha0 (hat.trans hh) haw)
      have hji := tick_index_lt_delivery E rho hV.toScheduleWellFormed hj he hat
      have hb := stateBefore_now_mono_atRestart C R E rho hV.toScheduleWellFormed
        (Nat.succ_le_of_lt hji) v
      rw [Run.stateBefore_succ E rho hj] at hb
      simpa only [World.step, Function.update_self, C.now_tick] using hb
  | false =>
      obtain ⟨w, haw, hwt, hw⟩ := wake_between hat haw (hV.deliver_awake v o t hm)
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
        (hV.wake_restart v hv w (ha0.trans_lt haw) (hwt.trans hh) hw)
      have hji := restart_index_lt_event hV.toScheduleWellFormed hj he hwt
        (show 0 < 2 from by decide)
      have hb := stateBefore_now_mono_atRestart C R E rho hV.toScheduleWellFormed
        (Nat.succ_le_of_lt hji) v
      rw [state_after_restart hj, R.restore_now] at hb
      exact (le_of_lt haw).trans hb

/-- Stability with the clock precondition and a restore preservation law. -/
theorem stateBefore_stable_clock_atRestart (C : ClockLaws P) (R : RestoreTimeLaw C)
    (E : Generic.Env V) (rho : Run V P) (hS : ScheduleWellFormed E rho)
    (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t))
    {i j : Nat} (hij : i ≤ j) (v : V) (hi : Q (Run.stateBefore E rho i v)) :
    Q (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q hij v ?_ hi
  intro k e _ _ he hv hk
  cases e with
  | restart u t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self] using hrestore _ t hk
  | tick u t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self] using
        tick_preserve E rho Q hrecord
          (hclock _ t (stateBefore_now_le_event_atRestart C R E rho hS he v) hk)
  | deliver u o t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self] using hprocess _ o hk

/-- Exact wake clocks also support properties on a restart-free interval. -/
theorem stateBefore_stable_clock_restartFree (C : ClockLaws P) (R : RestoreTimeLaw C)
    (E : Generic.Env V) (rho : Run V P) (hS : ScheduleWellFormed E rho)
    (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    {i j : Nat} (hij : i ≤ j) (v : V) (hrf : restartFree rho v i j)
    (hi : Q (Run.stateBefore E rho i v)) :
    Q (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q hij v ?_ hi
  intro k e hik hkj he hv hk
  cases e with
  | restart u t =>
      change u = v at hv; subst u
      exact absurd he (hrf k t hik hkj)
  | tick u t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self] using
        tick_preserve E rho Q hrecord
          (hclock _ t (stateBefore_now_le_event_atRestart C R E rho hS he v) hk)
  | deliver u o t =>
      change u = v at hv; subst u
      simpa only [World.step, Function.update_self] using hprocess _ o hk

/-- A restore-safe invariant holds for the entire run with exact wake clocks. -/
theorem stateBefore_invariant_atRestart (C : ClockLaws P) (R : RestoreTimeLaw C)
    (E : Generic.Env V) (rho : Run V P) (hS : ScheduleWellFormed E rho)
    (Q : P.State → Prop) (hinit : Q P.init)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t)) (i : Nat) (v : V) :
    Q (Run.stateBefore E rho i v) :=
  stateBefore_stable_clock_atRestart C R E rho hS Q hclock hprocess hrecord hrestore
    (Nat.zero_le i) v hinit

/-! ### Invariants and stability with the clock precondition -/

/-- Stability with the clock precondition on `[i, j)`, for a restart step
`hrestart` and restores that give a clock at most `0`. -/
private theorem stable_clock_aux (C : ClockLaws P) (E : Generic.Env V) (rho : Run V P)
    (hs : ScheduleWellFormed E rho) (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    {i j : Nat} (hij : i ≤ j) (v : V)
    (hR : ∀ k t, rho.events[k]? = some (.restart v t) →
      C.now (P.restore (P.durable (Run.stateBefore E rho k v)) t) ≤ 0)
    (hrestart : ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.restart v t) →
      Q (Run.stateBefore E rho k v) →
      Q (P.restore (P.durable (Run.stateBefore E rho k v)) t))
    (hi : Q (Run.stateBefore E rho i v)) : Q (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q hij v ?_ hi
  intro k e hik hkj he hv hk
  cases e with
  | restart u t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [World.step, Function.update_self] using hrestart k t hik hkj he hk
  | tick u t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [World.step, Function.update_self] using
        tick_preserve E rho Q hrecord (hclock _ t (now_le_event_aux C E rho hs v hR he) hk)
  | deliver u o t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [World.step, Function.update_self] using hprocess _ o hk

/-- A local invariant can use the fact that a valid clock tick never moves
backwards. It holds across restarts: `restore` keeps it (`hrestore`), and the
clock bound at every tick uses `hrestore_now`. -/
theorem stateBefore_invariant (C : ClockLaws P) (hrestore_now : ∀ d t, C.now (P.restore d t) ≤ 0)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (Q : P.State → Prop) (hinit : Q P.init)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t)) (i : Nat) (v : V) :
    Q (Run.stateBefore E rho i v) :=
  stable_clock_aux C E rho hs Q hclock hprocess hrecord (Nat.zero_le i) v
    (fun _ _ _ => hrestore_now _ _) (fun _ t _ _ _ => hrestore _ t)
    (by rw [stateBefore_zero]; exact hinit)

/-- `stateBefore_invariant` without restarts. -/
theorem stateBefore_invariant_noRestart (C : ClockLaws P)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (hnr : NoRestart rho)
    (Q : P.State → Prop) (hinit : Q P.init)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o)) (i : Nat) (v : V) :
    Q (Run.stateBefore E rho i v) :=
  stable_clock_aux C E rho hs Q hclock hprocess hrecord (Nat.zero_le i) v
    (fun k t h => absurd h (hnr k v t)) (fun k t _ _ h => absurd h (hnr k v t))
    (by rw [stateBefore_zero]; exact hinit)

/-- A state property that `process` and `recordOwn` keep, and that `clock`
keeps when the tick does not move backwards, holds on a restart-free interval
of a valid run. This is the run-indexed form of `stateBefore_stable`. It
needs `restartFree` on `[i, j)`: `hrestore_now` alone does not keep `Q`
through a restart (DC N1). -/
theorem stateBefore_stable_clock (C : ClockLaws P)
    (hrestore_now : ∀ d t, C.now (P.restore d t) ≤ 0)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    {i j : Nat} (hij : i ≤ j) (v : V) (hrf : restartFree rho v i j)
    (hi : Q (Run.stateBefore E rho i v)) : Q (Run.stateBefore E rho j v) :=
  stable_clock_aux C E rho hs Q hclock hprocess hrecord hij v
    (fun _ _ _ => hrestore_now _ _) (fun k t hik hkj h => absurd h (hrf k t hik hkj)) hi

/-- The restore form of `stateBefore_stable_clock`: `restore` keeps `Q`
(`hrestore`), and the interval may contain restarts (DC N1 check). -/
theorem stateBefore_stable_clock_restore (C : ClockLaws P)
    (hrestore_now : ∀ d t, C.now (P.restore d t) ≤ 0)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t))
    {i j : Nat} (hij : i ≤ j) (v : V)
    (hi : Q (Run.stateBefore E rho i v)) : Q (Run.stateBefore E rho j v) :=
  stable_clock_aux C E rho hs Q hclock hprocess hrecord hij v
    (fun _ _ _ => hrestore_now _ _) (fun _ t _ _ _ => hrestore _ t) hi

/-- `stateBefore_stable_clock` without restarts. -/
theorem stateBefore_stable_clock_noRestart (C : ClockLaws P)
    (E : Generic.Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (hnr : NoRestart rho) (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    {i j : Nat} (hij : i ≤ j) (v : V)
    (hi : Q (Run.stateBefore E rho i v)) : Q (Run.stateBefore E rho j v) :=
  stable_clock_aux C E rho hs Q hclock hprocess hrecord hij v
    (fun k t h => absurd h (hnr k v t)) (fun k t _ _ h => absurd h (hnr k v t)) hi

/-! ### Field lemmas -/

private theorem mem_field_foldl_recordOwn {α : Type} (field : P.State → List α)
    (hrecord : ∀ st o x, x ∈ field (P.recordOwn st o) → x ∈ field st) (x : α) :
    ∀ (l : List P.Object) (s : P.State), x ∈ field (l.foldl P.recordOwn s) → x ∈ field s := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons o rest ih =>
      intro s h
      rw [List.foldl_cons] at h
      exact hrecord s o x (ih _ h)

/-- The field origin, for a restart step that adds no rows. -/
private theorem field_origin_aux {α : Type} (field : P.State → List α)
    (hinit : field P.init = [])
    (hprocess : ∀ st o, field (P.process st o) = field st)
    (hrecord : ∀ st o x, x ∈ field (P.recordOwn st o) → x ∈ field st)
    (Q : P.State → Time → α → Prop)
    (hclock : ∀ st t row, row ∈ field (P.clock st t) → row ∈ field st ∨ Q st t row)
    (E : Generic.Env V) (rho : Run V P) (v : V)
    (hR : ∀ k t x, rho.events[k]? = some (.restart v t) →
      x ∈ field (P.restore (P.durable (Run.stateBefore E rho k v)) t) →
      x ∈ field (Run.stateBefore E rho k v))
    (index : Nat) (row : α) (hm : row ∈ field (Run.stateBefore E rho index v)) :
    ∃ j < index, ∃ t, rho.events[j]? = some (.tick v t) ∧
      Q (Run.stateBefore E rho j v) t row := by
  induction index with
  | zero => rw [stateBefore_zero, hinit] at hm; simp at hm
  | succ index ih =>
      have ih' : row ∈ field (Run.stateBefore E rho index v) → ∃ j < index + 1, ∃ t,
          rho.events[j]? = some (.tick v t) ∧ Q (Run.stateBefore E rho j v) t row :=
        fun h => let ⟨j, hj, rest⟩ := ih h; ⟨j, Nat.lt_succ_of_lt hj, rest⟩
      cases hi : rho.events[index]? with
      | none => exact ih' (by simpa [Run.stateBefore, List.take_add_one, hi] using hm)
      | some e =>
          rw [Run.stateBefore_succ E rho hi] at hm
          by_cases hv : e.node = v
          · cases e with
            | restart u t =>
                dsimp only [Event.node] at hv; subst u
                simp only [World.step, Function.update_self] at hm
                exact ih' (hR index t row hi hm)
            | tick u t =>
                dsimp only [Event.node] at hv; subst u
                simp only [World.step, Function.update_self, tick_decomp] at hm
                rcases hclock _ t row (mem_field_foldl_recordOwn field hrecord row _ _ hm) with
                  hold | hnew
                · exact ih' hold
                · exact ⟨index, Nat.lt_succ_self index, t, hi, hnew⟩
            | deliver u o t =>
                dsimp only [Event.node] at hv; subst u
                simp only [World.step, Function.update_self, hprocess] at hm
                exact ih' hm
          · rw [World.step_apply_of_node_ne E rho _ hv] at hm
            exact ih' hm

/-- A stored row whose only source is a local clock has a prior tick with
that source property. This includes immutable saves and freezes. The own
record adds no rows (`hrecord`), and `restore` adds no rows
(`hrestore_field`; it holds when `field init = []` and `restore := fun _ _ =>
init`). -/
theorem clock_field_origin {α : Type} (field : P.State → List α)
    (hinit : field P.init = [])
    (hprocess : ∀ st o, field (P.process st o) = field st)
    (hrecord : ∀ st o x, x ∈ field (P.recordOwn st o) → x ∈ field st)
    (hrestore_field : ∀ st t x, x ∈ field (P.restore (P.durable st) t) → x ∈ field st)
    (Q : P.State → Time → α → Prop)
    (hclock : ∀ st t row, row ∈ field (P.clock st t) → row ∈ field st ∨ Q st t row)
    (E : Generic.Env V) (rho : Run V P) (index : Nat) (v : V) (row : α)
    (hm : row ∈ field (Run.stateBefore E rho index v)) :
    ∃ j < index, ∃ t, rho.events[j]? = some (.tick v t) ∧
      Q (Run.stateBefore E rho j v) t row :=
  field_origin_aux field hinit hprocess hrecord Q hclock E rho v
    (fun _ t x _ h => hrestore_field _ t x h) index row hm

/-- `clock_field_origin` without restarts. -/
theorem clock_field_origin_noRestart {α : Type} (field : P.State → List α)
    (hinit : field P.init = [])
    (hprocess : ∀ st o, field (P.process st o) = field st)
    (hrecord : ∀ st o x, x ∈ field (P.recordOwn st o) → x ∈ field st)
    (Q : P.State → Time → α → Prop)
    (hclock : ∀ st t row, row ∈ field (P.clock st t) → row ∈ field st ∨ Q st t row)
    (E : Generic.Env V) (rho : Run V P) (hnr : NoRestart rho) (index : Nat) (v : V)
    (row : α) (hm : row ∈ field (Run.stateBefore E rho index v)) :
    ∃ j < index, ∃ t, rho.events[j]? = some (.tick v t) ∧
      Q (Run.stateBefore E rho j v) t row :=
  field_origin_aux field hinit hprocess hrecord Q hclock E rho v
    (fun k t _ h => absurd h (hnr k v t)) index row hm

/-- The field origin, for a restart step that adds no rows. -/
private theorem field_origin_of_subset_aux {α : Type} (field : P.State → List α)
    (hinit : field P.init = [])
    (hprocess : ∀ st o a, a ∈ field (P.process st o) → a ∈ field st)
    (hrecord : ∀ st o x, x ∈ field (P.recordOwn st o) → x ∈ field st)
    (Q : P.State → Time → α → Prop)
    (hclock : ∀ st t row, row ∈ field (P.clock st t) → row ∈ field st ∨ Q st t row)
    (E : Generic.Env V) (rho : Run V P) (v : V)
    (hR : ∀ k t x, rho.events[k]? = some (.restart v t) →
      x ∈ field (P.restore (P.durable (Run.stateBefore E rho k v)) t) →
      x ∈ field (Run.stateBefore E rho k v))
    (index : Nat) (row : α) (hm : row ∈ field (Run.stateBefore E rho index v)) :
    ∃ j < index, ∃ t, rho.events[j]? = some (.tick v t) ∧
      Q (Run.stateBefore E rho j v) t row := by
  induction index with
  | zero => rw [stateBefore_zero, hinit] at hm; simp at hm
  | succ index ih =>
      have ih' : row ∈ field (Run.stateBefore E rho index v) → ∃ j < index + 1, ∃ t,
          rho.events[j]? = some (.tick v t) ∧ Q (Run.stateBefore E rho j v) t row :=
        fun h => let ⟨j, hj, rest⟩ := ih h; ⟨j, Nat.lt_succ_of_lt hj, rest⟩
      cases hi : rho.events[index]? with
      | none => exact ih' (by simpa [Run.stateBefore, List.take_add_one, hi] using hm)
      | some e =>
          rw [Run.stateBefore_succ E rho hi] at hm
          by_cases hv : e.node = v
          · cases e with
            | restart u t =>
                dsimp only [Event.node] at hv; subst u
                simp only [World.step, Function.update_self] at hm
                exact ih' (hR index t row hi hm)
            | tick u t =>
                dsimp only [Event.node] at hv; subst u
                simp only [World.step, Function.update_self, tick_decomp] at hm
                rcases hclock _ t row (mem_field_foldl_recordOwn field hrecord row _ _ hm) with
                  hold | hnew
                · exact ih' hold
                · exact ⟨index, Nat.lt_succ_self index, t, hi, hnew⟩
            | deliver u o t =>
                dsimp only [Event.node] at hv; subst u
                simp only [World.step, Function.update_self] at hm
                exact ih' (hprocess _ o row hm)
          · rw [World.step_apply_of_node_ne E rho _ hv] at hm
            exact ih' hm

/-- [helper] A stored element comes from a prior local tick when all other
steps can only remove elements. -/
theorem clock_field_origin_of_subset {α : Type} (field : P.State → List α)
    (hinit : field P.init = [])
    (hprocess : ∀ st o a, a ∈ field (P.process st o) → a ∈ field st)
    (hrecord : ∀ st o a, a ∈ field (P.recordOwn st o) → a ∈ field st)
    (hrestore : ∀ st t a, a ∈ field (P.restore (P.durable st) t) → a ∈ field st)
    (Q : P.State → Time → α → Prop)
    (hclock : ∀ st t a, a ∈ field (P.clock st t) → a ∈ field st ∨ Q st t a)
    (E : Generic.Env V) (rho : Run V P) (index : Nat) (v : V) (a : α)
    (hm : a ∈ field (Run.stateBefore E rho index v)) :
    ∃ j < index, ∃ t, rho.events[j]? = some (.tick v t) ∧ Q (Run.stateBefore E rho j v) t a :=
  field_origin_of_subset_aux field hinit hprocess hrecord Q hclock E rho v
    (fun _ t x _ h => hrestore _ t x h) index a hm

/-- The field prefix on `[i, j)`, for a restart step that keeps the prefix. -/
private theorem field_prefix_aux {α : Type} (field : P.State → List α)
    (hclock : ∀ st t, field st <+: field (P.clock st t))
    (hprocess : ∀ st o, field st <+: field (P.process st o))
    (hrecord : ∀ st o, field st <+: field (P.recordOwn st o))
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrestart : ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.restart v t) →
      field (Run.stateBefore E rho k v) <+:
        field (P.restore (P.durable (Run.stateBefore E rho k v)) t)) :
    field (Run.stateBefore E rho i v) <+: field (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho
    (fun st => field (Run.stateBefore E rho i v) <+: field st) hij v ?_ (List.prefix_refl _)
  intro k e hik hkj he hv hk
  cases e with
  | restart u t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [World.step, Function.update_self] using hk.trans (hrestart k t hik hkj he)
  | tick u t =>
      dsimp only [Event.node] at hv; subst u
      simp only [World.step, Function.update_self]
      exact tick_preserve E rho (fun st => field (Run.stateBefore E rho i v) <+: field st)
        (fun st o h => h.trans (hrecord st o)) (hk.trans (hclock _ t))
  | deliver u o t =>
      dsimp only [Event.node] at hv; subst u
      simpa only [World.step, Function.update_self] using hk.trans (hprocess _ o)

/-- A field that only grows by append keeps its rows as a prefix on a
restart-free interval. The own record keeps the prefix (`hrecord`). -/
theorem stateBefore_field_prefix {α : Type} (field : P.State → List α)
    (hclock : ∀ st t, field st <+: field (P.clock st t))
    (hprocess : ∀ st o, field st <+: field (P.process st o))
    (hrecord : ∀ st o, field st <+: field (P.recordOwn st o))
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrf : restartFree rho v i j) :
    field (Run.stateBefore E rho i v) <+: field (Run.stateBefore E rho j v) :=
  field_prefix_aux field hclock hprocess hrecord E rho hij v
    (fun k t hik hkj h => absurd h (hrf k t hik hkj))

/-- The restore form of `stateBefore_field_prefix`: `restore` keeps the
prefix, and the interval may contain restarts. For `restore := fun _ _ =>
init`, use the `restartFree` form. -/
theorem stateBefore_field_prefix_restore {α : Type} (field : P.State → List α)
    (hclock : ∀ st t, field st <+: field (P.clock st t))
    (hprocess : ∀ st o, field st <+: field (P.process st o))
    (hrecord : ∀ st o, field st <+: field (P.recordOwn st o))
    (hrestore : ∀ st t, field st <+: field (P.restore (P.durable st) t))
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V) :
    field (Run.stateBefore E rho i v) <+: field (Run.stateBefore E rho j v) :=
  field_prefix_aux field hclock hprocess hrecord E rho hij v
    (fun _ t _ _ _ => hrestore _ t)

end AvailableChain.V2.D.Engine

end
