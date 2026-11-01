module
public import AvailableChainKitV2.EngineClock

@[expose] public section

/-! Counterexample checks for the Kit v2 premises (plan 2a, Task 4 Step 4;
Review Focus 6). Each check shows that a premise of plan 2a D9 or Astra A03
is necessary: without it, the conclusion of the lemma fails on a run. The
checks are named theorems (`check_a_recordOwn_needed`,
`check_b_restore_now_needed`, `check_c_restartFree_needed`,
`check_d_unit_restore`, `check_d_unit_invariant`), so the axiom check covers
them.

(a) `stateBefore_stable` needs its `recordOwn` premise (Astra A03).
(b) `stateBefore_now_le_event` and `stateBefore_now_mono` need
`hrestore_now` (Astra N02; DC N1): a restore sets the clock to 100, and
`restartFree` on the interval does not help.
(c) `stateBefore_stable_clock` needs `restartFree` (or the restore form):
`hrestore_now` holds, but a restart clears `Q` (DC N1 check).
(d) With `restore := fun _ _ => init` (for example `Durable := Unit`),
`hrestore`, `hrestore_now` and `hrestore_field` hold (FG-SA T7). -/

namespace AvailableChain.V2.Engine.Tests

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- Every node is awake; public times are the multiples of 2. -/
def env2 (V : Type) : Generic.Env V :=
  ⟨2, by decide, 0, le_rfl, fun _ _ => true⟩

/-! ### (a) A private flag that `recordOwn` changes -/

/-- One self-visible label with one seat, due at time 0. The state is a
private flag: `clock` and `process` keep it, and `recordOwn` clears it. -/
abbrev specFlag : ProtocolSpec Unit where
  State := Bool
  Label := Unit
  seats := fun _ => 1
  Payload := Unit
  Durable := Unit
  init := true
  clock := fun s _ => s
  actTime := fun _ => 0
  duties := fun t => if t = 0 then [()] else []
  duties_spec := by
    intro ℓ t
    by_cases h : t = 0 <;> simp [h, eq_comm]
  duties_nodup := by
    intro t
    split_ifs <;> simp
  act := fun _ _ _ => some ()
  gossip := fun _ _ => []
  process := fun s _ => s
  selfVisible := fun _ => true
  recordOwn := fun _ _ => false
  durable := fun _ => ()
  restore := fun _ _ => true
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-- The only node holds the seat and ticks at 0. -/
def rhoFlag : Run Unit specFlag where
  honest := {()}
  horizon := 0
  events := [.tick () 0]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

/-- `clock` and `process` keep the flag, the interval `[0, 1)` has no restart,
and the flag holds before the tick, but not after it: the tick signs a
self-visible object, and `recordOwn` clears the flag. So the `recordOwn`
premise of `stateBefore_stable` fails, and it is necessary. -/
theorem check_a_recordOwn_needed :
    (∀ st t, st = true → specFlag.clock st t = true) ∧
      (∀ st o, st = true → specFlag.process st o = true) ∧
      ¬ (∀ st o, st = true → specFlag.recordOwn st o = true) ∧
      restartFree rhoFlag () 0 1 ∧
      Run.stateBefore (env2 _) rhoFlag 0 () = true ∧
      Run.stateBefore (env2 _) rhoFlag 1 () = false := by
  refine ⟨fun _ _ h => h, fun _ _ h => h, fun h => ?_, ?_, rfl, rfl⟩
  · exact Bool.false_ne_true (h true ⟨.seat () 0, ()⟩ rfl)
  · intro k t _ hk
    rw [show k = 0 by omega]
    simp [rhoFlag]

/-! ### (b) A restore that sets the clock to 100 (Astra N02) -/

/-- No labels. The state is the clock; `restore` sets it to 100. -/
abbrev specClock100 : ProtocolSpec Unit where
  State := Time
  Label := Empty
  seats := fun _ => 0
  Payload := Unit
  Durable := Unit
  init := 0
  clock := fun _ t => t
  actTime := fun ℓ => ℓ.elim
  duties := fun _ => []
  duties_spec := fun ℓ => ℓ.elim
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ _ _ => none
  gossip := fun _ _ => []
  process := fun s _ => s
  selfVisible := fun _ => false
  recordOwn := fun s _ => s
  durable := fun _ => ()
  restore := fun _ _ => 100
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-- The clock laws of `specClock100`: the state is the clock. -/
def clock100 : ClockLaws specClock100 where
  now := id
  init := rfl
  clock := fun _ _ => rfl
  process := fun _ _ => rfl
  recordOwn_now := fun _ _ => rfl

/-- Ticks at 0 and 2, and a restart at 1. -/
def rhoClock100 : Run Unit specClock100 where
  honest := {()}
  horizon := 2
  events := [.tick () 0, .restart () 1, .tick () 2]
  seatOf := fun ℓ => ℓ.elim
  input := fun _ _ => ()

/-- The public times in `[0, 2]` for `env2` are 0 and 2. -/
theorem publicTime_env2 {V : Type} {t : Time} (ht : PublicTime (env2 V) t) (h0 : 0 ≤ t)
    (h2 : t ≤ 2) : t = 0 ∨ t = 2 := by
  obtain ⟨k, rfl⟩ := ht
  have hk : (k : ℤ) * 2 ≤ 2 := h2
  have hk0 : 0 ≤ (k : ℤ) * 2 := h0
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · left; simp
  · right; rfl

theorem rhoClock100_wf : ScheduleWellFormed (env2 _) rhoClock100 where
  horizon_nonneg := by decide
  sorted := by simp [rhoClock100, Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex]
  nodup := by simp [rhoClock100]
  in_horizon := by simp [rhoClock100, Event.time]
  honest_only := by simp [rhoClock100]
  tick_public := by
    intro v t h
    simp only [rhoClock100, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false,
      Event.tick.injEq, true_and, false_or] at h
    rcases h with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [env2]⟩
  tick_total := by
    intro v _ t ht h0 h2 _
    rcases publicTime_env2 ht h0 h2 with rfl | rfl <;> simp [rhoClock100]

/-- `hrestore_now` fails for this `restore`, and the conclusion of
`stateBefore_now_le_event` fails on a well-formed run: before the tick at
index 2 (time 2), the clock is 100. The conclusion of
`stateBefore_now_mono` fails on the restart-free interval `[2, 3)`: the
clock goes from 100 to 2. So `restartFree` does not replace
`hrestore_now`. -/
theorem check_b_restore_now_needed :
    ¬ (∀ d t, clock100.now (specClock100.restore d t) ≤ 0) ∧
      ScheduleWellFormed (env2 _) rhoClock100 ∧
      rhoClock100.events[2]? = some (.tick () 2) ∧
      ¬ clock100.now (Run.stateBefore (env2 _) rhoClock100 2 ()) ≤ 2 ∧
      restartFree rhoClock100 () 2 3 ∧
      clock100.now (Run.stateBefore (env2 _) rhoClock100 3 ()) <
        clock100.now (Run.stateBefore (env2 _) rhoClock100 2 ()) := by
  refine ⟨fun h => absurd (h () 1) (by decide), rhoClock100_wf, rfl, by decide, ?_, by decide⟩
  intro k t hk hk'
  rw [show k = 2 by omega]
  simp [rhoClock100]

/-! ### (c) A restart clears `Q`, and `hrestore_now` holds (DC N1 check) -/

/-- No labels. The state is a clock and a flag; a delivery sets the flag, and
`restore` returns `init`, whose flag is `false`. -/
abbrev specReset : ProtocolSpec Unit where
  State := Time × Bool
  Label := Empty
  seats := fun _ => 0
  Payload := Unit
  Durable := Unit
  init := (0, false)
  clock := fun s t => (t, s.2)
  actTime := fun ℓ => ℓ.elim
  duties := fun _ => []
  duties_spec := fun ℓ => ℓ.elim
  duties_nodup := fun _ => List.nodup_nil
  act := fun _ _ _ => none
  gossip := fun _ _ => []
  process := fun s _ => (s.1, true)
  selfVisible := fun _ => false
  recordOwn := fun s _ => s
  durable := fun _ => ()
  restore := fun _ _ => (0, false)
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-- The clock laws of `specReset`: the clock is the first component. -/
def clockReset : ClockLaws specReset where
  now := Prod.fst
  init := rfl
  clock := fun _ _ => rfl
  process := fun _ _ => rfl
  recordOwn_now := fun _ _ => rfl

/-- A tick at 0, a delivery at 0, a restart at 1, a tick at 2. -/
def rhoReset : Run Unit specReset where
  honest := {()}
  horizon := 2
  events := [.tick () 0, .deliver () ⟨.none, ()⟩ 0, .restart () 1, .tick () 2]
  seatOf := fun ℓ => ℓ.elim
  input := fun _ _ => ()

theorem rhoReset_wf : ScheduleWellFormed (env2 _) rhoReset where
  horizon_nonneg := by decide
  sorted := by simp [rhoReset, Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex]
  nodup := by simp [rhoReset]
  in_horizon := by simp [rhoReset, Event.time]
  honest_only := by simp [rhoReset]
  tick_public := by
    intro v t h
    simp only [rhoReset, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false,
      Event.tick.injEq, true_and, false_or] at h
    rcases h with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp [env2]⟩
  tick_total := by
    intro v _ t ht h0 h2 _
    rcases publicTime_env2 ht h0 h2 with rfl | rfl <;> simp [rhoReset]

/-- With `Q st := st.2 = true`: `hrestore_now`, `hclock`, `hprocess` and
`hrecord` hold, and the run is well-formed. `Q` holds before index 2 and
fails before index 3, after the restart in `[2, 3)`. So
`stateBefore_stable_clock` needs `restartFree`; its restore form needs
`hrestore`, which fails here. -/
theorem check_c_restartFree_needed :
    (∀ d t, clockReset.now (specReset.restore d t) ≤ 0) ∧
      (∀ st t, clockReset.now st ≤ t → st.2 = true → (specReset.clock st t).2 = true) ∧
      (∀ st o, st.2 = true → (specReset.process st o).2 = true) ∧
      (∀ st o, st.2 = true → (specReset.recordOwn st o).2 = true) ∧
      ¬ (∀ st t, st.2 = true → (specReset.restore (specReset.durable st) t).2 = true) ∧
      ScheduleWellFormed (env2 _) rhoReset ∧
      (Run.stateBefore (env2 _) rhoReset 2 ()).2 = true ∧
      (Run.stateBefore (env2 _) rhoReset 3 ()).2 = false ∧
      ¬ restartFree rhoReset () 2 3 :=
  ⟨fun _ _ => le_rfl, fun _ _ _ h => h, fun _ _ _ => rfl, fun _ _ h => h,
    fun h => absurd (h (0, true) 1 rfl) (by decide), rhoReset_wf, rfl, rfl,
    (not_restartFree_succ_iff rhoReset () 2).mpr ⟨1, rfl⟩⟩

/-! ### (d) `restore := fun _ _ => init` discharges the restore premises -/

/-- For FG-SA T7 (`Durable := Unit`, `restore := fun _ _ => init`): `hrestore`
holds for every `Q` with `Q init`, `hrestore_now` holds by
`ClockLaws.init`, and `hrestore_field` holds when `field init = []`. -/
theorem check_d_unit_restore {In : Type} (P : ProtocolSpec In) (C : ClockLaws P)
    (hR : ∀ d t, P.restore d t = P.init) (Q : P.State → Prop) (hQ : Q P.init)
    {α : Type} (field : P.State → List α) (hfield : field P.init = []) :
    (∀ st t, Q st → Q (P.restore (P.durable st) t)) ∧
      (∀ d t, C.now (P.restore d t) ≤ 0) ∧
      (∀ st t x, x ∈ field (P.restore (P.durable st) t) → x ∈ field st) :=
  ⟨fun _ _ _ => by rw [hR]; exact hQ, fun d t => by rw [hR, C.init],
    fun _ _ _ h => by rw [hR, hfield] at h; exact absurd h List.not_mem_nil⟩

/-- The same with the concrete spec `specReset` (`Durable := Unit`,
`restore := fun _ _ => init`): `stateBefore_invariant` applies to
`Q st := 0 ≤ st.1` on every run with a well-formed schedule, restarts
included. -/
theorem check_d_unit_invariant (rho : Run Unit specReset)
    (hs : ScheduleWellFormed (env2 _) rho) (i : Nat) :
    0 ≤ (Run.stateBefore (env2 _) rho i ()).1 :=
  stateBefore_invariant clockReset (fun _ _ => le_rfl) (env2 _) rho hs (fun st => 0 ≤ st.1)
    le_rfl (fun _ _ h hst => le_trans hst h) (fun _ _ h => h) (fun _ _ h => h)
    (fun _ _ _ => le_rfl) i ()

end AvailableChain.V2.Engine.Tests

end

#print axioms AvailableChain.V2.Engine.Tests.rhoClock100_wf
#print axioms AvailableChain.V2.Engine.Tests.check_b_restore_now_needed
#print axioms AvailableChain.V2.Engine.Tests.rhoReset_wf
#print axioms AvailableChain.V2.Engine.Tests.check_c_restartFree_needed
#print axioms AvailableChain.V2.Engine.Tests.check_d_unit_restore
#print axioms AvailableChain.V2.Engine.Tests.check_d_unit_invariant
