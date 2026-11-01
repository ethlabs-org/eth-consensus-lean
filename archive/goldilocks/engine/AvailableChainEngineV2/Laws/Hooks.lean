module
public import AvailableChainEngineV2.Conditions.Schedule

@[expose] public section

/-! Hook obligations over v2 runs (design §2 E4; plan 2a, Task 3). The fields
are those of v1 `HooksSound` (`AvailableChainFramework/Hooks.lean`), with
stability on restart-free intervals, and three laws for the own record. -/

namespace AvailableChain.V2

open AvailableChain

variable {In : Type}

/-- E4 obligations on the v2 engine (plan 2a D7). The hooks stay run-level:
stability is stated along runs, because `clock` can move back in time on
states that no run reaches. A restart starts a new epoch of the node, so
stability holds on the restart-free intervals of all runs (`restartFree`),
and `HooksSound` puts no law on a restart (the E6 laws are plan 2c).

The tick is atomic, so the run-level fields do not see the states inside the
own-record fold. The three `recordOwn` laws cover them: the own record does
not change `processed` or `depsPresent`, and it keeps `excludes`.

The run fields quantify over every validator type with decidable equality;
v1 also asked for `Fintype V`, which v2 runs do not need. -/
structure HooksSound (P : ProtocolSpec In) : Prop where
  /-- An excluded object does not change the state. -/
  excludes_inert : ∀ st o, P.excludes st o = true → P.process st o = st
  /-- Exclusion is stable on a restart-free interval of a run. -/
  excludes_stable : ∀ {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : Run V P),
    ScheduleWellFormed E rho → ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.excludes (Run.stateBefore E rho i v) o = true →
      P.excludes (Run.stateBefore E rho j v) o = true
  /-- `processed` is monotone on a restart-free interval of a run. -/
  processed_stable : ∀ {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : Run V P),
    ScheduleWellFormed E rho → ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.processed (Run.stateBefore E rho i v) o = true →
      P.processed (Run.stateBefore E rho j v) o = true
  /-- `depsPresent` is monotone on a restart-free interval of a run. -/
  deps_stable : ∀ {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : Run V P),
    ScheduleWellFormed E rho → ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.depsPresent (Run.stateBefore E rho i v) o = true →
      P.depsPresent (Run.stateBefore E rho j v) o = true
  /-- A handled object is the delivered object or one that it carries. -/
  handles_carries : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o'
  /-- The own record does not change `processed`. -/
  recordOwn_processed : ∀ st o o', P.processed (P.recordOwn st o) o' = P.processed st o'
  /-- The own record does not change `depsPresent`. -/
  recordOwn_deps : ∀ st o o', P.depsPresent (P.recordOwn st o) o' = P.depsPresent st o'
  /-- The own record keeps an exclusion. -/
  recordOwn_excludes : ∀ st o o', P.excludes st o' = true →
    P.excludes (P.recordOwn st o) o' = true

namespace HooksSound

variable {P : ProtocolSpec In}

/-- A fold of the own record does not change `processed`. -/
theorem foldl_recordOwn_processed (h : HooksSound P) (o' : P.Object) :
    ∀ (l : List P.Object) (s : P.State),
      P.processed (l.foldl P.recordOwn s) o' = P.processed s o' := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      rw [List.foldl_cons, ih, h.recordOwn_processed]

/-- A fold of the own record does not change `depsPresent`. -/
theorem foldl_recordOwn_deps (h : HooksSound P) (o' : P.Object) :
    ∀ (l : List P.Object) (s : P.State),
      P.depsPresent (l.foldl P.recordOwn s) o' = P.depsPresent s o' := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      rw [List.foldl_cons, ih, h.recordOwn_deps]

/-- A fold of the own record keeps an exclusion. -/
theorem foldl_recordOwn_excludes (h : HooksSound P) (o' : P.Object) :
    ∀ (l : List P.Object) (s : P.State), P.excludes s o' = true →
      P.excludes (l.foldl P.recordOwn s) o' = true := by
  intro l
  induction l with
  | nil => intro s hs; exact hs
  | cons o rest ih =>
      intro s hs
      rw [List.foldl_cons]
      exact ih _ (h.recordOwn_excludes s o o' hs)

/-- After a tick, `processed` is its value in the post-clock state. -/
theorem processed_tick (h : HooksSound P) {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) (o : P.Object) :
    P.processed (tick E rho st v t).1 o = P.processed (P.clock st t) o := by
  rw [tick_decomp, h.foldl_recordOwn_processed]

/-- After a tick, `depsPresent` is its value in the post-clock state. -/
theorem deps_tick (h : HooksSound P) {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) (o : P.Object) :
    P.depsPresent (tick E rho st v t).1 o = P.depsPresent (P.clock st t) o := by
  rw [tick_decomp, h.foldl_recordOwn_deps]

/-- A tick keeps an exclusion of the post-clock state. -/
theorem excludes_tick (h : HooksSound P) {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) (o : P.Object)
    (hx : P.excludes (P.clock st t) o = true) :
    P.excludes (tick E rho st v t).1 o = true := by
  rw [tick_decomp]; exact h.foldl_recordOwn_excludes o _ _ hx

end HooksSound

end AvailableChain.V2

end
