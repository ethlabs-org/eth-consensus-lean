module
public import AvailableChainEngineV2.Laws.Isolation
public import AvailableChainKitV2.Execution

@[expose] public section

/-! Stability over engine v2 (plan 2a, Task 4). v1 `stateBefore_stable`
(`AvailableChainKit/Engine/Stable.lean`) needs two more premises on v2: the
tick folds the own record after the clock, so the property must survive
`recordOwn` (Astra A03); and a restart replaces the state, so the interval
must be restart-free (plan 2a D9). -/

namespace AvailableChain.V2.Engine

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- A property that `recordOwn` keeps survives a fold of the own record. -/
theorem foldl_recordOwn_preserve (Q : P.State → Prop)
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o)) :
    ∀ (l : List P.Object) (s : P.State), Q s → Q (l.foldl P.recordOwn s) := by
  intro l
  induction l with
  | nil => intro s hs; exact hs
  | cons o rest ih =>
      intro s hs
      rw [List.foldl_cons]
      exact ih _ (hrecord s o hs)

/-- A property of the post-clock state that `recordOwn` keeps holds after the
tick. -/
theorem tick_preserve (E : Generic.Env V) (rho : Run V P) (Q : P.State → Prop)
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o)) {st : P.State} {v : V} {t : Time}
    (hclock : Q (P.clock st t)) : Q (tick E rho st v t).1 := by
  rw [tick_decomp]
  exact foldl_recordOwn_preserve Q hrecord _ _ hclock

/-- The alternative to the `recordOwn` premise (Astra A03): a property that
factors through the base of an `Isolation` is kept by `recordOwn`. -/
theorem recordOwn_preserve_of_base {F : LabelFamilies P} (iso : Isolation P F)
    (Q : iso.Base → Prop) : ∀ st o, Q (iso.base st) → Q (iso.base (P.recordOwn st o)) := by
  intro st o h
  rwa [iso.recordOwn_base]

/-- Induction along the events at `v` with an index in `[i, j)`. Events of
other nodes do not change the state of `v`; `hstep` handles the events of
`v`, from the state before them. -/
theorem stateBefore_step_induction (E : Generic.Env V) (rho : Run V P)
    (Q : P.State → Prop) {i j : Nat} (hij : i ≤ j) (v : V)
    (hstep : ∀ k e, i ≤ k → k < j → rho.events[k]? = some e → e.node = v →
      Q (Run.stateBefore E rho k v) → Q (World.step E rho (Run.stateBefore E rho k) e v))
    (hi : Q (Run.stateBefore E rho i v)) : Q (Run.stateBefore E rho j v) := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j hij ih =>
      have hj := ih fun k e hik hkj => hstep k e hik (Nat.lt_succ_of_lt hkj)
      cases he : rho.events[j]? with
      | none => simpa [Run.stateBefore, List.take_add_one, he] using hj
      | some e =>
          rw [Run.stateBefore_succ E rho he]
          by_cases hv : e.node = v
          · exact hstep j e hij (Nat.lt_succ_self j) he hv hj
          · rwa [World.step_apply_of_node_ne E rho _ hv]

/-- A state property that `clock`, `process` and `recordOwn` keep holds on a
restart-free interval of the run. The interval must be restart-free: no
premise keeps `Q` through `restore`. -/
theorem stateBefore_stable (Q : P.State → Prop)
    (hclock : ∀ st t, Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrf : restartFree rho v i j)
    (hi : Q (Run.stateBefore E rho i v)) : Q (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q hij v ?_ hi
  intro k e hik hkj he hv hk
  cases e with
  | restart u t =>
      simp only [Event.node] at hv
      subst u
      exact absurd he (hrf k t hik hkj)
  | tick u t =>
      simp only [Event.node] at hv
      subst u
      simpa only [World.step, Function.update_self] using
        tick_preserve E rho Q hrecord (hclock _ t hk)
  | deliver u o t =>
      simp only [Event.node] at hv
      subst u
      simpa only [World.step, Function.update_self] using hprocess _ o hk

/-- A property kept by restore holds across the interval. -/
theorem stateBefore_stable_restore (Q : P.State → Prop)
    (hclock : ∀ st t, Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    (hrecord : ∀ st o, Q st → Q (P.recordOwn st o))
    (E : Generic.Env V) (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V)
    (hrestore : ∀ st t, Q st → Q (P.restore (P.durable st) t))
    (hi : Q (Run.stateBefore E rho i v)) : Q (Run.stateBefore E rho j v) := by
  refine stateBefore_step_induction E rho Q hij v ?_ hi
  intro k e _ _ _ hv hk
  cases e with
  | restart u t =>
      simp only [Event.node] at hv
      subst u
      simpa only [World.step, Function.update_self] using hrestore _ t hk
  | tick u t =>
      simp only [Event.node] at hv
      subst u
      simpa only [World.step, Function.update_self] using
        tick_preserve E rho Q hrecord (hclock _ t hk)
  | deliver u o t =>
      simp only [Event.node] at hv
      subst u
      simpa only [World.step, Function.update_self] using hprocess _ o hk

end AvailableChain.V2.Engine

end
