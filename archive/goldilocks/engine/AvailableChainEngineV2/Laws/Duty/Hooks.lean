module
public import AvailableChainEngineV2.Conditions.Duty.Schedule

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {In : Type}

structure HooksSound (P : ProtocolSpecD In) : Prop where

  excludes_inert : ∀ st o, P.excludes st o = true → P.process st o = st

  excludes_stable : ∀ {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : Run V P),
    ScheduleWellFormed E rho → ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.excludes (Run.stateBefore E rho i v) o = true →
      P.excludes (Run.stateBefore E rho j v) o = true

  processed_stable : ∀ {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : Run V P),
    ScheduleWellFormed E rho → ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.processed (Run.stateBefore E rho i v) o = true →
      P.processed (Run.stateBefore E rho j v) o = true

  deps_stable : ∀ {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : Run V P),
    ScheduleWellFormed E rho → ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.depsPresent (Run.stateBefore E rho i v) o = true →
      P.depsPresent (Run.stateBefore E rho j v) o = true

  handles_carries : ∀ st o o', P.handles st o o' → o = o' ∨ P.carries o o'

  recordOwn_processed : ∀ st o o', P.processed (P.recordOwn st o) o' = P.processed st o'

  recordOwn_deps : ∀ st o o', P.depsPresent (P.recordOwn st o) o' = P.depsPresent st o'

  recordOwn_excludes : ∀ st o o', P.excludes st o' = true →
    P.excludes (P.recordOwn st o) o' = true

namespace HooksSound

variable {P : ProtocolSpecD In}

theorem foldl_recordOwn_processed (h : HooksSound P) (o' : P.Object) :
    ∀ (l : List P.Object) (s : P.State),
      P.processed (l.foldl P.recordOwn s) o' = P.processed s o' := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      rw [List.foldl_cons, ih, h.recordOwn_processed]

theorem foldl_recordOwn_deps (h : HooksSound P) (o' : P.Object) :
    ∀ (l : List P.Object) (s : P.State),
      P.depsPresent (l.foldl P.recordOwn s) o' = P.depsPresent s o' := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      rw [List.foldl_cons, ih, h.recordOwn_deps]

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

theorem processed_tick (h : HooksSound P) {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) (o : P.Object) :
    P.processed (tick E rho st v t).1 o = P.processed (P.clock st t) o := by
  rw [tick_decomp, h.foldl_recordOwn_processed]

theorem deps_tick (h : HooksSound P) {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) (o : P.Object) :
    P.depsPresent (tick E rho st v t).1 o = P.depsPresent (P.clock st t) o := by
  rw [tick_decomp, h.foldl_recordOwn_deps]

theorem excludes_tick (h : HooksSound P) {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) (o : P.Object)
    (hx : P.excludes (P.clock st t) o = true) :
    P.excludes (tick E rho st v t).1 o = true := by
  rw [tick_decomp]; exact h.foldl_recordOwn_excludes o _ _ hx

end HooksSound

end AvailableChain.V2.D

end
