module
public import AvailableChainEngineV2.Engine.Duty.Run

public section

/-! Local clock laws for duty runs. The own-record fold keeps the clock.
Restore premises are supplied by each theorem. -/

namespace AvailableChain.V2.D.Engine

open AvailableChain

variable {In : Type}

/-- Local clock laws. `recordOwn_now`: the own record does not change the
clock. There is no law on `restore`; the lemmas take restore premises. -/
structure ClockLaws (P : ProtocolSpecD In) where
  now : P.State → Time
  init : now P.init = 0
  clock : ∀ st t, now (P.clock st t) = t
  process : ∀ st o, now (P.process st o) = now st
  recordOwn_now : ∀ st o, now (P.recordOwn st o) = now st

structure RestoreTimeLaw {In : Type} {P : ProtocolSpecD In}
    (C : ClockLaws P) : Prop where
  restore_now : ∀ d t, C.now (P.restore d t) = t

namespace ClockLaws

variable {P : ProtocolSpecD In}

/-- A fold of the own record does not change the clock. -/
theorem now_foldl_recordOwn (C : ClockLaws P) :
    ∀ (l : List P.Object) (s : P.State), C.now (l.foldl P.recordOwn s) = C.now s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons o rest ih =>
      intro s
      rw [List.foldl_cons, ih, C.recordOwn_now]

/-- After a tick at time `t`, the clock is `t`. -/
theorem now_tick (C : ClockLaws P) {V : Type} [DecidableEq V] (E : Generic.Env V)
    (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    C.now (tick E rho st v t).1 = t := by
  rw [tick_decomp, C.now_foldl_recordOwn, C.clock]

end ClockLaws

end AvailableChain.V2.D.Engine

end
