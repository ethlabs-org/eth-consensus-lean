module
public import AvailableChainEngineV2.Laws.Duty.Isolation
public import AvailableChainEngineV2.Conditions.Duty.Interface

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {In : Type} {P : ProtocolSpecD In} {F : LabelFamilies P}

structure OutputsFactor (I : Interface P) (iso : Isolation P F) where

  confirmedB : iso.Base → Block
  confirmed_base : ∀ st, I.confirmed st = confirmedB (iso.base st)

  stableB : iso.Base → Block
  stable_base : ∀ st, I.stable st = stableB (iso.base st)

namespace OutputsFactor

variable {I : Interface P} {iso : Isolation P F}

theorem confirmed_recordOwn (h : OutputsFactor I iso) (st : P.State) (o : P.Object) :
    I.confirmed (P.recordOwn st o) = I.confirmed st := by
  rw [h.confirmed_base, h.confirmed_base, iso.recordOwn_base]

theorem stable_recordOwn (h : OutputsFactor I iso) (st : P.State) (o : P.Object) :
    I.stable (P.recordOwn st o) = I.stable st := by
  rw [h.stable_base, h.stable_base, iso.recordOwn_base]

theorem confirmed_tick {V : Type} [DecidableEq V] (h : OutputsFactor I iso)
    (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    I.confirmed (tick E rho st v t).1 = I.confirmed (P.clock st t) := by
  rw [h.confirmed_base, h.confirmed_base, iso.base_tick, iso.clock_base]

theorem stable_tick {V : Type} [DecidableEq V] (h : OutputsFactor I iso)
    (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    I.stable (tick E rho st v t).1 = I.stable (P.clock st t) := by
  rw [h.stable_base, h.stable_base, iso.base_tick, iso.clock_base]

end OutputsFactor

end AvailableChain.V2.D

end
