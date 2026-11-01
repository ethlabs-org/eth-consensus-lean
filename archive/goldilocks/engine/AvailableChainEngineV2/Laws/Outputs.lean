module
public import AvailableChainEngineV2.Laws.Isolation
public import AvailableChainEngineV2.Conditions.Interface

@[expose] public section

/-! Output isolation (design §2 E5; plan 2a, Task 5). The law shape is the
`output_base` field and `output_tick` of the pre-2a prototype `Sketch.lean`
(deleted at the 2a gate; see git history), for the two outputs of an
`Interface`. `Isolation` alone does not make the outputs isolated; an
instance must also give an `OutputsFactor` value. -/

namespace AvailableChain.V2

open AvailableChain

variable {In : Type} {P : ProtocolSpec In} {F : LabelFamilies P}

/-- Every output getter of `I` factors through `iso.base`. The factors are
data, like the factors of `Isolation`; with `base := id` the factors are the
getters and the laws hold by `rfl`. -/
structure OutputsFactor (I : Interface P) (iso : Isolation P F) where
  /-- The factor of `confirmed` on `Base`. -/
  confirmedB : iso.Base → Block
  confirmed_base : ∀ st, I.confirmed st = confirmedB (iso.base st)
  /-- The factor of `stable` on `Base`. -/
  stableB : iso.Base → Block
  stable_base : ∀ st, I.stable st = stableB (iso.base st)

namespace OutputsFactor

variable {I : Interface P} {iso : Isolation P F}

/-- The own record does not change `confirmed`. -/
theorem confirmed_recordOwn (h : OutputsFactor I iso) (st : P.State) (o : P.Object) :
    I.confirmed (P.recordOwn st o) = I.confirmed st := by
  rw [h.confirmed_base, h.confirmed_base, iso.recordOwn_base]

/-- The own record does not change `stable`. -/
theorem stable_recordOwn (h : OutputsFactor I iso) (st : P.State) (o : P.Object) :
    I.stable (P.recordOwn st o) = I.stable st := by
  rw [h.stable_base, h.stable_base, iso.recordOwn_base]

/-- After a tick, `confirmed` is that of the post-clock state: the own record
does not change it (the pre-2a prototype `Sketch.lean` (deleted at the 2a
gate; see git history), `output_tick`). -/
theorem confirmed_tick {V : Type} [DecidableEq V] (h : OutputsFactor I iso)
    (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    I.confirmed (tick E rho st v t).1 = I.confirmed (P.clock st t) := by
  rw [h.confirmed_base, h.confirmed_base, iso.base_tick, iso.clock_base]

/-- After a tick, `stable` is that of the post-clock state. -/
theorem stable_tick {V : Type} [DecidableEq V] (h : OutputsFactor I iso)
    (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V) (t : Time) :
    I.stable (tick E rho st v t).1 = I.stable (P.clock st t) := by
  rw [h.stable_base, h.stable_base, iso.base_tick, iso.clock_base]

end OutputsFactor

end AvailableChain.V2

end
