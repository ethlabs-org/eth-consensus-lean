module
public import AvailableChainEngineV2.Engine.Run

@[expose] public section

/-! Finite checks over a run (plan 2a, Task 6 review M4). A check is a `Bool`
over the event indices, so `decide +kernel` evaluates it on a concrete run;
the `_spec` lemmas turn a passed check into the `Prop` fact at every event.
`allTicks` and `allDeliveries` check every tick event and every delivery
event; `emittedBy` finds a tick of a node at a time at most `t` that releases
an object. The engine-v2 toy (`AvailableChainKitV2/Tests/Toy.lean`) uses
them for `ExecutionValid`, `SelfDelivery` and the delivery conditions. -/

namespace AvailableChain.V2.Engine

open AvailableChain

section

variable {V : Type} {In : Type} {P : ProtocolSpec In}

/-- The check `f` holds at every tick event. -/
def allTicks (rho : Run V P) (f : Nat → V → Time → Bool) : Bool :=
  (List.range rho.events.length).all fun k => match rho.events[k]? with
    | some (.tick v t) => f k v t
    | _ => true

/-- The check `f` holds at every delivery event. -/
def allDeliveries (rho : Run V P) (f : Nat → V → P.Object → Time → Bool) : Bool :=
  (List.range rho.events.length).all fun k => match rho.events[k]? with
    | some (.deliver v o t) => f k v o t
    | _ => true

/-- A passed `allTicks` check holds at every tick event. -/
theorem allTicks_spec {rho : Run V P} {f : Nat → V → Time → Bool} (h : allTicks rho f = true)
    {k : Nat} {v : V} {t : Time} (hk : rho.events[k]? = some (.tick v t)) : f k v t = true := by
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  have := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  simpa only [hk] using this

/-- A passed `allDeliveries` check holds at every delivery event. -/
theorem allDeliveries_spec {rho : Run V P} {f : Nat → V → P.Object → Time → Bool}
    (h : allDeliveries rho f = true) {k : Nat} {v : V} {o : P.Object} {t : Time}
    (hk : rho.events[k]? = some (.deliver v o t)) : f k v o t = true := by
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  have := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  simpa only [hk] using this

variable [DecidableEq V] [DecidableEq P.Object]

/-- Some tick of `u` at a time at most `t` releases `o`. -/
def emittedBy (E : Generic.Env V) (rho : Run V P) (u : V) (o : P.Object) (t : Time) : Bool :=
  (List.range rho.events.length).any fun k => match rho.events[k]? with
    | some (.tick u' t') => decide (u' = u) && decide (t' ≤ t) && decide (o ∈ Run.emitsAt E rho k)
    | _ => false

/-- A passed `emittedBy` check gives an emission at a time at most `t`. -/
theorem emittedBy_spec {E : Generic.Env V} {rho : Run V P} {u : V} {o : P.Object} {t : Time}
    (h : emittedBy E rho u o t = true) : ∃ t', t' ≤ t ∧ Run.emits E rho u o t' := by
  obtain ⟨k, -, hk⟩ := List.any_eq_true.mp h
  revert hk
  cases he : rho.events[k]? with
  | none => simp
  | some e =>
    cases e with
    | tick u' t' =>
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨⟨rfl, ht⟩, ho⟩
      exact ⟨t', ht, k, he, ho⟩
    | restart _ _ => simp
    | deliver _ _ _ => simp

end

end AvailableChain.V2.Engine

end
