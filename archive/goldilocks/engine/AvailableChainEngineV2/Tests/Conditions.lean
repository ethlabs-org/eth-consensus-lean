module
public import AvailableChainEngineV2.Conditions.Schedule
public import AvailableChainEngineV2.Conditions.Committees
public import AvailableChainEngineV2.Tests.Engine

@[expose] public section

/-! Tests of the conditions without blocks (plan 2a, Task 2): a restart of
another node does not break `restartFree`; a `Linked` family is `CStar`; a
seat map that is not bijective is not `CStar`; a one-seat family is
`SingleSeat`; a run with and a run without the self-delivery of a
self-visible object. -/

namespace AvailableChain.V2.Tests

open AvailableChain AvailableChain.V2

/-- Validator 1 restarts at time 0, then validator 0 ticks at time 0. -/
def rhoR : Run (Fin 2) specA where
  honest := ∅
  horizon := 0
  events := [.restart 1 0, .tick 0 0]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

-- The restart of validator 1 does not count for validator 0.
example : restartFree rhoR 0 0 1 := by
  by_contra h
  obtain ⟨t, ht⟩ := (not_restartFree_succ_iff rhoR 0 0).mp h
  simp [rhoR] at ht
-- It counts for validator 1 on `[0, 1)`, but not on `[1, 2)`.
example : ¬ restartFree rhoR 1 0 1 := (not_restartFree_succ_iff rhoR 1 0).mpr ⟨0, rfl⟩
example : restartFree rhoR 1 1 2 := by
  by_contra h
  obtain ⟨t, ht⟩ := (not_restartFree_succ_iff rhoR 1 1).mp h
  simp [rhoR] at ht
example : ¬ NoRestart rhoR := fun h => h 0 1 0 rfl

/-- `specM`: label `true` has two seats, label `false` one. Seat `i` of any
label is validator `i mod 2`. -/
def rhoL : Run (Fin 2) specM where
  honest := ∅
  horizon := 0
  events := []
  seatOf := fun _ i => ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  input := fun _ _ => 0

/-- The family `{true}` is linked through the identity bijection. -/
theorem rhoL_linked : Linked (fun ℓ => ℓ = true) rhoL := by
  refine ⟨2, Equiv.refl _, fun ℓ hℓ => ?_⟩
  subst hℓ
  exact ⟨rfl, fun i => Fin.ext (Nat.mod_eq_of_lt i.isLt)⟩

example : CStar (fun ℓ => ℓ = true) rhoL := rhoL_linked.toCStar
example : SingleSeat specM (fun ℓ => ℓ = false) := by
  rintro ℓ rfl; rfl

-- In `rhoR`, validator 0 holds every seat, so no seat map reaches validator 1.
example : ¬ CStar (fun _ => True) rhoR := by
  intro h
  obtain ⟨i, hi⟩ := (h true trivial).2 1
  exact absurd hi (by simp [rhoR])

/-! ### `SelfDelivery` -/

/-- The own object of `rhoSD` and `rhoNoSD`: label `true` of `specA` is due at
time 1 and self-visible; validator 0 signs its state 0 with seat 0. -/
def oSD : specA.Object := ⟨.seat true 0, 0⟩

/-- Validator 0 ticks at time 1, and then gets its own object at time 1. -/
def rhoSD : Run (Fin 2) specA where
  honest := {0}
  horizon := 1
  events := [.tick 0 1, .deliver 0 oSD 1]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- Validator 0 ticks at time 1, and nothing more. -/
def rhoNoSD : Run (Fin 2) specA := { rhoSD with events := [.tick 0 1] }

example : Run.emitsAt (envAwake _) rhoSD 0 = [oSD] := rfl
example : specA.objSelfVisible oSD = true := rfl

example : SelfDelivery (envAwake _) rhoSD := by
  intro i v t h o ho _
  match i, h with
  | 0, h =>
    simp only [rhoSD, List.getElem?_cons_zero, Option.some.injEq, Event.tick.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [show Run.emitsAt (envAwake _) rhoSD 0 = [oSD] from rfl, List.mem_singleton] at ho
    exact ⟨1, Nat.zero_lt_one, by rw [ho]; rfl⟩
  | 1, h =>
    simp only [rhoSD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      reduceCtorEq] at h
  | _ + 2, h => simp only [rhoSD, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at h

example : ¬ SelfDelivery (envAwake _) rhoNoSD := by
  intro h
  obtain ⟨j, hj, hjd⟩ := h 0 0 1 rfl oSD (List.mem_singleton_self _) rfl
  match j, hj, hjd with
  | _ + 1, _, hjd =>
    simp only [rhoNoSD, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hjd

end AvailableChain.V2.Tests

end
