module
public import AvailableChainEngineV2.Laws.Isolation
public import AvailableChainEngineV2.Laws.SelfDelivery
public import AvailableChainEngineV2.Tests.Conditions

@[expose] public section

/-! Tests of the laws without blocks (plan 2a, Task 3). Separation (Review
Focus 3): a spec with a self-visible AP label, or a self-visible fresh label,
has no `Isolation` value; a self-visible linked label is allowed. The hook
projection covers unsigned objects, and it fails for a hook that reads the
own record (on an AP object and on an unsigned object). A one-seat
label in a `CStar` family forces one validator. `HooksSound` holds for
`specA`, and `ExecutionValid.snoc_selfDelivery` appends a self-delivery to a
valid run of `specA`. -/

namespace AvailableChain.V2.Tests

open AvailableChain AvailableChain.V2

/-! ### Separation (Review Focus 3) -/

/-- Every label of `specA` in `ap`. Label `true` is self-visible. -/
def famAllAP : LabelFamilies specA := ⟨fun _ => True, fun _ => False, fun _ => False⟩
/-- Every label of `specA` in `fresh`. -/
def famAllFresh : LabelFamilies specA := ⟨fun _ => False, fun _ => True, fun _ => False⟩
/-- Every label of `specA` in `linked`. -/
def famAllLinked : LabelFamilies specA := ⟨fun _ => False, fun _ => False, fun _ => True⟩

-- A self-visible AP label: no `Isolation` value.
example : IsEmpty (Isolation specA famAllAP) :=
  ⟨fun iso => absurd (iso.separation true (Or.inl trivial)) (by decide)⟩
-- A self-visible fresh label: no `Isolation` value.
example : IsEmpty (Isolation specA famAllFresh) :=
  ⟨fun iso => absurd (iso.separation true (Or.inr trivial)) (by decide)⟩

/-- A self-visible linked label is allowed. The base is trivial: no label is
an AP label, and the hooks of `specA` are constant, so they factor on the
unsigned objects too. -/
def isoLinked : Isolation specA famAllLinked where
  Base := Unit
  base := fun _ => ()
  clockB := fun _ _ => ()
  clock_base := fun _ _ => rfl
  processB := fun _ _ => ()
  process_base := fun _ _ => rfl
  recordOwn_base := fun _ _ => rfl
  actB := fun _ _ _ => none
  act_base := fun _ _ _ h => h.elim
  gossipB := fun _ _ => []
  gossip_base := fun _ _ => rfl
  depsB := fun _ _ => true
  processedB := fun _ _ => false
  excludesB := fun _ _ => false
  handlesB := fun _ o o' => o = o'
  hooks_base := fun _ _ _ => ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩
  separation := fun _ h => h.elim (fun h => h.elim) (fun h => h.elim)

-- An unsigned object is an object of the AP projection, so `hooks_base`
-- covers it, and the factors of `isoLinked` compute by `rfl`.
example : famAllLinked.APObject (⟨.none, 3⟩ : specA.Object) := trivial
example (st : Nat) : specA.processed st ⟨.none, 3⟩ =
    isoLinked.processedB (isoLinked.base st) ⟨.none, 3⟩ :=
  (isoLinked.hooks_base st ⟨.none, 3⟩ trivial).2.1
example : isoLinked.processedB () ⟨.none, 3⟩ = false := rfl
-- A signed object of a linked label is not.
example : ¬ famAllLinked.APObject (⟨.seat true 0, 3⟩ : specA.Object) := id

/-- `specB` (no self-visible label) with its one label in `ap` and `fresh`.
The base is the whole state. -/
def isoB : Isolation specB ⟨fun _ => True, fun _ => True, fun _ => False⟩ where
  Base := Nat
  base := id
  clockB := fun b _ => b
  clock_base := fun _ _ => rfl
  processB := fun _ o => o.payload
  process_base := fun _ _ => rfl
  recordOwn_base := fun _ _ => rfl
  actB := fun b _ _ => some b
  act_base := fun _ _ _ _ => rfl
  gossipB := fun _ _ => []
  gossip_base := fun _ _ => rfl
  depsB := fun _ _ => true
  processedB := fun _ _ => false
  excludesB := fun _ _ => false
  handlesB := fun _ o o' => o = o'
  hooks_base := fun _ _ _ => ⟨rfl, rfl, rfl, fun _ _ => Iff.rfl⟩
  separation := fun _ _ => rfl

-- `base_tick` for `isoB`: the tick of `rhoB` at time 5 keeps the base.
example (st : Nat) : isoB.base (tick (envAwake _) rhoB st () 5).1 = st :=
  isoB.base_tick _ _ _ _ _

/-! ### `hooks_base` can fail -/

/-- One label, not self-visible, due at time 5. The state is a flag. The own
record sets the flag, and `processed` reads it for every object. -/
abbrev specF : ProtocolSpec Unit where
  State := Bool
  Label := Unit
  seats := fun _ => 1
  Payload := Nat
  Durable := Unit
  init := false
  clock := fun s _ => s
  actTime := fun _ => 5
  duties := dutiesB
  duties_spec := specB.duties_spec
  duties_nodup := specB.duties_nodup
  act := fun _ _ _ => none
  gossip := fun _ _ => []
  process := fun s _ => s
  selfVisible := fun _ => false
  recordOwn := fun _ _ => true
  durable := fun _ => ()
  restore := fun _ _ => false
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun s _ => s
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

/-- `recordOwn_base` makes the base forget the flag, so a hook of an object of
the AP projection that reads the flag does not factor through the base. -/
theorem specF_not_isolated (F : LabelFamilies specF) (o : specF.Object)
    (ho : F.APObject o) : IsEmpty (Isolation specF F) :=
  ⟨fun iso => by
    have h : iso.base true = iso.base false := iso.recordOwn_base false o
    have hp := (iso.hooks_congr h ho).2.1
    exact Bool.noConfusion hp⟩

-- With the label in `ap`: an AP object reads the flag.
example : IsEmpty (Isolation specF ⟨fun _ => True, fun _ => False, fun _ => False⟩) :=
  specF_not_isolated _ ⟨.seat () 0, 0⟩ trivial
-- With no AP label: an unsigned object reads the flag (the widened law).
example : IsEmpty (Isolation specF ⟨fun _ => False, fun _ => False, fun _ => True⟩) :=
  specF_not_isolated _ ⟨.none, 0⟩ trivial

-- DC N9: a one-seat label in a `CStar` family forces one validator.
example {V : Type} [Fintype V] {In : Type} {P : ProtocolSpec In} {F : P.Label → Prop}
    {rho : Run V P} (h : CStar F rho) {ℓ : P.Label} (hℓ : F ℓ) (h1 : P.seats ℓ = 1) :
    Fintype.card V = 1 :=
  (CStar.seats_eq h hℓ).symm.trans h1

/-! ### Hooks and the append form -/

/-- `specA` satisfies the hook obligations: `processed`, `depsPresent` and
`excludes` are constant, and a node handles only the delivered object. -/
theorem hooksA : HooksSound specA where
  excludes_inert := fun _ _ h => absurd h Bool.false_ne_true
  excludes_stable := fun _ _ _ _ _ _ _ _ _ h => h
  processed_stable := fun _ _ _ _ _ _ _ _ _ h => h
  deps_stable := fun _ _ _ _ _ _ _ _ _ h => h
  handles_carries := fun _ _ _ h => Or.inl h
  recordOwn_processed := fun _ _ _ => rfl
  recordOwn_deps := fun _ _ _ => rfl
  recordOwn_excludes := fun _ _ _ h => h

/-- Validator 0 is honest and ticks at times 0 and 1 (every public time up to
the horizon 1). -/
def rhoV : Run (Fin 2) specA where
  honest := {0}
  horizon := 1
  events := [.tick 0 0, .tick 0 1]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

example : Run.emitsAt (envAwake _) rhoV 1 = [oSD] := rfl

theorem rhoV_valid : ExecutionValid (envAwake _) rhoV := by
  refine { toScheduleWellFormed := ?_, toDeliveryWellFormed := ?_,
           toUnforgeableSignatures := ?_,
           toSleepWellFormed := ⟨by intros; rfl, by intros; rfl, by intros; rfl,
             by simp [Wakes, envAwake]⟩ }
  · refine ⟨by decide, ?_, by decide, ?_, ?_, ?_, ?_⟩
    · simp [rhoV, Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex]
    · simp [rhoV, Event.time]
    · simp [rhoV, Event.node]
    · intro v t h
      simp only [rhoV, List.mem_cons, Event.tick.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨0, by simp [envAwake]⟩
      · exact ⟨1, by simp [envAwake]⟩
    · intro v hv t ⟨k, hk⟩ h0 h1 _ha
      simp only [rhoV, Finset.mem_singleton] at hv
      subst hv
      simp only [envAwake, mul_one] at hk
      subst hk
      have h1' : (k : Int) ≤ 1 := h1
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl <;> simp [rhoV]
  · refine ⟨?_, ?_, ?_⟩ <;> intro i v o t h <;>
      match i, h with
      | 0, h => simp only [rhoV, List.getElem?_cons_zero, Option.some.injEq, reduceCtorEq] at h
      | 1, h =>
        simp only [rhoV, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          reduceCtorEq] at h
      | _ + 2, h =>
        simp only [rhoV, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at h
  · refine ⟨?_, ?_⟩ <;> rintro v o t ⟨i, h⟩ <;>
      match i, h with
      | 0, h => simp only [rhoV, List.getElem?_cons_zero, Option.some.injEq, reduceCtorEq] at h
      | 1, h =>
        simp only [rhoV, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          reduceCtorEq] at h
      | _ + 2, h =>
        simp only [rhoV, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at h

/-- The tick at index 1 releases `oSD` with `EmitOk`. -/
theorem rhoV_emitOk :
    EmitOk (envAwake _) rhoV (Run.stateBefore (envAwake _) rhoV 1 0) 0 1 oSD :=
  ⟨rfl, rfl, rfl, fun _ h => h⟩

/-- `rhoV` with the self-delivery of `oSD` to validator 0 at time 1. -/
def rhoVSD : Run (Fin 2) specA := { rhoV with events := rhoV.events ++ [.deliver 0 oSD 1] }

-- The append form: `rhoVSD` is valid.
example : ExecutionValid (envAwake _) rhoVSD :=
  rhoV_valid.snoc_selfDelivery hooksA
    (by simp [rhoV, Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex])
    (i := 1) rfl
    (fun k e hk he => by
      match k, hk, he with
      | _ + 2, _, he =>
        simp only [rhoV, List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at he)
    (by rw [show Run.emitsAt (envAwake _) rhoV 1 = [oSD] from rfl]; exact List.mem_singleton_self _)
    rhoV_emitOk

-- `selfDelivery_admissible` at the appended delivery (index 2 of `rhoVSD`): its
-- hypotheses hold, and the delivery is fresh.
example : specA.processed (Run.stateBefore (envAwake _) rhoVSD 2 0) oSD = false :=
  (selfDelivery_admissible hooksA (i := 1) (j := 2) rfl
    (by rw [show Run.emitsAt (envAwake _) rhoVSD 1 = [oSD] from rfl]
        exact List.mem_singleton_self _)
    ⟨rfl, rfl, rfl, fun _ h => h⟩ rfl).2.2.1

end AvailableChain.V2.Tests

end

#print axioms AvailableChain.V2.Tests.rhoV_valid
