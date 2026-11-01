module
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures
public import AvailableChainGeneric.Proofs.V2.Duty.Linked -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Counts
public import AvailableChainGeneric.Statements.V2.Duty.Counts
public import AvailableChainGeneric.Statements.V2.Reads -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Duty.Reads -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Receipt -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Duty.Receipt -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Regimes -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Duty.Regimes -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Interface -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Duty.Interface -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Slashing
public import AvailableChainGeneric.Statements.V2.Duty.Slashing
public import AvailableChainGeneric.Statements.V2.Linked -- shake: keep (axioms)
public import AvailableChainGeneric.Statements.V2.Duty.LinkedHolders -- shake: keep (axioms)
public import AvailableChainGeneric.Proofs.V2.Reads
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import AvailableChainGeneric.Proofs.V2.Receipt
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt
public import AvailableChainGeneric.Proofs.V2.Regimes -- shake: keep (axioms)
public import AvailableChainGeneric.Proofs.V2.Duty.Regimes -- shake: keep (axioms)
public import AvailableChainGeneric.Proofs.V2.Fields
public import AvailableChainGeneric.Proofs.V2.Duty.Fields
public import AvailableChainGeneric.Proofs.V2.Induction
public import AvailableChainGeneric.Proofs.V2.Duty.Induction
public import AvailableChainGeneric.Proofs.V2.BaseTransport
public import AvailableChainGeneric.Proofs.V2.Duty.BaseTransport
public import AvailableChainGeneric.Proofs.V2.Linked
public import AvailableChainGeneric.Proofs.V2.Duty.LinkedHolders

@[expose] public section

open AvailableChain AvailableChain.V2

namespace AvailableChain.Gen.V2.Duty.Tests

/-- Two FG duties at times 0 and 1 use the same signing label and seat. -/
abbrev toy : ProtocolSpecD Unit where
  State := List Bool
  Label := Unit
  Duty := Bool
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Bool
  Durable := List Bool
  init := []
  clock := fun st _ => st
  actTime := fun d => if d then 1 else 0
  duties := fun t => if t = 0 then [false] else if t = 1 then [true] else []
  duties_spec := by
    intro d t
    cases d <;> split_ifs <;> simp_all [eq_comm]
  duties_nodup := by intro t; split_ifs <;> simp
  act := fun st d _ => if d ∈ st then none else some d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st o => o.payload :: st
  durable := id
  restore := fun d _ => d
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

abbrev env : Generic.Env (Fin 1) := ⟨1, by decide, 0, by decide, fun _ _ => true⟩

abbrev run : D.Run (Fin 1) toy where
  honest := {0}
  horizon := 1
  events := [.tick 0 0, .tick 0 1]
  seatOf := fun _ i => i
  input := fun _ _ => ()

theorem no_single_duty : ¬ SingleDuty toy () := by
  rintro ⟨d, _, h⟩
  have hf := h false rfl
  have ht := h true rfl
  exact Bool.false_ne_true (hf.trans ht.symm)

theorem send_once : EmitOnceUnder env run () := by
  intro i _ p j k t u hj hk hp hq
  have hjlt : j < 2 := (List.getElem?_eq_some_iff.mp hj).1
  have hklt : k < 2 := (List.getElem?_eq_some_iff.mp hk).1
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have emitted : D.Run.emitsAt env run 0 = [⟨.seat () 0, false⟩] ∧
      D.Run.emitsAt env run 1 = [⟨.seat () 0, true⟩] := by decide
  have hjcases : j = 0 ∨ j = 1 := by omega
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hjcases with rfl | rfl <;> rcases hkcases with rfl | rfl
  · rfl
  · simp only [emitted.1, List.mem_singleton, Signed.mk.injEq, true_and] at hp
    simp only [emitted.2, List.mem_singleton, Signed.mk.injEq, true_and] at hq
    exact (Bool.false_ne_true (hp.symm.trans hq)).elim
  · simp only [emitted.2, List.mem_singleton, Signed.mk.injEq, true_and] at hp
    simp only [emitted.1, List.mem_singleton, Signed.mk.injEq, true_and] at hq
    exact (Bool.false_ne_true (hq.symm.trans hp)).elim
  · rfl

theorem uniqueness_consumer (p : Bool) (j k : Nat) (t u : Time)
    (hj : run.events[j]? = some (.tick 0 t)) (hk : run.events[k]? = some (.tick 0 u))
    (hp : (⟨.seat () 0, p⟩ : toy.Object) ∈ D.Run.emitsAt env run j)
    (hq : (⟨.seat () 0, p⟩ : toy.Object) ∈ D.Run.emitsAt env run k) :
    j = k ∧ t = u :=
  emit_unique_of_emitOnce env run () send_once 0 (by simp) p j k t u hj hk hp hq

/-- This protocol repeats one content, so the send-once premise is false. -/
abbrev repeats : ProtocolSpecD Unit := { toy with act := fun _ _ _ => some false }

abbrev repeatRun : D.Run (Fin 1) repeats where
  honest := {0}
  horizon := 1
  events := [.tick 0 0, .tick 0 1]
  seatOf := fun _ i => i
  input := fun _ _ => ()

theorem repeat_rejected : ¬ EmitOnceUnder env repeatRun () := by
  intro h
  have heq := h 0 (by simp) false 0 1 0 1 rfl rfl (by decide) (by decide)
  exact (by decide : (0 : Nat) ≠ 1) heq

end AvailableChain.Gen.V2.Duty.Tests

#print axioms AvailableChain.Gen.V2.Duty.Tests.no_single_duty
#print axioms AvailableChain.Gen.V2.Duty.Tests.send_once
#print axioms AvailableChain.Gen.V2.Duty.Tests.uniqueness_consumer
#print axioms AvailableChain.Gen.V2.Duty.Tests.repeat_rejected

namespace AvailableChain.Gen.V2.Duty.Tests.Lift

variable {In V : Type} [DecidableEq V] {P : ProtocolSpec In}

abbrev clockLift (C : V2.Engine.ClockLaws P) : D.Engine.ClockLaws P.toD :=
  ⟨C.now, C.init, C.clock, C.process, C.recordOwn_now⟩

abbrev timelyLift {T : P.State → P.Object → Prop} (C : Gen.V2.TimelyClock P T) :
    Duty.TimelyClock P.toD T :=
  ⟨C.actTime, C.clockOf, C.timely_iff, clockLift C.clock, C.clockOf_eq⟩

abbrev finalityLift (I : Gen.V2.FinalityInterface P) : Duty.FinalityInterface P.toD :=
  { I.toInterface.toD with finalized := I.finalized }

abbrev slashingLift (I : Gen.V2.SlashingInterface (V := V) P) :
    Duty.SlashingInterface (V := V) P.toD :=
  { finalityLift I.toFinalityInterface with slashes := fun rho => I.slashes rho.ofD }

/-- Compare the complete proposition, including each premise. -/
def statementOf {p : Prop} (_ : p) : Prop := p

variable (E : Generic.Env V) (rho : V2.Run V P)

omit [DecidableEq V] in
theorem finality_roundtrip (I : Gen.V2.FinalityInterface P) :
    ({ (finalityLift I).toInterface.ofD with finalized := (finalityLift I).finalized } :
      Gen.V2.FinalityInterface P) = I := rfl

omit [DecidableEq V] in
theorem timely_roundtrip {T : P.State → P.Object → Prop} (C : Gen.V2.TimelyClock P T) :
    (⟨(timelyLift C).actTime, (timelyLift C).clockOf, (timelyLift C).timely_iff,
      ⟨(timelyLift C).clock.now, (timelyLift C).clock.init, (timelyLift C).clock.clock,
        (timelyLift C).clock.process, (timelyLift C).clock.recordOwn_now⟩,
      (timelyLift C).clockOf_eq⟩ : Gen.V2.TimelyClock P T) = C := rfl

theorem faulty_agrees [Fintype V] : Duty.faulty rho.toD = Gen.V2.faulty rho := rfl

omit [DecidableEq V] in
theorem awakeHonest_agrees (t : Time) :
    Duty.awakeHonest E rho.toD t = Gen.V2.awakeHonest E rho t := rfl

omit [DecidableEq V] in
theorem idxBefore_agrees (t : Time) : D.Run.idxBefore rho.toD t = V2.Run.idxBefore rho t := rfl

theorem nthIdx_agrees (v : V) (k : Nat) :
    D.Run.nthIdx? rho.toD v k = V2.Run.nthIdx? rho v k := rfl

omit [DecidableEq V] in
theorem pubFloor_agrees (t : Time) : Duty.pubFloor E t = Gen.V2.pubFloor E t := rfl

omit [DecidableEq V] in
theorem honestSlot_agrees (I : V2.Interface P) (s : Slot) :
    Duty.HonestSlot rho.toD I.toD s ↔ Gen.V2.HonestSlot rho I s := Iff.rfl

theorem holdsBefore_agrees (Q : P.State → Prop) (t : Time) (v : V) :
    Duty.HoldsBefore E rho.toD Q t v ↔ Gen.V2.HoldsBefore E rho Q t v := by
  simp only [Duty.HoldsBefore_def, Gen.V2.HoldsBefore_def, D.stateBeforeTime_toD]

omit [DecidableEq V] in
theorem monoAlong_agrees (Q : P.State → Prop) :
    Duty.MonoAlong (P := P.toD) Q ↔ Gen.V2.MonoAlong (P := P) Q := Iff.rfl

omit [DecidableEq V] in
theorem pending_agrees (t : Time) (served : Nat → Prop) (i : Nat) :
    Duty.Pending rho.toD t served i ↔ Gen.V2.Pending rho t served i := Iff.rfl

theorem trigger_agrees (o : P.Object) (t : Time) :
    Duty.Trigger E rho.toD o t ↔ Gen.V2.Trigger E rho o t := by
  simp only [Duty.Trigger_def, Gen.V2.Trigger_def, D.emits_toD, D.acceptsAt_toD]

theorem deliveryWithin_agrees (dl : Time → Time) (cut : Time) :
    Duty.DeliveryWithin E rho.toD dl cut ↔ Gen.V2.DeliveryWithin E rho dl cut := by
  constructor <;> intro h
  · exact ⟨by simpa only [D.emits_toD, D.deliveryDemand_toD_iff] using h.broadcast,
      by simpa only [D.acceptsAt_toD, D.deliveryDemand_toD_iff] using h.relay⟩
  · exact ⟨by simpa only [D.emits_toD, D.deliveryDemand_toD_iff] using h.broadcast,
      by simpa only [D.acceptsAt_toD, D.deliveryDemand_toD_iff] using h.relay⟩

omit [DecidableEq V] in
theorem acceptanceLaw_agrees (T : P.State → P.Object → Prop) (Inv : P.State → Prop) :
    Duty.AcceptanceLaw P.toD T Inv ↔ Gen.V2.AcceptanceLaw P T Inv :=
  ⟨fun h => ⟨h.accepts⟩, fun h => ⟨h.accepts⟩⟩

omit [DecidableEq V] in
theorem admitSound_agrees {T : P.State → P.Object → Prop} (C : Gen.V2.TimelyClock P T) :
    Duty.AdmitSound P.toD (timelyLift C) ↔ Gen.V2.AdmitSound P C :=
  ⟨fun h => ⟨h.timely⟩, fun h => ⟨h.timely⟩⟩

theorem labelSync_agrees (vt dt : Time) :
    Duty.LabelSync E rho.toD vt dt ↔ Gen.V2.LabelSync E rho vt dt := by
  simp only [Duty.LabelSync_def, Gen.V2.LabelSync_def, deliveryWithin_agrees]

theorem labelFacts_agrees (vt dt : Time) (h m : Nat) :
    Duty.LabelFacts E rho.toD vt dt h m ↔ Gen.V2.LabelFacts E rho vt dt h m :=
  ⟨fun x => ⟨(labelSync_agrees E rho vt dt).mp x.sync, x.batch⟩,
    fun x => ⟨(labelSync_agrees E rho vt dt).mpr x.sync, x.batch⟩⟩

theorem baseCore_agrees : Duty.BaseCore E rho.toD ↔ Gen.V2.BaseCore E rho :=
  ⟨fun h => ⟨(D.executionValid_toD_iff E rho).mp h.valid, h.noRestart⟩,
    fun h => ⟨(D.executionValid_toD_iff E rho).mpr h.valid, h.noRestart⟩⟩

theorem healthyCore_agrees (cut : Time) :
    Duty.HealthyCore E rho.toD cut ↔ Gen.V2.HealthyCore E rho cut :=
  ⟨fun h => ⟨(D.healthyPrefixDelivery_toD_iff E rho cut).mp h.healthy⟩,
    fun h => ⟨(D.healthyPrefixDelivery_toD_iff E rho cut).mpr h.healthy⟩⟩

theorem cutCore_agrees (cut : Time) :
    Duty.CutCore E rho.toD cut ↔ Gen.V2.CutCore E rho cut :=
  ⟨fun h => ⟨(healthyCore_agrees E rho cut).mp h.toHealthyCore, h.cut⟩,
    fun h => ⟨(healthyCore_agrees E rho cut).mpr h.toHealthyCore, h.cut⟩⟩

omit [DecidableEq V] in
theorem outageCore_agrees (T b₀ b₁ : Time) :
    Duty.OutageCore rho.toD T b₀ b₁ ↔ Gen.V2.OutageCore rho T b₀ b₁ :=
  ⟨fun h => ⟨h.order⟩, fun h => ⟨h.order⟩⟩

theorem recoveryCore_agrees (I : V2.Interface P) (G : Time) :
    Duty.RecoveryCore P.toD I.toD E rho.toD G ↔ Gen.V2.RecoveryCore P I E rho G :=
  ⟨fun h => ⟨(D.partialSynchrony_toD_iff E rho).mp h.sync, h.gap⟩,
    fun h => ⟨(D.partialSynchrony_toD_iff E rho).mpr h.sync, h.gap⟩⟩

theorem seedAt_agrees (i : Nat) (Q : V → P.State → Prop) :
    Duty.SeedAt E rho.toD i Q ↔ Gen.V2.SeedAt E rho i Q := by
  simp only [Duty.SeedAt_def, Gen.V2.SeedAt_def, D.stateBefore_toD]

omit [DecidableEq V] in
theorem honestNeverSlashed_agrees (I : Gen.V2.SlashingInterface (V := V) P) :
    Duty.HonestNeverSlashed (slashingLift I) rho.toD ↔ Gen.V2.HonestNeverSlashed I rho :=
  Iff.rfl

theorem genericOwnReleased_agrees (v : V) (i j : Nat) :
    D.Engine.ownReleased E rho.toD v i j = V2.Engine.ownReleased E rho v i j := by
  rw [D.Engine.ownReleased_def]
  unfold V2.Engine.ownReleased
  congr 1
  funext k
  simp only [D.Engine.ownReleasedAt_def, V2.Engine.ownReleasedAt,
    D.emitsAt_toD, D.objSelfVisible_toD]

theorem ownRecord_fold_restart_agrees {β : Type} (proj : P.State → β)
    (g : β → P.Object → β) {i j : Nat} :
    statementOf (Duty.ownRecord_fold_restart proj g (i := i) (j := j) (E := E) (rho := rho.toD)) ↔
      statementOf (Gen.V2.ownRecord_fold_restart proj g
        (i := i) (j := j) (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD, genericOwnReleased_agrees]

theorem invariant_triple_agrees (Q : P.State → Prop) :
    statementOf (Duty.invariant_triple Q (E := E) (rho := rho.toD)) ↔
      statementOf (Gen.V2.invariant_triple Q (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD]

theorem invariant_clock_free_agrees {β : Type} (proj : P.State → β) (Q : β → Prop) :
    statementOf (Duty.invariant_clock_free proj Q (E := E) (rho := rho.toD)) ↔
      statementOf (Gen.V2.invariant_clock_free proj Q (E := E) (rho := rho)) := by
  simp only [statementOf, D.stateBefore_toD]

theorem interval_induction_all_agrees (Q : V → P.State → Prop) {i j : Nat} :
    statementOf (Duty.interval_induction_all E rho.toD Q (i := i) (j := j)) ↔
      statementOf (Gen.V2.interval_induction_all E rho Q (i := i) (j := j)) := by
  simp only [statementOf, D.stateBefore_toD, D.world_step_toD]

theorem write_once_along_run_agrees {α : Type} (field : P.State → Option α) {i j : Nat} :
    statementOf (Duty.write_once_along_run field E rho.toD (i := i) (j := j)) ↔
      statementOf (Gen.V2.write_once_along_run field E rho (i := i) (j := j)) := by
  simp only [statementOf, D.stateBefore_toD, D.world_step_toD]

theorem kept_from_seed_agrees (Q : V → P.State → Prop) {start stop : Nat} :
    statementOf (Duty.kept_from_seed E rho.toD Q (start := start) (stop := stop)) ↔
      statementOf (Gen.V2.kept_from_seed E rho Q (start := start) (stop := stop)) := by
  simp only [statementOf, D.stateBefore_toD, D.world_step_toD, seedAt_agrees]

theorem base_invariant_agrees {B : Type} (base : P.State → B) (R : B → B → Prop)
    (Q : B → Prop) :
    statementOf (Duty.base_invariant base R Q E rho.toD) ↔
      statementOf (Gen.V2.base_invariant base R Q E rho) := by
  simp only [statementOf, D.stateBefore_toD, D.world_step_toD]

theorem base_invariant_holdsBefore_agrees {B : Type} (base : P.State → B)
    (R : B → B → Prop) (Q : B → Prop) :
    statementOf (Duty.base_invariant_holdsBefore base R Q E rho.toD) ↔
      statementOf (Gen.V2.base_invariant_holdsBefore base R Q E rho) := by
  simp only [statementOf, D.stateBefore_toD, D.world_step_toD,
    D.scheduleWellFormed_toD_iff, holdsBefore_agrees]

theorem timely_of_clock_agrees {T : P.State → P.Object → Prop} (C : Gen.V2.TimelyClock P T) :
    statementOf (Duty.timely_of_clock E rho.toD (timelyLift C)) ↔
      statementOf (Gen.V2.timely_of_clock E rho C) := by
  simp only [statementOf, D.stateBefore_toD, D.scheduleWellFormed_toD_iff,
    D.restartFree_toD_iff]

set_option linter.unusedDecidableInType false in
theorem timely_of_emit_agrees {T : P.State → P.Object → Prop} (C : Gen.V2.TimelyClock P T) :
    statementOf (Duty.timely_of_emit E rho.toD (timelyLift C)) ↔
      statementOf (Gen.V2.timely_of_emit E rho C) := by
  rfl

theorem timely_of_relay_agrees {T : P.State → P.Object → Prop} (C : Gen.V2.TimelyClock P T) :
    statementOf (Duty.timely_of_relay E rho.toD (timelyLift C)) ↔
      statementOf (Gen.V2.timely_of_relay E rho C) := by
  simp only [statementOf, D.scheduleWellFormed_toD_iff, D.acceptsAt_toD, admitSound_agrees,
    pubFloor_agrees]

theorem firstAccept_of_processed_agrees :
    statementOf (Duty.firstAccept_of_processed E rho.toD) ↔
      statementOf (Gen.V2.firstAccept_of_processed E rho) := by
  simp only [statementOf, D.stateBefore_toD, D.restartFree_toD_iff, D.acceptsAt_toD]

omit [DecidableEq V] in
theorem linked_holder_eq_agrees {F : P.Label → Prop} (hL : V2.Linked F rho)
    {ℓ ℓ' : P.Label} :
    statementOf (Duty.linked_holder_eq (rho := rho.toD) (ℓ := ℓ) (ℓ' := ℓ') hL) ↔
      statementOf (Gen.V2.linked_holder_eq (ℓ := ℓ) (ℓ' := ℓ') hL) := Iff.rfl

omit [DecidableEq V] in
theorem linked_card_le_agrees {F : P.Label → Prop} (hL : V2.Linked F rho) :
    statementOf (Duty.linked_card_le_of_holders (rho := rho.toD) hL) ↔
      statementOf (Gen.V2.linked_card_le_of_holders hL) := Iff.rfl

end AvailableChain.Gen.V2.Duty.Tests.Lift

namespace AvailableChain.Gen.V2.Duty.Tests

/-- Send-once permits different FG contents at different duties. -/
theorem two_fg_contents :
    D.Run.emits env run 0 ⟨.seat () 0, false⟩ 0 ∧
    D.Run.emits env run 0 ⟨.seat () 0, true⟩ 1 := by
  exact ⟨⟨0, rfl, by decide⟩, ⟨1, rfl, by decide⟩⟩

/-- One signing seat does not give unconditional FG content uniqueness. -/
theorem unconditional_fg_uniqueness_false :
    ¬ (∀ (p q : Bool) (t u : Time),
      D.Run.emits env run 0 ⟨.seat () 0, p⟩ t →
      D.Run.emits env run 0 ⟨.seat () 0, q⟩ u → p = q) := by
  intro h
  exact Bool.false_ne_true (h false true 0 1 two_fg_contents.1 two_fg_contents.2)

/-- Send-once does not equate the action times of different contents. -/
theorem unconditional_fg_action_uniqueness_false :
    ¬ (∀ (p q : Bool) (t u : Time),
      D.Run.emits env run 0 ⟨.seat () 0, p⟩ t →
      D.Run.emits env run 0 ⟨.seat () 0, q⟩ u → t = u) := by
  intro h
  exact (by decide : (0 : Time) ≠ 1)
    (h false true 0 1 two_fg_contents.1 two_fg_contents.2)

end AvailableChain.Gen.V2.Duty.Tests

-- Migration 03 test axiom coverage.
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.clockLift
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.timelyLift
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.finalityLift
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.slashingLift
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.statementOf
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.finality_roundtrip
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.timely_roundtrip
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.faulty_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.awakeHonest_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.idxBefore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.nthIdx_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.pubFloor_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.honestSlot_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.holdsBefore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.monoAlong_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.pending_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.trigger_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.deliveryWithin_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.acceptanceLaw_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.admitSound_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.labelSync_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.labelFacts_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.baseCore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.healthyCore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.cutCore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.outageCore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.recoveryCore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.seedAt_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.honestNeverSlashed_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.genericOwnReleased_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.ownRecord_fold_restart_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.invariant_triple_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.invariant_clock_free_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.interval_induction_all_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.write_once_along_run_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.kept_from_seed_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.base_invariant_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.base_invariant_holdsBefore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.timely_of_clock_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.timely_of_emit_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.timely_of_relay_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.firstAccept_of_processed_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.linked_holder_eq_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.linked_card_le_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.two_fg_contents
#print axioms AvailableChain.Gen.V2.Duty.Tests.unconditional_fg_uniqueness_false
#print axioms AvailableChain.Gen.V2.Duty.Tests.unconditional_fg_action_uniqueness_false

namespace AvailableChain.Gen.V2.Duty.Tests.Lift

variable {In V : Type} [DecidableEq V] {P : ProtocolSpec In}
  (E : Generic.Env V) (rho : V2.Run V P)

theorem stateBefore_idxBefore_agrees :
    statementOf (Duty.stateBefore_idxBefore E rho.toD) ↔
      statementOf (Gen.V2.stateBefore_idxBefore E rho) := by
  simp only [statementOf, D.scheduleWellFormed_toD_iff, D.stateBefore_toD, D.stateBeforeTime_toD,
    idxBefore_agrees]

theorem holdsBefore_iff_exists_idx_agrees {Q : P.State → Prop} {d : Time} {x : V} :
    statementOf (Duty.holdsBefore_iff_exists_idx (E := E) (rho := rho.toD)
      (Q := Q) (d := d) (x := x)) ↔
      statementOf (Gen.V2.holdsBefore_iff_exists_idx (E := E) (rho := rho)
        (Q := Q) (d := d) (x := x)) := by
  simp only [statementOf, D.noRestart_toD_iff, D.scheduleWellFormed_toD_iff,
    D.stateBefore_toD, holdsBefore_agrees, monoAlong_agrees]

/-- All deadline premises survive the identity lift. -/
theorem accepted_by_deadline_agrees {T : P.State → P.Object → Prop}
    {Inv : P.State → Prop} :
    statementOf (Duty.accepted_by_deadline E rho.toD (Timely := T) (Inv := Inv)) ↔
      statementOf (Gen.V2.accepted_by_deadline E rho (Timely := T) (Inv := Inv)) := by
  have hready : ∀ o send w a d, Duty.ReadyTrigger E rho.toD o send w a d ↔
      Gen.V2.ReadyTrigger E rho o send w a d := by
    intros
    simp only [Duty.ReadyTrigger, Gen.V2.ReadyTrigger, D.emits_toD,
      D.acceptsAt_toD, D.linkReadyOn_toD_iff]
  have hcut : ∀ a, D.Run.actionCut rho.toD a = V2.Run.actionCut rho a := fun _ => rfl
  have hhist : ∀ w o a, Duty.HistorySafeAt E rho.toD w o a ↔
      Gen.V2.HistorySafeAt E rho w o a := by
    intros
    simp only [Duty.HistorySafeAt, Gen.V2.HistorySafeAt, D.processedByActionCut_toD_iff,
      D.Run.stateAfterRestartsAt, V2.Run.stateAfterRestartsAt, D.stateBefore_toD, hcut]
  simp only [statementOf, deliveryWithin_agrees, hready, hhist, hcut,
    D.scheduleWellFormed_toD_iff, D.restartFree_toD_iff, D.stateBefore_toD,
    D.stateBeforeTime_toD, D.handlesAt_toD, idxBefore_agrees, acceptanceLaw_agrees,
    D.hooksSound_toD_iff]

end AvailableChain.Gen.V2.Duty.Tests.Lift

namespace AvailableChain.Gen.V2.Duty.Tests

/-- The FG counterexample has a complete, ordered public schedule. -/
theorem twoDuty_schedule : D.ScheduleWellFormed env run where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by simp [Event.time]
  honest_only := by simp [Event.node]
  tick_public := by
    intro v t h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Event.tick.injEq] at h
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  tick_total := by
    intro v _ t _ h0 h1 _
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    have ht : t = 0 ∨ t = 1 := by
      change t ≤ 1 at h1
      dsimp only [Time] at *
      omega
    rcases ht with rfl | rfl <;> simp

theorem twoDuty_executionValid : D.ExecutionValid env run where
  toScheduleWellFormed := twoDuty_schedule
  tick_awake := fun _ _ _ => rfl
  deliver_awake := fun _ _ _ _ => rfl
  restart_awake := fun _ _ _ => rfl
  wake_restart := fun _ _ _ _ _ hw => by cases hw.2
  wire := by intros; rfl
  deps := by intros; rfl
  fresh := by intros; rfl
  unforgeable := by
    rintro v o t ⟨i, hi⟩
    have hm := List.mem_of_getElem? hi
    simp at hm
  carried := by
    rintro v o t ⟨i, hi⟩
    have hm := List.mem_of_getElem? hi
    simp at hm

theorem twoDuty_linked : D.Linked (fun ℓ => ℓ = ()) run :=
  (D.Engine.linked_singleton_iff run ()).mpr ⟨Equiv.refl (Fin 1), fun _ => rfl⟩

/-- The same durable record is used on each side of the restart. -/
abbrev restartedRun : D.Run (Fin 1) toy :=
  { run with events := [.tick 0 0, .restart 0 1, .tick 0 1] }

theorem generic_restart_fold :
    D.Run.stateBefore env restartedRun 3 0 =
      (D.Engine.ownReleased env restartedRun 0 0 3).foldl
        (fun st o => o.payload :: st) [] := by
  exact ownRecord_fold_restart id (fun st o => o.payload :: st)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    env restartedRun (i := 0) (j := 3) (by omega) 0 (by intros; rfl)

theorem generic_restart_contents :
    D.Run.stateBefore env restartedRun 1 0 = [false] ∧
    D.Run.stateBefore env restartedRun 2 0 = [false] ∧
    D.Run.stateBefore env restartedRun 3 0 = [true, false] := by decide

/-- A HEAD-style label supplies SingleDuty to the existing honest producer. -/
example : HonestUniqueSingleDutyStatement := honest_unique_singleDuty_statement

end AvailableChain.Gen.V2.Duty.Tests

#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.stateBefore_idxBefore_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.holdsBefore_iff_exists_idx_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.Lift.accepted_by_deadline_agrees
#print axioms AvailableChain.Gen.V2.Duty.Tests.twoDuty_schedule
#print axioms AvailableChain.Gen.V2.Duty.Tests.twoDuty_executionValid
#print axioms AvailableChain.Gen.V2.Duty.Tests.twoDuty_linked
#print axioms AvailableChain.Gen.V2.Duty.Tests.restartedRun
#print axioms AvailableChain.Gen.V2.Duty.Tests.generic_restart_fold
#print axioms AvailableChain.Gen.V2.Duty.Tests.generic_restart_contents
