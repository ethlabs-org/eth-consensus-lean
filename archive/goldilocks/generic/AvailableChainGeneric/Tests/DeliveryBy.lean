module
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy
public import Mathlib.Tactic.IntervalCases

@[expose] public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine
open AvailableChain.Gen.Pure

namespace AvailableChain.Gen.V2.Duty.DeliveryByTests

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)

theorem partial_forward (h : D.PartialSynchrony E rho) :
    PartialSynchronyBy E rho (fun _ => E.Δ) :=
  (partialSynchrony_iff_by_const E rho).1 h

theorem partial_reverse (h : PartialSynchronyBy E rho (fun _ => E.Δ)) :
    D.PartialSynchrony E rho :=
  (partialSynchrony_iff_by_const E rho).2 h

theorem prefix_forward (cut : Time) (h : D.HealthyPrefixDelivery E rho cut) :
    HealthyPrefixDeliveryBy E rho (fun _ => E.Δ) cut :=
  (healthyPrefix_iff_by_const E rho cut).1 h

theorem prefix_reverse (cut : Time) (h : HealthyPrefixDeliveryBy E rho (fun _ => E.Δ) cut) :
    D.HealthyPrefixDelivery E rho cut :=
  (healthyPrefix_iff_by_const E rho cut).2 h

theorem true_forward (dl : Time → Time) (cut : Time) (h : DeliveryWithin E rho dl cut) :
    DeliveryWithinOn E rho (fun _ => True) dl cut :=
  (deliveryWithin_iff_on_true E rho dl cut).1 h

theorem true_reverse (dl : Time → Time) (cut : Time)
    (h : DeliveryWithinOn E rho (fun _ => True) dl cut) : DeliveryWithin E rho dl cut :=
  (deliveryWithin_iff_on_true E rho dl cut).2 h

theorem false_vacuous (dl : Time → Time) (cut : Time) :
    DeliveryWithinOn E rho (fun _ => False) dl cut := by
  constructor
  · intro v hv o ho
    exact ho.elim
  · intro v hv i o ho
    exact ho.elim

theorem family_mono {Q Q' : P.Object → Prop} {dl : Time → Time} {cut : Time}
    (h : DeliveryWithinOn E rho Q dl cut) (hQ : ∀ o, Q' o → Q o) :
    DeliveryWithinOn E rho Q' dl cut :=
  DeliveryWithinOn.of_subfamily E rho h hQ

theorem sync_bridge (Q : P.Object → Prop) (vt dt : Time) (h : LabelSync E rho vt dt) :
    LabelSyncOn E rho Q vt dt := labelSync_to_on E rho Q vt dt h

theorem facts_bridge (Q : P.Object → Prop) (vt dt : Time) (h m : Nat)
    (hf : LabelFacts E rho vt dt h m) : LabelFactsOn E rho Q vt dt h m :=
  labelFacts_to_on E rho Q vt dt h m hf

/-- False is the block family. True is the row family. A block can accept a row. -/
abbrev toy : ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Bool
  Durable := Bool
  init := false
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; exact d.elim
  duties_nodup := by intro t; simp
  act := fun _ d => d.elim
  gossip := fun _ _ => []
  process := fun _ _ => true
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := fun d _ => d
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun st o => if o.payload then st else false
  excludes := fun _ _ => false
  handles := fun _ o' o => o'.payload = o.payload ∨
    (o'.payload = false ∧ o.payload = true)
  carries := fun o' o => o'.payload = false ∧ o.payload = true

abbrev env : Generic.Env (Fin 2) := ⟨2, by decide, 0, by decide, fun _ _ => true⟩
abbrev ΔF : Time := 5
abbrev block : toy.Object := ⟨.none, false⟩
abbrev row : toy.Object := ⟨.none, true⟩
abbrev delayOf (o : toy.Object) : Time := if o.payload then ΔF else env.Δ
abbrev IsRow (o : toy.Object) : Prop := o.payload = true
abbrev IsBlock (o : toy.Object) : Prop := o.payload = false

abbrev run : D.Run (Fin 2) toy where
  honest := {0, 1}
  horizon := 12
  events := [.deliver 0 block 4, .deliver 1 row 8]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

theorem delay_gap : env.Δ < ΔF := by decide

theorem row_positive : 0 < ΔF :=
  delay_pos_of_env_le env (le_of_lt delay_gap)

theorem row_deadline_strict (t : Time) : t < t + ΔF :=
  lt_add_of_pos_right t row_positive

theorem row_exact : ∀ o, IsRow o → delayOf o = ΔF := by
  intro o ho
  simp [delayOf, ho]

theorem block_exact : ∀ o, IsBlock o → delayOf o = env.Δ := by
  intro o ho
  simp [delayOf, ho]

theorem delivery_no_emission (v : Fin 2) (o : toy.Object) (t : Time) :
    ¬ D.Run.emits env run v o t := by
  rintro ⟨i, hi, _⟩
  have hm := List.mem_of_getElem? hi
  simp at hm

theorem acceptance_cases {i : Nat} {v : Fin 2} {o : toy.Object} {t : Time}
    (ha : D.Run.acceptsAt env run i v o t) :
    IsRow o ∧ ((i = 0 ∧ v = 0 ∧ t = 4) ∨ (i = 1 ∧ v = 1 ∧ t = 8)) := by
  obtain ⟨⟨o', hi, _⟩, _, ht⟩ := ha
  have ho : IsRow o := by
    cases hp : o.payload
    · simp [hp] at ht
    · exact hp
  have hil : i < 2 := (List.getElem?_eq_some_iff.mp hi).1
  have hic : i = 0 ∨ i = 1 := by omega
  refine ⟨ho, ?_⟩
  rcases hic with rfl | rfl
  · change some (Event.deliver (0 : Fin 2) block 4) = some (Event.deliver v o' t) at hi
    have he := Event.deliver.inj (Option.some.inj hi)
    exact Or.inl ⟨rfl, he.1.symm, he.2.2.symm⟩
  · change some (Event.deliver (1 : Fin 2) row 8) = some (Event.deliver v o' t) at hi
    have he := Event.deliver.inj (Option.some.inj hi)
    exact Or.inr ⟨rfl, he.1.symm, he.2.2.symm⟩

theorem relay_delivery (v : Fin 2) (i : Nat) (o : toy.Object) (t : Time)
    (ha : D.Run.acceptsAt env run i v o t) (w : Fin 2)
    (hp : toy.processed (D.Run.stateBefore env run (i + 1) w) o = false) :
    ∃ t', t ≤ t' ∧ t' < t + delayOf o ∧ ∃ j, D.Run.handlesAt env run j w o t' := by
  obtain ⟨ho, hc⟩ := acceptance_cases ha
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hw : w = 0 ∨ w = 1 := by
      have hv : w.val = 0 ∨ w.val = 1 := by omega
      exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    rcases hw with rfl | rfl
    · change (if o.payload then true else false) = false at hp
      simp [ho] at hp
    · refine ⟨8, by decide, ?_, 1, row, rfl, Or.inl ho.symm⟩
      rw [row_exact o ho]
      decide
  · have hw : w = 0 ∨ w = 1 := by
      have hv : w.val = 0 ∨ w.val = 1 := by omega
      exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
    rcases hw with rfl | rfl <;>
      change (if o.payload then true else false) = false at hp <;>
      simp [ho] at hp

theorem relay_service {o : toy.Object} {a d : Time}
    (ho : IsRow o) (w : Fin 2) (ha : 4 ≤ a) (hd : a + ΔF ≤ d) :
    D.DeliveryService env run w o a d := by
  have hw : w = 0 ∨ w = 1 := by
    have hv : w.val = 0 ∨ w.val = 1 := by omega
    exact hv.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  rcases hw with rfl | rfl
  · by_cases hlt : 4 < a
    · refine Or.inl ⟨1, ?_, ?_⟩
      · simp [D.Run.actionCut, Event.time, Event.phase, hlt]
      · change (if o.payload then true else false) = true
        simp [ho]
    · refine Or.inr ⟨4, ?_, ?_, 0, block, rfl, Or.inr ⟨rfl, ho⟩⟩
      · exact le_of_not_gt hlt
      · dsimp [ΔF, Time] at *; omega
  · by_cases hlt : 8 < a
    · refine Or.inl ⟨2, ?_, ?_⟩
      · have h4 : (4 : Time) < a := by dsimp [Time] at *; omega
        simp [D.Run.actionCut, Event.time, Event.phase, hlt, h4]
      · change (if o.payload then true else false) = true
        simp [ho]
    · refine Or.inr ⟨8, le_of_not_gt hlt, ?_, 1, row, rfl, Or.inl ho.symm⟩
      dsimp [ΔF, Time] at *; omega

theorem partial_by : PartialSynchronyBy env run delayOf := by
  constructor
  · intro v hv o t he
    exact (delivery_no_emission v o t he).elim
  · intro v hv i o t ha w hw a hta _ _ _ _ _ _
    obtain ⟨ho, ht⟩ := acceptance_cases ha
    have h4 : 4 ≤ a := by rcases ht with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      dsimp [Time] at * <;> omega
    apply relay_service ho w h4
    rw [row_exact o ho]
    exact add_le_add (le_max_left a env.t_GST) le_rfl

theorem prefix_by : HealthyPrefixDeliveryBy env run delayOf 12 := by
  constructor
  · intro v hv o t he
    exact (delivery_no_emission v o t he).elim
  · intro v hv i o t ha w hw a hta _ _ _ _ _ _
    obtain ⟨ho, ht⟩ := acceptance_cases ha
    have h4 : 4 ≤ a := by rcases ht with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      dsimp [Time] at * <;> omega
    apply relay_service ho w h4
    rw [row_exact o ho]

theorem row_partial : DeliveryWithinOn env run IsRow
    (fun t => max t env.t_GST + ΔF) run.horizon :=
  deliveryWithinOn_of_partialSynchronyBy env run partial_by IsRow ΔF row_exact

theorem block_partial : DeliveryWithinOn env run IsBlock
    (fun t => max t env.t_GST + env.Δ) run.horizon :=
  deliveryWithinOn_of_partialSynchronyBy env run partial_by IsBlock env.Δ block_exact

theorem row_prefix : DeliveryWithinOn env run IsRow (fun t => t + ΔF) 12 :=
  deliveryWithinOn_of_healthyPrefixBy env run 12 prefix_by IsRow ΔF row_exact

theorem block_prefix : DeliveryWithinOn env run IsBlock (fun t => t + env.Δ) 12 :=
  deliveryWithinOn_of_healthyPrefixBy env run 12 prefix_by IsBlock env.Δ block_exact

theorem block_sync_clean : LabelSyncOn env run IsBlock 0 2 :=
  LabelSyncOn.of_cleanCutBy env run IsBlock 12 0 2 prefix_by block_exact
    (by decide) (by decide) (by decide)

theorem block_sync_recovery : LabelSyncOn env run IsBlock 0 2 :=
  LabelSyncOn.of_recoveryBy env run IsBlock 0 2 partial_by block_exact
    (by decide) (by decide) (by decide)

theorem block_facts_clean : LabelFactsOn env run IsBlock 0 2 1 0 :=
  LabelFactsOn.of_cleanCutBy env run IsBlock 12 0 2 1 0 prefix_by block_exact
    (by decide) (by decide) (by decide) ⟨by decide⟩

theorem block_facts_recovery : LabelFactsOn env run IsBlock 0 2 1 0 :=
  LabelFactsOn.of_recoveryBy env run IsBlock 0 2 1 0 partial_by block_exact
    (by decide) (by decide) (by decide) ⟨by decide⟩

/-- The delivered object is the block; the accepted object is the row. -/
theorem row_accepted_through_block : D.Run.acceptsAt env run 0 0 row 4 := by
  exact ⟨⟨block, rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl, rfl⟩

theorem row_fresh_at_four : ¬ D.ProcessedByActionCut env run 1 row 4 := by
  rintro ⟨k, hk, hp⟩
  have hk0 : k = 0 := by simpa [D.Run.actionCut, Event.time, Event.phase] using hk
  subst k
  contradiction

/-- Relay is due at 4 + 5 = 9, from row acceptance, and arrives at 8. -/
theorem row_relay_from_acceptance :
    ∃ t', 4 ≤ t' ∧ t' < 4 + ΔF ∧ ∃ j, D.Run.handlesAt env run j 1 row t' := by
  have h := partial_by.relay_accepted 0 (by simp) 0 row 4 row_accepted_through_block
    1 (by simp) 4 le_rfl (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ => rfl) rfl
  exact h.resolve_left row_fresh_at_four


theorem row_relay_after_block_deadline :
    D.Run.handlesAt env run 1 1 row 8 ∧ 4 + env.Δ ≤ 8 ∧ 8 < 4 + ΔF := by
  exact ⟨⟨row, rfl, Or.inl rfl⟩, by decide, by decide⟩

/-- The old all-object delay would require the row before time 6. -/
theorem old_partial_rejected : ¬ D.PartialSynchrony env run := by
  intro h
  have hs := h.relay_accepted 0 (by simp) 0 row 4 row_accepted_through_block
    1 (by simp) 4 le_rfl (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ => rfl) rfl
  obtain ⟨t', _, hlt, j, o', hj, _⟩ := hs.resolve_left row_fresh_at_four
  have hm := List.mem_of_getElem? hj
  change Event.deliver (1 : Fin 2) o' t' ∈
    [Event.deliver 0 block 4, Event.deliver 1 row 8] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Event.deliver.injEq] at hm
  rcases hm with ⟨he, _, _⟩ | ⟨_, _, ht⟩
  · exact (by decide : (1 : Fin 2) ≠ 0) he
  · subst t'
    exact (by decide : ¬ (8 : Time) < max 4 env.t_GST + env.Δ) hlt

-- The anchor deadline may equal the read cutoff. The handler is still strict.
example : ∃ t', 4 ≤ t' ∧ t' < (9 : Time) ∧
    ∃ j, D.Run.handlesAt env run j 1 row t' := by
  exact ready_relay (dl := fun a => a + ΔF) (cut := 9)
    ⟨fun v hv o ho t he w hw a hta ha had hc hh hr hx =>
        row_prefix.broadcast v hv o ho t he w hw a hta ha had
          (hc.trans (by decide)) hh hr hx,
      fun v hv i o ho t he w hw a hta ha had hc hh hr hx =>
        row_prefix.relay v hv i o ho t he w hw a hta ha had
          (hc.trans (by decide)) hh hr hx⟩ (v := 0) (i := 0)
    (by simp) rfl row_accepted_through_block (by simp) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ => rfl) row_fresh_at_four rfl

namespace SleepReceipts

-- The clock and the stored receipt stamp are separate fields.
abbrev stamped : ProtocolSpecD Unit :=
  { toy with
    State := Time × Option Time
    act := fun _ d => d.elim
    gossip := fun _ _ => []
    depsPresent := fun _ _ => true
    excludes := fun _ _ => false
    Durable := Unit
    init := (0, none)
    clock := fun st t => (t, st.2)
    process := fun st _ => (st.1, some st.1)
    recordOwn := fun st _ => st
    durable := fun _ => ()
    restore := fun _ t => (t, none)
    processed := fun st _ => st.2.isSome
    handles := fun _ o o' => o = o'
    carries := fun _ _ => False }

abbrev object : stamped.Object := ⟨.none, true⟩
abbrev awake : Generic.Env Unit :=
  ⟨2, by decide, 0, le_rfl, fun _ t => decide (2 ≤ t)⟩
abbrev trace (deliveryTime : Time) : D.Run Unit stamped where
  honest := {()}
  horizon := 4
  events := if deliveryTime = 2 then [.restart () 2, .tick () 2, .deliver () object 2, .tick () 4]
    else [.restart () 2, .tick () 2, .tick () 4, .deliver () object 4]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

theorem trace_valid (deliveryTime : Time) :
    D.ExecutionValid awake (trace deliveryTime) := by
  have hcases : deliveryTime = 2 ∨ deliveryTime ≠ 2 := eq_or_ne deliveryTime 2
  rcases hcases with h | h
  all_goals
    refine {
      horizon_nonneg := ?_
      sorted := ?_
      nodup := ?_
      in_horizon := ?_
      honest_only := ?_
      tick_public := ?_
      tick_total := ?_
      wire := ?_
      deps := ?_
      fresh := ?_
      unforgeable := ?_
      carried := ?_
      tick_awake := ?_
      deliver_awake := ?_
      restart_awake := ?_
      wake_restart := ?_
    }
  all_goals solve
    | (change (0 : Time) ≤ 4; decide)
    | (simp only [trace, h, ↓reduceIte]; decide)
    | (intros; rfl)
    | (intro v o t hp o' hc; exact hc.elim)
    | (intros; simp)
    | (intro v t ht
       have ht' : t = 2 ∨ t = 4 := by simpa [h] using ht
       rcases ht' with rfl | rfl
       exact ⟨1, rfl⟩
       exact ⟨2, rfl⟩)
    | (intro v _ t ⟨k, hk⟩ _ hh ha
       change t = (k : Int) * 2 at hk
       change t ≤ 4 at hh
       have ha' : 2 ≤ t := of_decide_eq_true ha
       have ht : t = 2 ∨ t = 4 := by dsimp [Time] at *; omega
       rcases ht with rfl | rfl <;> simp [h])
    | (intro i v o t hi
       have hil := (List.getElem?_eq_some_iff.mp hi).1
       have hil' : i < 4 := by simpa [h] using hil
       interval_cases i <;> simp [h] at hi
       rcases hi with ⟨rfl, rfl⟩
       simp [D.Run.stateBefore, D.World.step, D.tick, h])
    | (rintro v o t ⟨i, hi⟩ u _ hu
       have hm := List.mem_of_getElem? hi
       simp [h] at hm
       rcases hm with ⟨rfl, rfl⟩
       contradiction)
    | (intro v t ht; simp [h] at ht
       rcases ht with rfl | rfl <;> rfl)
    | (intro v o t ht; simp [h] at ht
       rcases ht with ⟨rfl, rfl⟩; rfl)
    | (intro v _ t _ _ hw
       have ha : 2 ≤ t := of_decide_eq_true hw.1
       have hb : ¬ 2 ≤ t - 1 := of_decide_eq_false hw.2
       have ht : t = 2 := by dsimp [Time] at *; omega
       subst t; simp [h])

abbrev stampedClock : ClockLaws stamped :=
  ⟨Prod.fst, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
abbrev stampedRestore : RestoreTimeLaw stampedClock := ⟨fun _ _ => rfl⟩

-- All premises of the receipt core hold together, including an actual wake.
theorem stampedHooks : D.HooksSound stamped where
  excludes_inert := by intros st o h; contradiction
  excludes_stable := by intros V _ E rho hS v o i j hij hrf hx; contradiction
  processed_stable := by
    intro V _ E rho _ v o i j hij hrf hi
    exact stateBefore_stable (fun st => stamped.processed st o = true)
      (by intros; assumption) (by intros; rfl) (by intros; assumption)
      E rho hij v hrf hi
  deps_stable := by intros; rfl
  handles_carries := by intro st o o' h; exact Or.inl h
  recordOwn_processed := by intros; rfl
  recordOwn_deps := by intros; rfl
  recordOwn_excludes := by intros; assumption

theorem stampedAcceptance :
    AcceptanceLaw stamped (fun _ _ => True) (fun _ => True) :=
  ⟨by intros; exact Or.inl rfl⟩

theorem fresh : ¬ D.ProcessedByActionCut awake (trace 2) () object 2 := by
  rintro ⟨i, hi, hp⟩
  have hi' : i ≤ 1 := by simpa [D.Run.actionCut, Event.time, Event.phase] using hi
  interval_cases i <;> contradiction

theorem receipt_core :
    stamped.processed (D.Run.stateBeforeTime awake (trace 2) 4 ()) object = true := by
  apply processed_by_deadline_of_service awake (trace 2) (fun _ _ => True)
    (fun _ => True) () object 2 4 (trace_valid 2).toScheduleWellFormed (by decide)
    (Or.inr ⟨2, le_rfl, by decide, 2, object, rfl, rfl⟩)
    (historySafeAt_of_fresh fresh) _ stampedHooks stampedAcceptance
    (by intros; exact ⟨trivial, rfl, rfl, trivial⟩) rfl
  intro k t hk hlt he
  have hk' : 1 ≤ k := by simpa [D.Run.actionCut, Event.time, Event.phase] using hk
  have hlt' : k < 3 := by simpa [D.Run.idxBefore, Event.time] using hlt
  interval_cases k <;> simp at he

theorem demand :
    D.DeliveryDemand awake (trace 2) () () object 2 (fun a => a + 2) 4 := by
  intro a hsend _ _ hcut _ _ _
  have ha : a = 2 := by dsimp [Time] at *; omega
  subst a
  exact Or.inr ⟨2, le_rfl, by decide, 2, object, rfl, rfl⟩

theorem handler_before_cutoff : D.HandledBetween awake (trace 2) () object 2 4 :=
  (demand 2 le_rfl (by decide) (by decide) (by decide) (by decide)
    (by intro t ha _; exact decide_eq_true ha) rfl).resolve_left fresh

-- dl(2) = C = 4. The stored receipt uses the handler's pre-event clock.
theorem stamp_before_equal_cutoff : (fun a : Time => a + 2) 2 = (4 : Time) ∧
    ∃ stamp, (D.Run.stateBeforeTime awake (trace 2) 4 ()).2 = some stamp ∧ stamp < 4 := by
  obtain ⟨t, _, ht, i, o, hi, _⟩ := handler_before_cutoff
  have hil : i < 4 := (List.getElem?_eq_some_iff.mp hi).1
  interval_cases i <;> simp at hi
  obtain ⟨rfl, rfl⟩ := hi
  refine ⟨rfl, stampedClock.now (D.Run.stateBefore awake (trace 2) 2 ()), rfl, ?_⟩
  exact lt_of_le_of_lt
    (stateBefore_now_le_event_atRestart stampedClock stampedRestore awake (trace 2)
      (trace_valid 2).toScheduleWellFormed
      (show (trace 2).events[2]? = some (.deliver () object 2) from rfl) ()) ht

-- A valid delivery exactly at C stores C, which fails the strict receipt test.
theorem late_stamp_rejected : D.ExecutionValid awake (trace 4) ∧
    (D.Run.stateBefore awake (trace 4) 4 ()).2 = some 4 ∧
    ¬ (4 : Time) < 4 := ⟨trace_valid 4, rfl, by decide⟩

theorem late_handler_at_cutoff : D.Run.handlesAt awake (trace 4) 3 () object 4 :=
  ⟨object, rfl, rfl⟩

theorem late_handler_rejected : ¬ D.HandledBetween awake (trace 4) () object 2 4 := by
  rintro ⟨t, _, ht, i, o, hi, _⟩
  have hm := List.mem_of_getElem? hi
  simp at hm
  obtain ⟨_, _, rfl⟩ := hm
  exact (lt_irrefl _ ht)

theorem late_demand_rejected :
    ¬ D.DeliveryDemand awake (trace 4) () () object 2 (fun a => a + 2) 4 := by
  intro hd
  have hs := hd 2 le_rfl (by decide) (by decide) (by decide) (by decide)
    (by intro t ha _; exact decide_eq_true ha) rfl
  rcases hs with ⟨i, hi, hp⟩ | hh
  · have hi' : i ≤ 1 := by simpa [D.Run.actionCut, Event.time, Event.phase] using hi
    interval_cases i <;> contradiction
  · exact late_handler_rejected hh

theorem late_read_empty :
    stamped.processed (D.Run.stateBeforeTime awake (trace 4) 4 ()) object = false := rfl

-- A second wake clears a receipt that was processed before the sleep.
abbrev twiceAwake : Generic.Env Unit :=
  ⟨2, by decide, 0, le_rfl, fun _ t => decide (t = 2 ∨ 4 ≤ t)⟩
abbrev erased : D.Run Unit stamped :=
  { trace 2 with events :=
    [.restart () 2, .tick () 2, .deliver () object 2, .restart () 4, .tick () 4] }

theorem erased_valid : D.ExecutionValid twiceAwake erased where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by simp [Event.time]
  honest_only := by intros; simp
  tick_public := by
    intro v t h
    simp at h
    rcases h with rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  tick_total := by
    intro v _ t _ _ hh ha
    change t ≤ 4 at hh
    have ha' : t = 2 ∨ 4 ≤ t := of_decide_eq_true ha
    have ht : t = 2 ∨ t = 4 := by dsimp [Time] at *; omega
    rcases ht with rfl | rfl <;> simp
  wire := by intros; rfl
  deps := by intros; rfl
  fresh := by
    intro i v o t hi
    have hil : i < 5 := (List.getElem?_eq_some_iff.mp hi).1
    interval_cases i <;> simp at hi
    obtain ⟨rfl, rfl⟩ := hi
    rfl
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ hu
    have hm := List.mem_of_getElem? hi
    simp at hm
    obtain ⟨rfl, rfl⟩ := hm
    contradiction
  carried := by intro v o t _ o' hc; exact hc.elim
  tick_awake := by intro v t h; simp at h; rcases h with rfl | rfl <;> rfl
  deliver_awake := by intro v o t h; simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  restart_awake := by intro v t h; simp at h; rcases h with rfl | rfl <;> rfl
  wake_restart := by
    intro v _ t _ hh hw
    have ha : t = 2 ∨ 4 ≤ t := of_decide_eq_true hw.1
    change t ≤ 4 at hh
    have ht : t = 2 ∨ t = 4 := by dsimp [Time] at *; omega
    rcases ht with rfl | rfl <;> simp

theorem erased_execution : D.ExecutionValid twiceAwake erased := erased_valid

theorem erased_service : D.DeliveryService twiceAwake erased () object 4 6 :=
  Or.inl ⟨3, by decide, rfl⟩

theorem erased_history_rejected : ¬ HistorySafeAt twiceAwake erased () object 4 := by
  intro h
  have := h ⟨3, by decide, rfl⟩
  contradiction

-- A valid handler may refuse processing; it then fails the acceptance law.
abbrev refusing : ProtocolSpecD Unit :=
  { stamped with init := (0, some 0), process := fun st _ => st }
abbrev refused : D.Run Unit refusing := { trace 2 with }

theorem delivery_refused_valid : D.ExecutionValid awake refused where
  horizon_nonneg := (trace_valid 2).horizon_nonneg
  sorted := (trace_valid 2).sorted
  nodup := (trace_valid 2).nodup
  in_horizon := (trace_valid 2).in_horizon
  honest_only := (trace_valid 2).honest_only
  tick_public := (trace_valid 2).tick_public
  tick_total := (trace_valid 2).tick_total
  tick_awake := (trace_valid 2).tick_awake
  deliver_awake := (trace_valid 2).deliver_awake
  restart_awake := (trace_valid 2).restart_awake
  wake_restart := (trace_valid 2).wake_restart
  wire := by intros; rfl
  deps := by intros; rfl
  fresh := by
    intro i v o t hi
    have hil : i < 4 := (List.getElem?_eq_some_iff.mp hi).1
    interval_cases i <;> simp at hi
    obtain ⟨rfl, rfl⟩ := hi
    rfl
  unforgeable := by
    rintro v o t ⟨i, hi⟩ u _ hu
    have hm := List.mem_of_getElem? hi
    simp at hm
    obtain ⟨rfl, rfl⟩ := hm
    contradiction
  carried := by intro v o t _ o' hc; exact hc.elim

theorem refused_handler :
    D.ExecutionValid awake refused ∧ D.Run.handlesAt awake refused 2 () object 2 :=
  ⟨delivery_refused_valid, object, rfl, rfl⟩

theorem refused_history_rejected : ¬ HistorySafeAt awake refused () object 2 := by
  intro h
  have := h ⟨0, by decide, rfl⟩
  contradiction

theorem refused_acceptance_rejected :
    ¬ AcceptanceLaw refusing (fun _ _ => True) (fun _ => True) := by
  intro h
  have := h.processed_of_not_excluded (2, none) object object
    trivial rfl rfl rfl trivial rfl
  contradiction

#print axioms trace_valid
#print axioms stampedHooks
#print axioms stampedAcceptance
#print axioms fresh
#print axioms demand
#print axioms handler_before_cutoff
#print axioms erased_valid
#print axioms delivery_refused_valid

#print axioms receipt_core
#print axioms stamp_before_equal_cutoff
#print axioms late_stamp_rejected
#print axioms late_handler_at_cutoff
#print axioms late_handler_rejected
#print axioms late_demand_rejected
#print axioms late_read_empty
#print axioms erased_execution
#print axioms erased_service
#print axioms erased_history_rejected
#print axioms refused_handler
#print axioms refused_history_rejected
#print axioms refused_acceptance_rejected

end SleepReceipts

end AvailableChain.Gen.V2.Duty.DeliveryByTests

-- Kernel audit of the concrete family tests.
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.partial_forward
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.partial_reverse
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.prefix_forward
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.prefix_reverse
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.true_forward
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.true_reverse
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.false_vacuous
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.family_mono
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.sync_bridge
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.facts_bridge
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.delay_gap
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_positive
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_deadline_strict
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_exact
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_exact
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.delivery_no_emission
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.acceptance_cases
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.relay_delivery
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.partial_by
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.prefix_by
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_partial
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_partial
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_prefix
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_prefix
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_sync_clean
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_sync_recovery
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_facts_clean
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.block_facts_recovery
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_accepted_through_block
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_relay_from_acceptance
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.row_relay_after_block_deadline
#print axioms AvailableChain.Gen.V2.Duty.DeliveryByTests.old_partial_rejected
