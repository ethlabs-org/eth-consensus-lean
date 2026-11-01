module
public import AvailableChainFGCompose.Proofs.Healing.AttemptStop
public import AvailableChainFGCompose.Proofs.Healing.AttemptRows -- shake: keep (height laws)

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d4
open AvailableChain.SimplexFG AvailableChain.KitFG

-- Inhabited event-fold interface models. They do not assert ExecutionValid.
-- Certified heights apply to all blocks, including fresh children.
-- Row-consumer and dispatcher applications use the FG-SA producer in its test file.
private def d4A : FGBlock (Fin 1) := .node .genesis 1 ⟨41⟩ 7 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d4B : FGBlock (Fin 1) := .node .genesis 1 ⟨42⟩ 8 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d4C : FGBlock (Fin 1) := .node d4A 2 ⟨43⟩ 9 [⟨0, .vote 2 d4A.root false, none⟩]
private def d4D : FGBlock (Fin 1) := .node d4B 2 ⟨44⟩ 10 [⟨0, .vote 2 d4B.root false, none⟩]
private def d4E : FGBlock (Fin 1) := .node d4C 3 ⟨45⟩ 11 [⟨0, .vote 3 d4C.root false, none⟩]
private def d4F : FGBlock (Fin 1) := .node d4D 3 ⟨46⟩ 12 [⟨0, .vote 3 d4D.root false, none⟩]
private def d4Row : Row (Fin 1) := ⟨0, .vote 3 d4C.root false, some ⟨0, genesisRoot⟩⟩
private def d4StopRow : Row (Fin 1) := ⟨0, .vote 4 d4E.root true, some ⟨1, d4A.root⟩⟩
private def d4Electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def d4Height : FGHeightView (Fin 1) := simplexHeightView d4Electorate ⟨0⟩
private theorem d4HeightLaws : FGHeightLaws d4Electorate d4Height := by
  let E := d4Electorate
  let cfg : FGConfig := ⟨0⟩
  refine {
    one_le_h := one_le_h E cfg
    h_mono := h_mono E cfg
    node_cases := derive_node_height_entry_cases E cfg
    entry_preceq := entry_preceq E cfg
    entry_same_height := entry_same_height E cfg
    entry_idem := entry_idem E cfg
    entry_plateau := entry_eq_on_plateau E cfg
    justified_preceq_entry := fun B => (chainOrder_derive E cfg B).justified_preceq_target
    justified_below_height := justified_below_height E cfg
    target_sub_progress := fun B => (derive_witnesses E cfg B).target_sub
    target_origin := ?_
    progress_origin := ?_
    height_crossing := height_crossing E cfg
    justification_certificate := justification_certificate E cfg }
  · intro B i hi
    obtain ⟨a, ⟨W, hW, ha⟩, hs, hm⟩ := (derive_witnesses E cfg B).target i hi
    exact ⟨W, a, hW, ha, hs, hm⟩
  · intro B i hi
    obtain ⟨a, ⟨W, hW, ha⟩, hs, hm⟩ := (derive_witnesses E cfg B).progress i hi
    exact ⟨W, a, hW, ha, hs, hm⟩
private theorem d4FreshChild :
    let Z : FGBlock (Fin 1) := .node d4E 4 ⟨47⟩ 13
      [⟨0, .vote 4 d4E.root false, none⟩]
    FGBlock.Preceq d4E Z ∧ (d4Height d4E).h < (d4Height Z).h := by
  decide +kernel
#print axioms d4HeightLaws
#print axioms d4FreshChild
private def d4Erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node P s root body _ => .node (d4Erase P) s root body
private def d4Phase (contested : Bool) : Store (Fin 1) :=
  ⟨if contested then {.genesis, d4A, d4B, d4C, d4D} else {.genesis, d4A, d4C},
    .genesis, d4A, 2, 3⟩
private def d4High (contested : Bool) : Store (Fin 1) :=
  ⟨if contested then {.genesis, d4A, d4B, d4C, d4D, d4E, d4F}
    else {.genesis, d4A, d4C, d4E}, .genesis, d4C, 3, 4⟩
private def d4Kind (contested : Bool) : PhaseKind := if contested then .contest else .topJ
private def d4Last (contested : Bool) : Time := if contested then 29 else 49

private abbrev d4Protocol (contested : Bool) (first : Store (Fin 1)) :
    V2.ProtocolSpecD Unit where
  State := Store (Fin 1)
  Label := Nat
  Duty := Nat
  signLabel := id
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := Store (Fin 1)
  init := first
  clock st _ := st
  actTime s := (s : Time)
  duties t := if 0 ≤ t then [t.toNat] else []
  duties_spec s t := by
    split
    · next ht =>
      simp only [List.mem_singleton]
      constructor
      · intro hs; subst s; exact Int.toNat_of_nonneg ht
      · intro hs; subst t; simp
    · next ht =>
      constructor
      · intro hm; cases hm
      · intro hs; exact False.elim (ht (hs ▸ Int.natCast_nonneg s))
  duties_nodup t := by split <;> simp
  act _ _ _ := none
  gossip _ _ := [d4Row]
  process _ o := if o.payload = d4StopRow then d4High contested else d4Phase contested
  selfVisible _ := false
  recordOwn st _ := st
  durable := id
  restore st _ := st
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private def d4Core (b : Bool) (first : Store (Fin 1)) :
    FGCoreReads (d4Protocol b first) 1 Unit Unit (Row (Fin 1)) where
  core nd := ⟨(), nd, [], []⟩
  erase := d4Erase
  source nd := if nd.h_max = 4 then some d4E else some d4C
  headVote nd _ := if nd.h_max = 4 then d4Erase d4E else d4Erase d4C
  finalityHead nd := if nd.h_max = 4 then some d4E else some d4C
  proposalFG _ _ := none
private def d4Safety (b : Bool) (first : Store (Fin 1)) :
    FGSafetyReads (d4Protocol b first) 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.none, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some d4C, ⟨3, d4C.root, 2⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private def d4Obs (b : Bool) (first : Store (Fin 1)) :
    FGObservationReads (d4Core b first) where
  height := d4Height
  finality _ := ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d4Height nd
  viable nd X := treeStoreFrameView d4Height nd X
private def d4Gate (b : Bool) (first : Store (Fin 1)) :
    FGAttemptGateReads (d4Protocol b first) where
  restartTime _ := none
  preClock st _ := st
  saved _ _ := none
  confirmation _ _ := none
  blocked _ _ := false
  writes _ _ := none
private def d4Interface (b : Bool) (first : Store (Fin 1)) :
    V2.D.Interface (d4Protocol b first) where
  confirmed st := d4Erase st.F
  stable st := d4Erase st.F
  block _ := none
  opening _ := True
  propLabel := id
  propDuty := id
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := Function.injective_id
private def d4Timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private abbrev d4Env : Generic.Env Unit := ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private def d4Trace (b : Bool) : V2.D.Run Unit (d4Protocol b Store.init) where
  honest := {()}
  horizon := d4Last b
  events := [.deliver () ⟨.none, d4Row⟩ 1, .tick () 6,
    .deliver () ⟨.none, d4StopRow⟩ (d4Last b)]
  seatOf _ _ := ()
  input _ _ := ()
private def d4Key (b : Bool) (task : AttemptTask) : AttemptKey :=
  ⟨0, 3, d4Kind b, task, false⟩

private theorem d4UnitExists (P : Unit → Prop) : (∃ x, P x) ↔ P () := by
  constructor
  · rintro ⟨x, h⟩
    cases x
    exact h
  · intro h
    exact ⟨(), h⟩

private theorem d4NonGenesis : d4C ≠ .genesis ∧ d4C.parent = d4A ∧
    d4C.root ≠ d4A.root ∧ d4Row.finality_pair = some ⟨0, genesisRoot⟩ := by
  decide +kernel
private theorem d4Front (b : Bool) :
    frontierAtIdx (d4Core b Store.init) d4Env (d4Trace b) 1 = 3 := by
  cases b <;> decide +kernel
private theorem d4StartEvent (b : Bool) :
    EffectiveEvent (d4Core b Store.init) d4Env (d4Trace b) (d4Obs b Store.init) 0 := by
  apply Or.inl
  cases b <;> decide +kernel
private theorem d4StopEvent (b : Bool) :
    EffectiveEvent (d4Core b Store.init) d4Env (d4Trace b) (d4Obs b Store.init) 2 := by
  apply Or.inl
  cases b <;> decide +kernel
private theorem d4TickQuiet (b : Bool) :
    ¬ EffectiveEvent (d4Core b Store.init) d4Env (d4Trace b) (d4Obs b Store.init) 1 := by
  cases b <;> simp only [EffectiveEvent, TopEvidence, ContestEvidence,
    d4Trace, Finset.mem_singleton, d4UnitExists] <;> decide +kernel
private theorem d4PhaseAt (b : Bool) :
    AttemptPhaseAt (d4Core b Store.init) d4Env (d4Trace b) (d4Obs b Store.init)
      1 3 (d4Kind b) := by
  cases b <;> simp only [AttemptPhaseAt, TopEvidence, ContestEvidence,
    d4Trace, Finset.mem_singleton, d4UnitExists, d4Kind, reduceCtorEq, ite_false,
      ite_true] <;> decide +kernel
private theorem d4Sent (b : Bool) :
    HonestRowAt (d4Safety b Store.init) d4Env (d4Trace b) d4Timing 1 () 0 d4Row := by
  refine ⟨(by change () ∈ ({()} : Finset Unit); decide), rfl, ?_⟩
  change (⟨.none, d4Row⟩ : (d4Protocol b Store.init).Object) ∈ [⟨.none, d4Row⟩]
  exact List.mem_singleton_self _
private theorem d4Valid (b : Bool) (task : AttemptTask) :
    AttemptValid (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing (d4Interface b Store.init) (d4Gate b Store.init)
      Row.height_pair 0 (d4Key b task) := by
  refine ⟨.deliver () ⟨.none, d4Row⟩ 1, rfl, (by change (0 : Time) ≤ 1; decide),
    Or.inl (d4StartEvent b), (d4Front b).symm, (by change 1 ≤ (3 : Nat); decide), d4PhaseAt b,
      ?_, ?_⟩
  · constructor
    · intro h; cases h
    · rintro ⟨s, Q, Qfg, hQ, _⟩
      obtain ⟨_, o, _, hb⟩ := hQ
      cases hb
  · intro _ j y r a h e hj ha _
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    cases ha.2.1

private theorem d4BudgetLower (k : AttemptKey) : 17 ≤ attemptBudget d4Timing 4 10 k := by
  rw [p0d4_attemptBudget_def]
  cases k.task <;> cases k.phase <;> decide +kernel

private theorem d4BoundedStart {b : Bool} {k : AttemptKey}
    {ev : V2.Event Unit (d4Protocol b Store.init).Object}
    (hv : AttemptValid (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing (d4Interface b Store.init) (d4Gate b Store.init)
      Row.height_pair 0 k)
    (hs : (d4Trace b).events[k.start]? = some ev)
    (hh : ev.time + attemptBudget d4Timing 4 10 k ≤ (d4Trace b).horizon) : k.start = 0 := by
  obtain ⟨ev0, hs0, _, hc, _⟩ := hv
  have he : ev0 = ev := Option.some.inj (hs0.symm.trans hs)
  subst ev0
  have hlen : k.start < 3 := (List.getElem?_eq_some_iff.mp hs).1
  by_cases hz : k.start = 0
  · exact hz
  rcases (show k.start = 1 ∨ k.start = 2 by omega) with hi | hi
  · have hev : ev = .tick () 6 := Option.some.inj (hs.symm.trans (by rw [hi]; rfl))
    subst ev
    rcases hc with heff | ⟨rG, _, hmin, ht, _⟩
    · rw [hi] at heff
      exact (d4TickQuiet b heff).elim
    · have hz : rG = 0 := Nat.eq_zero_of_le_zero
        (hmin 0 (by change (0 : Time) ≤ 6; decide))
      subst rG
      change (6 : Time) = 22 at ht
      cases ht
  · have hev : ev = .deliver () ⟨.none, d4StopRow⟩ (d4Last b) :=
      Option.some.inj (hs.symm.trans (by rw [hi]; rfl))
    have hp := d4BudgetLower k
    change ev.time + attemptBudget d4Timing 4 10 k ≤ d4Last b at hh
    rw [hev] at hh
    change d4Last b + attemptBudget d4Timing 4 10 k ≤ d4Last b at hh
    have hb : attemptBudget d4Timing 4 10 k ≤ 0 := by linarith only [hh]
    have hn := hp.trans hb
    norm_num at hn

private theorem d4FrontKey {b : Bool} {k : AttemptKey}
    (hv : AttemptValid (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing (d4Interface b Store.init) (d4Gate b Store.init)
      Row.height_pair 0 k) (hi : k.start = 0) : k.frontier = 3 := by
  obtain ⟨_, _, _, _, hf, _⟩ := hv
  rw [hi, d4Front] at hf
  exact hf

private theorem d4KindKey {b : Bool} {k : AttemptKey}
    (hv : AttemptValid (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing (d4Interface b Store.init) (d4Gate b Store.init)
      Row.height_pair 0 k) (hi : k.start = 0) : k.phase = d4Kind b := by
  have hf := d4FrontKey hv hi
  obtain ⟨_, _, _, _, _, _, hp, _⟩ := hv
  rw [hi, hf] at hp
  cases b <;> cases hkind : k.phase <;>
    simp only [AttemptPhaseAt, TopEvidence, ContestEvidence, d4Trace,
      Finset.mem_singleton, d4UnitExists, hkind, d4Kind, reduceCtorEq, ite_false, ite_true] at hp ⊢
  all_goals first | rfl | exact absurd hp (by decide +kernel)

private theorem d4End {b : Bool} {k : AttemptKey}
    {ev : V2.Event Unit (d4Protocol b Store.init).Object}
    (hv : AttemptValid (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing (d4Interface b Store.init) (d4Gate b Store.init)
      Row.height_pair 0 k)
    (hs : (d4Trace b).events[k.start]? = some ev)
    (hh : ev.time + attemptBudget d4Timing 4 10 k ≤ (d4Trace b).horizon) :
    AttemptEndsBy (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing Row.height_pair k (attemptBudget d4Timing 4 10 k) := by
  have hi := d4BoundedStart hv hs hh
  have hf := d4FrontKey hv hi
  have hp := d4KindKey hv hi
  have he : ev = .deliver () ⟨.none, d4Row⟩ 1 :=
    Option.some.inj (hs.symm.trans (by rw [hi]; rfl))
  subst ev
  cases ht : k.task with
  | raise =>
    apply healing_attempt_ends_of_event (d4Core b Store.init) (d4Safety b Store.init)
      d4Env (d4Trace b) (d4Obs b Store.init) d4Timing Row.height_pair hs
      (show k.start < 2 by omega) rfl ?_ (d4StopEvent b)
    rw [p0d4_attemptBudget_def, ht, hp]
    cases b <;> decide +kernel
  | firstRow =>
    apply healing_attempt_ends_of_row (d4Core b Store.init) (d4Safety b Store.init)
      d4Env (d4Trace b) (d4Obs b Store.init) d4Timing Row.height_pair hs
      (show k.start < 1 by omega) rfl ?_ ht (d4Sent b)
      (e := d4C.root)
    · rw [hf]; rfl
    · have hb := d4BudgetLower k
      change (6 : Time) ≤ 1 + attemptBudget d4Timing 4 10 k
      linarith only [hb]

private theorem d4Dispatch (b : Bool) (task : AttemptTask) :
    AttemptEndsBy (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing Row.height_pair (d4Key b task)
      (attemptBudget d4Timing 4 10 (d4Key b task)) := by
  -- A stop-constructor control; the four consumer functions are tested on the real producer.
  apply d4End (d4Valid b task) rfl
  cases b <;> cases task <;> decide +kernel

private theorem d4RaiseContest :
    AttemptEndsBy (d4Core true Store.init) (d4Safety true Store.init) d4Env (d4Trace true)
      (d4Obs true Store.init) d4Timing Row.height_pair (d4Key true .raise)
      (attemptBudget d4Timing 4 10 (d4Key true .raise)) := d4Dispatch true .raise
private theorem d4RaiseOther :
    AttemptEndsBy (d4Core false Store.init) (d4Safety false Store.init) d4Env (d4Trace false)
      (d4Obs false Store.init) d4Timing Row.height_pair (d4Key false .raise)
      (attemptBudget d4Timing 4 10 (d4Key false .raise)) := d4Dispatch false .raise
private theorem d4FirstContest :
    AttemptEndsBy (d4Core true Store.init) (d4Safety true Store.init) d4Env (d4Trace true)
      (d4Obs true Store.init) d4Timing Row.height_pair (d4Key true .firstRow)
      (attemptBudget d4Timing 4 10 (d4Key true .firstRow)) := d4Dispatch true .firstRow
private theorem d4FirstOther :
    AttemptEndsBy (d4Core false Store.init) (d4Safety false Store.init) d4Env (d4Trace false)
      (d4Obs false Store.init) d4Timing Row.height_pair (d4Key false .firstRow)
      (attemptBudget d4Timing 4 10 (d4Key false .firstRow)) := d4Dispatch false .firstRow

#print axioms d4NonGenesis
#print axioms d4RaiseContest
#print axioms d4RaiseOther
#print axioms d4FirstContest
#print axioms d4FirstOther
#print axioms d4BoundedStart
#print axioms d4TickQuiet
#print axioms d4Sent

-- The row at index 1 is the first permitted later witness.
private theorem d4EarliestRow (b : Bool) :
    (d4Key b .firstRow).start + 1 = 1 ∧
    HonestRowAt (d4Safety b Store.init) d4Env (d4Trace b) d4Timing 1 () 0 d4Row :=
  ⟨rfl, d4Sent b⟩

-- The effective event lies at the inclusive contest deadline.
private theorem d4InclusiveDeadline :
    d4Last true = 1 + attemptBudget d4Timing 4 10 (d4Key true .raise) := by
  decide +kernel

private theorem d4NoZeroBudget (b : Bool) (task : AttemptTask) :
    ¬ AttemptEndsBy (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4Trace b)
      (d4Obs b Store.init) d4Timing Row.height_pair (d4Key b task) 0 := by
  rintro ⟨ev, hi, j, ev', hj, hn, ht, _⟩
  have he : ev = .deliver () ⟨.none, d4Row⟩ 1 := Option.some.inj hi.symm
  subst ev
  have hlen : j < 3 := (List.getElem?_eq_some_iff.mp hn).1
  change 0 < j at hj
  rcases (show j = 1 ∨ j = 2 by omega) with hj | hj <;> subst j
  · have he' : ev' = .tick () 6 := Option.some.inj hn.symm
    subst ev'
    change (6 : Time) ≤ 1 + 0 at ht
    exact (by decide : ¬ (6 : Time) ≤ 1 + 0) ht
  · have he' : ev' = .deliver () ⟨.none, d4StopRow⟩ (d4Last b) :=
      Option.some.inj hn.symm
    subst ev'
    cases b
    · change (49 : Time) ≤ 1 at ht
      exact (by decide : ¬ (49 : Time) ≤ 1) ht
    · change (29 : Time) ≤ 1 at ht
      exact (by decide : ¬ (29 : Time) ≤ 1) ht

private theorem d4WrongRowName (e : BlockId) :
    namedEntry d4Row.height_pair ≠ some (4, e) := by
  intro h
  have he : some (3 : Nat) = some 4 := congrArg (fun x => x.map Prod.fst) h
  have hn : (3 : Nat) = 4 := Option.some.inj he
  omega

private def d4InclusiveTrace (b : Bool) :
    V2.D.Run Unit (d4Protocol b (d4Phase b)) where
  honest := {()}
  horizon := 80
  events := [.deliver () ⟨.none, d4Row⟩ 22, .tick () 30]
  seatOf _ _ := ()
  input _ _ := ()

private theorem d4InclusiveQuiet (b : Bool) :
    ¬ EffectiveEvent (d4Core b (d4Phase b)) d4Env (d4InclusiveTrace b)
      (d4Obs b (d4Phase b)) 0 := by
  cases b <;> simp only [EffectiveEvent, TopEvidence, ContestEvidence,
    d4InclusiveTrace, Finset.mem_singleton, d4UnitExists] <;> decide +kernel

private theorem d4InclusiveValid (b : Bool) :
    AttemptValid (d4Core b (d4Phase b)) (d4Safety b (d4Phase b)) d4Env
      (d4InclusiveTrace b) (d4Obs b (d4Phase b)) d4Timing (d4Interface b (d4Phase b))
      (d4Gate b (d4Phase b)) Row.height_pair 0 (d4Key b .firstRow) := by
  refine ⟨.deliver () ⟨.none, d4Row⟩ 22, rfl, (by change (0 : Time) ≤ 22; decide),
    Or.inr ⟨0, by decide, fun r _ => Nat.zero_le r, rfl, rfl⟩,
    ?_, (by change 1 ≤ (3 : Nat); decide), ?_, ?_, ?_⟩
  · cases b <;> decide +kernel
  · cases b <;> simp only [AttemptPhaseAt, TopEvidence, ContestEvidence,
      d4InclusiveTrace, Finset.mem_singleton, d4UnitExists, d4Key, d4Kind, reduceCtorEq,
        ite_false, ite_true] <;> decide +kernel
  · constructor
    · intro h; cases h
    · rintro ⟨s, Q, Qfg, hQ, _⟩
      obtain ⟨_, o, _, hb⟩ := hQ
      cases hb
  · intro _ j y r a h e hj ha _
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    cases ha.2.1

private theorem d4InclusiveStartArm (b : Bool) :
    ∃ ev rG, (d4InclusiveTrace b).events[(d4Key b .firstRow).start]? = some ev ∧
      0 ≤ ev.time ∧ 0 ≤ d4Timing.action rG ∧
      (∀ r, 0 ≤ d4Timing.action r → rG ≤ r) ∧
      ev.time = d4Timing.action (rG + 2) ∧
      timeIdx (d4InclusiveTrace b) (d4Timing.action (rG + 2)) =
        (d4Key b .firstRow).start + 1 :=
  healing_attempt_inclusive_start (d4Core b (d4Phase b)) (d4Safety b (d4Phase b))
    d4Env (d4InclusiveTrace b) (d4Obs b (d4Phase b)) d4Timing (d4Interface b (d4Phase b))
    (d4Gate b (d4Phase b)) Row.height_pair 0 (d4InclusiveValid b) (d4InclusiveQuiet b)

private theorem d4InclusiveRowStop (b : Bool) :
    AttemptEndsBy (d4Core b (d4Phase b)) (d4Safety b (d4Phase b)) d4Env
      (d4InclusiveTrace b) (d4Obs b (d4Phase b)) d4Timing Row.height_pair
      (d4Key b .firstRow) 8 := by
  apply healing_attempt_ends_of_row (d4Core b (d4Phase b)) (d4Safety b (d4Phase b))
    d4Env (d4InclusiveTrace b) (d4Obs b (d4Phase b)) d4Timing Row.height_pair
    (j := 1) (y := ()) (r := 3) (a := d4Row) (e := d4C.root)
    rfl (by change 0 < (1 : Nat); decide) rfl (by change (30 : Time) ≤ 22 + 8; decide) rfl
  · refine ⟨(by change () ∈ ({()} : Finset Unit); decide), rfl, ?_⟩
    change (⟨.none, d4Row⟩ : (d4Protocol b (d4Phase b)).Object) ∈ [⟨.none, d4Row⟩]
    exact List.mem_singleton_self _
  · rfl

private def d4EarlyTrace (b : Bool) : V2.D.Run Unit (d4Protocol b Store.init) where
  honest := {()}
  horizon := 80
  events := [.deliver () ⟨.none, d4Row⟩ 1, .deliver () ⟨.none, d4StopRow⟩ 2]
  seatOf _ _ := ()
  input _ _ := ()

private theorem d4EarliestEvent (b : Bool) :
    EffectiveEvent (d4Core b Store.init) d4Env (d4EarlyTrace b) (d4Obs b Store.init)
      ((d4Key b .raise).start + 1) := by
  apply Or.inl
  cases b <;> decide +kernel

private theorem d4EarliestEventStop (b : Bool) :
    AttemptEndsBy (d4Core b Store.init) (d4Safety b Store.init) d4Env (d4EarlyTrace b)
      (d4Obs b Store.init) d4Timing Row.height_pair (d4Key b .raise) 1 := by
  exact healing_attempt_ends_of_event (d4Core b Store.init) (d4Safety b Store.init)
    d4Env (d4EarlyTrace b) (d4Obs b Store.init) d4Timing Row.height_pair
    rfl (by change 0 < (1 : Nat); decide) rfl (by change (2 : Time) ≤ 1 + 1; decide)
    (d4EarliestEvent b)

#print axioms d4EarliestEvent
#print axioms d4EarliestEventStop

private theorem d4NoStartAsStop : ¬ (d4Key true .raise).start < 0 := by decide

#print axioms d4EarliestRow
#print axioms d4InclusiveDeadline
#print axioms d4NoZeroBudget
#print axioms d4WrongRowName
#print axioms d4InclusiveQuiet
#print axioms d4InclusiveValid
#print axioms d4InclusiveStartArm
#print axioms d4InclusiveRowStop
#print axioms d4NoStartAsStop

end AvailableChain.FGCompose.Tests.P0d4
end
