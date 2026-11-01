module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchBudget
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d5a
open AvailableChain.SimplexFG AvailableChain.KitFG

-- These are inhabited event-fold interface tests, not ExecutionValid claims.
-- The trace emits a signed row, has a quiet tick, and then raises the frontier.
private def d5A : FGBlock (Fin 1) := .node .genesis 1 ⟨41⟩ 7 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d5B : FGBlock (Fin 1) := .node .genesis 1 ⟨42⟩ 8 [⟨0, .vote 1 genesisRoot false, none⟩]
private def d5C : FGBlock (Fin 1) := .node d5A 2 ⟨43⟩ 9 [⟨0, .vote 2 d5A.root false, none⟩]
private def d5D : FGBlock (Fin 1) := .node d5B 2 ⟨44⟩ 10 [⟨0, .vote 2 d5B.root false, none⟩]
private def d5E : FGBlock (Fin 1) := .node d5C 3 ⟨45⟩ 11 [⟨0, .vote 3 d5C.root false, none⟩]
private def d5F : FGBlock (Fin 1) := .node d5D 3 ⟨46⟩ 12 [⟨0, .vote 3 d5D.root false, none⟩]
private def d5Row : Row (Fin 1) := ⟨0, .vote 3 d5C.root false, some ⟨0, genesisRoot⟩⟩
private def d5StopRow : Row (Fin 1) := ⟨0, .vote 4 d5E.root true, some ⟨1, d5A.root⟩⟩
private def d5Electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def d5Height : FGHeightView (Fin 1) := simplexHeightView d5Electorate ⟨0⟩
private def d5Erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node P s root body _ => .node (d5Erase P) s root body
private def d5Phase (contested : Bool) : Store (Fin 1) :=
  ⟨if contested then {.genesis, d5A, d5B, d5C, d5D} else {.genesis, d5A, d5C},
    .genesis, d5A, 2, 3⟩
private def d5High (contested : Bool) : Store (Fin 1) :=
  ⟨if contested then {.genesis, d5A, d5B, d5C, d5D, d5E, d5F}
    else {.genesis, d5A, d5C, d5E}, .genesis, d5C, 3, 4⟩
private def d5Kind (contested : Bool) : PhaseKind := if contested then .contest else .topJ
private def d5Last (contested : Bool) : Time := if contested then 29 else 49

private abbrev d5Protocol (contested : Bool) (first : Store (Fin 1)) :
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
  gossip _ _ := [d5Row]
  process _ o := if o.payload = d5StopRow then d5High contested else d5Phase contested
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

private def d5Core (b : Bool) (first : Store (Fin 1)) :
    FGCoreReads (d5Protocol b first) 1 Unit Unit (Row (Fin 1)) where
  core nd := ⟨(), nd, [], []⟩
  erase := d5Erase
  source nd := if nd.h_max = 4 then some d5E else some d5C
  headVote nd _ := if nd.h_max = 4 then d5Erase d5E else d5Erase d5C
  finalityHead nd := if nd.h_max = 4 then some d5E else some d5C
  proposalFG _ _ := none
private def d5Safety (b : Bool) (first : Store (Fin 1)) :
    FGSafetyReads (d5Protocol b first) 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.none, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some d5C, ⟨3, d5C.root, 2⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private def d5Obs (b : Bool) (first : Store (Fin 1)) :
    FGObservationReads (d5Core b first) where
  height := d5Height
  finality _ := ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d5Height nd
  viable nd X := treeStoreFrameView d5Height nd X
private def d5Timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private abbrev d5Env : Generic.Env Unit := ⟨6, by decide, 0, by decide, fun _ t =>
    decide (t = 1 ∨ t = 6 ∨ t = 29 ∨ t = 49)⟩
private def d5Trace (b : Bool) : V2.D.Run Unit (d5Protocol b Store.init) where
  honest := {()}
  horizon := d5Last b
  events := [.deliver () ⟨.none, d5Row⟩ 1, .tick () 6,
    .deliver () ⟨.none, d5StopRow⟩ (d5Last b)]
  seatOf _ _ := ()
  input _ _ := ()
private theorem d5UnitExists (P : Unit → Prop) : (∃ x, P x) ↔ P () := by
  constructor
  · rintro ⟨x, h⟩
    cases x
    exact h
  · intro h
    exact ⟨(), h⟩

private theorem d5NonGenesis : d5C ≠ .genesis ∧ d5C.parent = d5A ∧
    d5C.root ≠ d5A.root ∧ d5Row.finality_pair = some ⟨0, genesisRoot⟩ := by
  decide +kernel
private theorem d5Front (b : Bool) :
    frontierAtIdx (d5Core b Store.init) d5Env (d5Trace b) 1 = 3 := by
  cases b <;> decide +kernel
private theorem d5StartEvent (b : Bool) :
    EffectiveEvent (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init) 0 := by
  apply Or.inl
  cases b <;> decide +kernel
private theorem d5StopEvent (b : Bool) :
    EffectiveEvent (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init) 2 := by
  apply Or.inl
  cases b <;> decide +kernel
private theorem d5TickQuiet (b : Bool) :
    ¬ EffectiveEvent (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init) 1 := by
  cases b <;> simp only [EffectiveEvent, TopEvidence, ContestEvidence,
    d5Trace, Finset.mem_singleton, d5UnitExists] <;> decide +kernel
private theorem d5PhaseAt (b : Bool) :
    AttemptPhaseAt (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init)
      1 3 (d5Kind b) := by
  cases b <;> simp only [AttemptPhaseAt, TopEvidence, ContestEvidence,
    d5Trace, Finset.mem_singleton, d5UnitExists, d5Kind, reduceCtorEq, ite_false,
      ite_true] <;> decide +kernel
private theorem d5Sent (b : Bool) :
    HonestRowAt (d5Safety b Store.init) d5Env (d5Trace b) d5Timing 1 () 0 d5Row := by
  refine ⟨(by change () ∈ ({()} : Finset Unit); decide), rfl, ?_⟩
  change (⟨.none, d5Row⟩ : (d5Protocol b Store.init).Object) ∈ [⟨.none, d5Row⟩]
  exact List.mem_singleton_self _

private theorem d5TimingLaws : FGTimingLaws d5Timing where
  delta_pos := by decide
  rounds := by decide
  proposal_eq s := by simp [d5Timing]
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [d5Timing]; ring

private theorem d5Schedule (b : Bool) : V2.D.ScheduleWellFormed d5Env (d5Trace b) where
  horizon_nonneg := by cases b <;> decide
  sorted := by cases b <;> decide
  nodup := by cases b <;> decide
  in_horizon := by
    intro e he
    simp only [d5Trace, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> cases b <;> decide
  honest_only := by intro e he; simp [d5Trace]
  tick_public := by
    intro v t ht
    have ht' : t = 6 := by simpa [d5Trace] using ht
    subst t
    exact ⟨1, rfl⟩
  tick_total := by
    intro v hv t ht hn hh ha
    obtain ⟨k, hk⟩ := ht
    change t = (k : Time) * 6 at hk
    have ha' : t = 1 ∨ t = 6 ∨ t = 29 ∨ t = 49 := of_decide_eq_true ha
    have ht6 : t = 6 := by
      simp only [Time] at *
      omega
    subst t
    cases v
    simp only [d5Trace, List.mem_cons, V2.Event.tick.injEq, reduceCtorEq,
      false_or]
    exact Or.inl ⟨True.intro, ht6⟩


private theorem d5FirstEvent (b : Bool) :
    FirstEffectiveBy (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init)
      0 (d5Last b) := by
  refine ⟨2, .deliver () ⟨.none, d5StopRow⟩ (d5Last b), by decide, rfl,
    le_rfl, d5StopEvent b, ?_⟩
  intro k hk0 hk2
  have hk : k = 1 := by omega
  subst k
  exact d5TickQuiet b

private theorem d5SplitAtDeadline (b : Bool) :
    FirstEffectiveBy (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init)
      0 (d5Last b) := by
  rcases frontierSearch_first_effective_split (d5Core b Store.init) d5Env (d5Trace b)
    (d5Obs b Store.init) (d5Schedule b) 0 (d5Last b) with he | hnone
  · exact he
  · exact (hnone 2 (by decide) (by cases b <;> decide) (d5StopEvent b)).elim

private theorem d5InclusiveEvent (b : Bool) :
    (.deliver () ⟨.none, d5StopRow⟩ (d5Last b) :
      V2.Event Unit (d5Protocol b Store.init).Object).time ≤ d5Last b :=
  frontierSearch_event_time_le d5Env (d5Trace b) (d5Schedule b) (j := 2) rfl
    (by cases b <;> decide)

private theorem d5FirstRise (b : Bool) :
    FrontierRiseBy (d5Core b Store.init) d5Env (d5Trace b) 0 3 (d5Last b) := by
  apply frontierSearch_first_rise _ _ _ (d5Schedule b)
  · refine ⟨2, by decide, ?_, ?_⟩
    · cases b <;> decide
    · cases b <;> decide +kernel
  · exact (d5Front b).le

private theorem d5NoEarlierEvent (b : Bool) :
    ¬ FirstEffectiveBy (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init)
      0 (d5Last b - 1) := by
  rintro ⟨j, ev, hij, hj, ht, he, _⟩
  have hj3 : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
  have hcases : j = 1 ∨ j = 2 := by omega
  rcases hcases with rfl | rfl
  · exact d5TickQuiet b he
  · have hev : ev = .deliver () ⟨.none, d5StopRow⟩ (d5Last b) :=
      Option.some.inj (hj.symm.trans rfl)
    rw [hev] at ht
    change d5Last b ≤ d5Last b - 1 at ht
    linarith only [ht]

private theorem d5NoStartAsStop (b : Bool) :
    ¬ FirstEffectiveBy (d5Core b Store.init) d5Env (d5Trace b) (d5Obs b Store.init) 0 1 := by
  intro h
  apply d5NoEarlierEvent b
  obtain ⟨j, ev, hij, hj, ht, he, hf⟩ := h
  exact ⟨j, ev, hij, hj, ht.trans (by cases b <;> decide), he, hf⟩

private theorem d5FirstRow (b : Bool) :
    FirstHeightRowBy (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      Row.height_pair 3 6 := by
  apply frontierSearch_first_row _ _ _ _ _ d5TimingLaws
  · exact ⟨1, (), d5Row, d5C.root, d5Sent b, rfl⟩
  · exact le_rfl

private theorem d5UniqueFirstRow (b : Bool) {r r' : Nat}
    (hr : HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) r 3)
    (hf : ∀ s, HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) s 3 → r ≤ s)
    (hr' : HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) r' 3)
    (hf' : ∀ s, HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) s 3 → r' ≤ s) : r = r' :=
  frontierSearch_first_row_unique _ _ _ _ _ hr hf hr' hf'

private theorem d5SelectedFirstRow (b : Bool) :
    ∃ r, HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) r 3 ∧ r = 0 := by
  obtain ⟨r, hr, hf, _⟩ := d5FirstRow b
  have hrow0 : HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) 0 3 :=
    ⟨1, (), d5Row, d5C.root, d5Sent b, rfl⟩
  exact ⟨r, hr, d5UniqueFirstRow b hr hf hrow0 (fun s _ => Nat.zero_le s)⟩

-- A height-3 row exists at the first tick; there is no height-2 row at any tick.
private theorem d5SkippedHeight (b : Bool) :
    HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) 0 3 ∧
    ¬ ∃ r, HeightRow (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      (fun a => namedEntry a.height_pair) r 2 := by
  refine ⟨⟨1, (), d5Row, d5C.root, d5Sent b, rfl⟩, ?_⟩
  rintro ⟨r, j, y, a, e, ⟨_, hj, ha⟩, hn⟩
  have hjlen : j < 3 := (List.getElem?_eq_some_iff.mp hj).1
  have hj1 : j = 1 := by
    interval_cases j <;> simp_all [d5Trace, V2.Event.tick.injEq]
  subst j
  have hevent : (6 : Time) = d5Timing.action r := by
    simpa [d5Trace] using hj
  have hr0 : r = 0 := by
    change (6 : Time) = 8 * (r : Time) + 6 at hevent
    have hz : (r : Time) = 0 := by linarith only [hevent]
    exact_mod_cast hz
  subst r
  have ha' : a = d5Row := by
    change (⟨.none, a⟩ : (d5Protocol b Store.init).Object) ∈ [⟨.none, d5Row⟩] at ha
    simpa using ha
  subst a
  cases hn

-- The cap model sends the two actual rows before a jump from height 1 to height 3.
private def d5CapOne : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private def d5CapTwo : Row (Fin 1) := ⟨0, .vote 2 d5A.root true, none⟩
private abbrev d5CapProtocol : V2.ProtocolSpecD Unit :=
  { d5Protocol false Store.init with gossip := fun _ _ => [d5CapOne, d5CapTwo] }
private noncomputable def d5CapCore : FGCoreReads d5CapProtocol 1 Unit Unit (Row (Fin 1)) where
  core nd := ⟨(), nd, [], []⟩
  erase := d5Erase
  source _ := some d5C
  headVote _ _ := d5Erase d5C
  finalityHead _ := some d5C
  proposalFG _ _ := none
private noncomputable def d5CapSafety : FGSafetyReads d5CapProtocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode a := ⟨.none, a⟩
  decode := some
  decodeObject o := some o.payload
  fgLabel := 0
  fgSeats := Equiv.refl _
  record _ := RecordOnce.initial
  inputs _ := (some d5C, ⟨3, d5C.root, 2⟩)
  enabled _ := true
  finalizedOut _ := .genesis
private noncomputable def d5CapObs : FGObservationReads d5CapCore where
  height := d5Height
  finality _ := ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d5Height nd
  viable nd X := treeStoreFrameView d5Height nd X
private abbrev d5CapEnv : Generic.Env Unit :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private noncomputable def d5CapTrace : V2.D.Run Unit d5CapProtocol where
  honest := {()}
  horizon := 7
  events := [.tick () 6, .deliver () ⟨.none, d5Row⟩ 7]
  seatOf _ _ := ()
  input _ _ := ()
private theorem d5CapSent :
    HonestRowAt d5CapSafety d5CapEnv d5CapTrace d5Timing 0 () 0 d5CapOne ∧
    HonestRowAt d5CapSafety d5CapEnv d5CapTrace d5Timing 0 () 0 d5CapTwo := by
  constructor <;> refine ⟨(by decide), rfl, ?_⟩
  · change (⟨.none, d5CapOne⟩ : d5CapProtocol.Object) ∈
      [⟨.none, d5CapOne⟩, ⟨.none, d5CapTwo⟩]
    simp
  · change (⟨.none, d5CapTwo⟩ : d5CapProtocol.Object) ∈
      [⟨.none, d5CapOne⟩, ⟨.none, d5CapTwo⟩]
    simp
private theorem d5CapState (i : Nat) :
    d5CapTrace.stateBefore d5CapEnv (i + 2) () = d5Phase false := by
  simp [V2.D.Run.stateBefore, d5CapTrace, d5CapProtocol,
    d5Protocol, d5CapEnv, V2.D.World.step, V2.D.World.init,
    d5Row, d5StopRow]
private theorem d5CapLaw :
    RCap d5CapCore d5CapSafety d5CapEnv d5CapTrace d5CapObs d5Timing
      (fun a => namedEntry a.height_pair) (fun _ _ => [d5CapOne, d5CapTwo]) := by
  intro y i x W hW hskip
  simp only [Height] at hskip
  cases x
  rcases i with _ | _ | i
  · have hw : W = .genesis := by simpa [HeldAt, d5CapCore, d5CapTrace,
        V2.D.Run.stateBefore, V2.D.World.init,
        d5CapProtocol, d5Protocol, Store.init] using hW.2
    subst W
    have : (d5CapObs.height .genesis).h = 1 := by decide +kernel
    rw [this] at hskip
    omega
  · have hw : W = .genesis := by simpa [HeldAt, d5CapCore, d5CapTrace,
        V2.D.Run.stateBefore, V2.D.World.init,
        V2.D.World.step, V2.D.tick, d5CapEnv, d5CapProtocol, d5Protocol, Store.init,
        V2.ProtocolSpecD.objSelfVisible] using hW.2
    subst W
    have : (d5CapObs.height .genesis).h = 1 := by decide +kernel
    rw [this] at hskip
    omega
  · have hw : W = .genesis ∨ W = d5A ∨ W = d5C := by
      simpa [d5CapCore, d5CapState, d5Phase, Finset.mem_insert, Finset.mem_singleton]
        using hW.2
    rcases hw with rfl | rfl | rfl
    · have : (d5CapObs.height .genesis).h = 1 := by decide +kernel
      rw [this] at hskip
      omega
    · have : (d5CapObs.height d5A).h = 2 := by decide +kernel
      rw [this] at hskip
      have hy : y = 0 := by simp only [Height] at *; omega
      subst y
      exact ⟨0, (), 0, d5CapOne, genesisRoot, by omega, d5CapSent.1, rfl, by simp⟩
    · have : (d5CapObs.height d5C).h = 3 := by decide +kernel
      rw [this] at hskip
      have hy : y = 0 ∨ y = 1 := by simp only [Height] at *; omega
      rcases hy with rfl | rfl
      · exact ⟨0, (), 0, d5CapOne, genesisRoot, by omega, d5CapSent.1, rfl, by simp⟩
      · exact ⟨0, (), 0, d5CapTwo, d5A.root, by omega, d5CapSent.2, rfl, by simp⟩
private theorem d5CapSkippedRow :
    ∃ j z r a e, j < 2 ∧ HonestRowAt d5CapSafety d5CapEnv d5CapTrace d5Timing j z r a ∧
      namedEntry a.height_pair = some (2, e) := by
  apply frontierSearch_skipped_row d5CapCore d5CapSafety d5CapEnv d5CapTrace d5CapObs
    d5Timing Row.height_pair (fun _ _ => [d5CapOne, d5CapTwo]) d5CapLaw
    (W := d5C) (x := ())
  · refine ⟨(by decide), ?_⟩
    change d5C ∈ (d5CapTrace.stateBefore d5CapEnv (0 + 2) ()).TF
    rw [d5CapState]
    simp [d5Phase]
  · decide +kernel

private def d5Empty : V2.D.Run Unit (d5Protocol false Store.init) :=
  { d5Trace false with events := [], horizon := 0 }
private theorem d5EmptySchedule : V2.D.ScheduleWellFormed d5Env d5Empty where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by simp [d5Empty]
  honest_only := by simp [d5Empty]
  tick_public := by simp [d5Empty]
  tick_total := by
    intro v hv t ht hn hh ha
    have hz : t = 0 := by
      change t ≤ 0 at hh
      exact le_antisymm hh hn
    subst t
    change decide ((0 : Time) = 1 ∨ 0 = 6 ∨ 0 = 29 ∨ 0 = 49) = true at ha
    contradiction
private theorem d5EmptySplit :
    ∀ j, 0 < j → j < timeIdx d5Empty 0 →
      ¬ EffectiveEvent (d5Core false Store.init) d5Env d5Empty
        (d5Obs false Store.init) j := by
  rcases frontierSearch_first_effective_split (d5Core false Store.init) d5Env d5Empty
    (d5Obs false Store.init) d5EmptySchedule 0 0 with he | hnone
  · obtain ⟨j, ev, _, hj, _⟩ := he
    simp [d5Empty] at hj
  · exact hnone
private theorem d5EmptyNoRow :
    ¬ FirstHeightRowBy (d5Safety false Store.init) d5Env d5Empty d5Timing
      Row.height_pair 3 100 := by
  rintro ⟨_, ⟨j, y, a, e, ⟨_, hj, _⟩, _⟩, _⟩
  simp [d5Empty] at hj

private theorem d5NoEarlyRow (b : Bool) :
    ¬ FirstHeightRowBy (d5Safety b Store.init) d5Env (d5Trace b) d5Timing
      Row.height_pair 3 5 := by
  rintro ⟨r, _, _, ht⟩
  change 8 * (r : Time) + 6 ≤ 5 at ht
  linarith only [ht, Int.natCast_nonneg r]

private theorem d5TerminalPositive :
    (19 : Time) ≤ 0 + (3 * FGCompose.P d5Timing + Γ d5Timing 8 - 13 * d5Timing.delta) ∧
    (23 : Time) ≤ 0 + (3 * FGCompose.P d5Timing + Γ d5Timing 12 - 13 * d5Timing.delta) :=
  ⟨frontierSearch_terminal_opening_cost d5Timing 8 0 4 19 (by decide) (by decide),
    frontierSearch_terminal_opening_cost d5Timing 12 0 4 23 (by decide) (by decide)⟩
private theorem d5TerminalNegative8 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 8 - 9) ≤ horizon → a + 2 * 8 + 8 - 9 ≤ horizon) :=
  frontierSearch_terminal_horizon_gap8
private theorem d5TerminalNegative12 :
    ¬ (∀ d a horizon : Int, d ≤ a → a ≤ d + (8 - 4) →
      d + (2 * 8 + 12 - 9) ≤ horizon → a + 2 * 8 + 12 - 9 ≤ horizon) :=
  frontierSearch_terminal_horizon_gap12

#print axioms d5NonGenesis
#print axioms d5FirstRise
#print axioms d5SplitAtDeadline
#print axioms d5FirstEvent
#print axioms d5InclusiveEvent
#print axioms d5NoEarlierEvent
#print axioms d5NoStartAsStop
#print axioms d5NoEarlyRow
#print axioms d5FirstRow
#print axioms d5SelectedFirstRow
#print axioms d5UniqueFirstRow
#print axioms d5CapSkippedRow
#print axioms d5SkippedHeight
#print axioms d5EmptySplit
#print axioms d5EmptyNoRow
#print axioms d5TerminalPositive
#print axioms d5TerminalNegative8
#print axioms d5TerminalNegative12
end AvailableChain.FGCompose.Tests.P0d5a
end
