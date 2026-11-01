module
public import AvailableChainFGCompose.Proofs.Population.PromotionRows
public import AvailableChainFGCompose.Proofs.Population.PromotionBridges

set_option linter.privateModule false

noncomputable section
public section

/-! Generic ordinary-event-fold controls. These are not concrete PC executions.
The FG label is 6; seat 0 belongs to 9. Honest nonholder 7 also has an action cut
and later carrier cuts, but never emits an encoded FG wire. -/
namespace AvailableChain.FGCompose.Tests.PopulationPromotion
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate (n : Nat) : Electorate (Fin n) :=
  ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev head : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := RecordOnce
  Label := Time
  Duty := Time
  signLabel := id
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := RecordOnce
  init := RecordOnce.initial
  clock := fun st _ => st
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun st _ _ => (createRowOnce (electorate 1) cfg st 0 (some .genesis) head).1
  gossip := fun _ _ => [row]
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st o => match o.auth with
    | .none => st
    | .seat _ _ => record_row_once st o.payload
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.auth with
  | .seat l _ => if l = 6 then some o.payload else none
  | .none => none
private abbrev reads : FGSafetyReads protocol 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := fun a => ⟨.seat 6 0, a⟩
  decode := some
  decodeObject := decode
  fgLabel := 6
  fgSeats := Equiv.refl _
  record := id
  inputs := fun _ => (some .genesis, head)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis
private abbrev env : Generic.Env Nat where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true
private abbrev run : V2.D.Run Nat protocol where
  honest := {7, 9}
  horizon := 20
  events := [.tick 9 6, .tick 7 6, .tick 7 8, .tick 7 12]
  seatOf := fun l _ => if l = 6 then 9 else 7
  input := fun _ _ => ()
private noncomputable abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6
private abbrev core : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), Store.init, [], []⟩
  erase := fun _ => .genesis
  source := fun _ => some .genesis
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => some .genesis
  proposalFG := fun _ _ => none
private noncomputable abbrev height : FGHeightView (Fin 1) :=
  fun _ => ⟨.genesis, 0, 1, .genesis, ∅, ∅, 0, .genesis⟩
private theorem height_premises_sat : FGHeightLaws (electorate 1) height where
  one_le_h _ := by change 1 ≤ (1 : Nat); decide
  h_mono _ := le_rfl
  node_cases _ _ _ _ _ := Or.inl ⟨rfl, rfl⟩
  entry_preceq B := genesis_preceq B
  entry_same_height _ := rfl
  entry_idem _ := rfl
  entry_plateau _ _ := rfl
  justified_preceq_entry _ := preceq_refl _
  justified_below_height _ := by change 0 < (1 : Nat); decide
  target_sub_progress _ := Finset.Subset.refl _
  target_origin _ _ hi := False.elim (Finset.notMem_empty _ hi)
  progress_origin _ _ hi := False.elim (Finset.notMem_empty _ hi)
  height_crossing _ y hy hlo := by
    change y < 1 at hlo
    exact ((Nat.not_lt_of_ge hy) hlo).elim
  justification_certificate _ hn := False.elim (hn rfl)


#print axioms height_premises_sat

private theorem mixed_premises_sat :
    run.honest = {7, 9} ∧ run.horizon = 20 ∧
    run.events = [.tick 9 6, .tick 7 6, .tick 7 8, .tick 7 12] ∧
    (∀ i, safetyHolder reads run i = 9) ∧ FGHonestSeats reads run = {0} ∧
    protocol.objSelfVisible (reads.encode row) = true ∧
    reads.decodeObject (reads.encode row) = some row ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    (∀ x ∈ run.honest,
      actionSourceFG core env run timing x 0 = some (some .genesis)) ∧
    OpeningEntry core env run height timing 0 1 ∧
    OpeningCoveredFG core reads env run height timing Row.height_pair
      (FGHonestSeats reads run) 0 .genesis := by
  refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, run]
  · unfold HonestRowAt
    decide +kernel
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · exact ⟨genesisRoot, fun _ _ _ _ => ⟨rfl, rfl⟩⟩
  · intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨.genesis, RecordOnce.initial, 0, 0, row, ?_, ?_, ?_, ?_, le_rfl, ?_, rfl⟩
    · rfl
    · decide +kernel
    · decide
    · decide
    · unfold HonestRowAt
      decide +kernel

#print axioms mixed_premises_sat

private theorem geometry_premises_sat :
    (∀ x y K L, x ∈ run.honest → y ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) →
      actionSourceFG core env run timing y 0 = some (some L) →
      (height K).T_h.root = (height L).T_h.root → (height K).T_h = (height L).T_h) ∧
    (∀ x K, x ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) → K.slot ≤ 0 * timing.roundSlots) ∧
    (∀ x K U, x ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) → FGBlock.Preceq U K →
      U.slot ≤ K.slot) := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ => rfl, ?_, ?_⟩
  · intro x K hx hK
    have he := mixed_premises_sat.2.2.2.2.2.2.2.2.1 x hx
    have hk : K = .genesis := Option.some.inj (Option.some.inj (hK.symm.trans he))
    subst K
    exact le_rfl
  · intro x K U hx hK hUK
    have he := mixed_premises_sat.2.2.2.2.2.2.2.2.1 x hx
    have hk : K = .genesis := Option.some.inj (Option.some.inj (hK.symm.trans he))
    subst K
    have hu : U = .genesis := by simpa [FGBlock.Preceq, FGBlock.preceq] using hUK
    subst U
    exact le_rfl

#print axioms geometry_premises_sat

private theorem mixed_fixed_rows :
    EntryAt height (.genesis : FGBlock (Fin 1)) 1 ∧
    FixedRowsFG core reads env run height timing Row.height_pair
      (FGHonestSeats reads run) 0 1 .genesis .genesis := by
  have hH := mixed_premises_sat.2.2.2.2.1
  have hne : (FGHonestSeats reads run).Nonempty := by rw [hH]; exact ⟨0, by simp⟩
  obtain ⟨U, hU, _, rows⟩ := healing_promotion_bounded_rows_holder core reads env run
    height timing Row.height_pair (electorate 1) height_premises_sat
    (Finset.Subset.refl _) hne mixed_premises_sat.2.2.2.2.2.2.2.2.2.1
    mixed_premises_sat.2.2.2.2.2.2.2.2.2.2 geometry_premises_sat.1
    geometry_premises_sat.2.1 geometry_premises_sat.2.2
  obtain ⟨K, _, _, _, _, _, _, _, _, _, _, _, hKU, _⟩ := rows 0 (by rw [hH]; simp)
  have hu : FGBlock.genesis = U := hKU
  subst U
  exact ⟨hU, rows⟩

#print axioms mixed_fixed_rows

/-- Node 7 emits no encoded FG wire, even when its non-FG duty emits a signed object. -/
private theorem nonholder_no_encoded (j : Nat) (t : Time)
    (ht : run.events[j]? = some (.tick 7 t)) (a : Row (Fin 1)) :
    reads.encode a ∉ V2.D.Run.emitsAt env run j := by
  have hj : j < 4 := (List.getElem?_eq_some_iff.mp ht).1
  interval_cases j
  · have hn : (9 : Nat) = 7 := congrArg V2.Event.node (Option.some.inj ht)
    omega
  · change (⟨.seat 6 0, a⟩ : protocol.Object) ∉ [⟨.none, row⟩]
    simp
  · change (⟨.seat 6 0, a⟩ : protocol.Object) ∉ [⟨.seat 8 0, row⟩, ⟨.none, row⟩]
    simp
  · change (⟨.seat 6 0, a⟩ : protocol.Object) ∉ [⟨.none, row⟩]
    simp

#print axioms nonholder_no_encoded

/-- Only the old all-honest row demand fails; both honest sources are present. -/
private theorem old_coverage_rejected :
    ¬ OpeningCovered core reads env run height timing Row.height_pair 0 .genesis ∧
    ∀ U, ¬ FixedRows core reads env run height timing Row.height_pair 0 1 .genesis U := by
  constructor
  · intro hc
    obtain ⟨_, _, j, rSent, a, _, _, _, _, _, ha, _⟩ := hc 7 (by decide)
    exact nonholder_no_encoded j _ ha.2.1 a ha.2.2
  · intro U hr
    obtain ⟨_, _, j, rSent, a, _, _, _, _, _, _, _, _, _, ha, _⟩ := hr 7 (by decide)
    exact nonholder_no_encoded j _ ha.2.1 a ha.2.2

#print axioms old_coverage_rejected

private abbrev interface : V2.D.Interface protocol where
  confirmed _ := .genesis
  stable _ := .genesis
  block _ := some .genesis
  opening _ := True
  propLabel s := 4 * (s : Time)
  propDuty s := 4 * (s : Time)
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := by
    intro a b h
    change 4 * (a : Int) = 4 * (b : Int) at h
    exact Int.ofNat_injective (mul_left_cancel₀ (by decide : (4 : Int) ≠ 0) h)
private abbrev child (s : Slot) : FGBlock (Fin 1) := .node .genesis s ⟨s⟩ 0 []
private abbrev parent (_ : RecordOnce) (_ : Block) := some (FGBlock.genesis : FGBlock (Fin 1))
private abbrev parentHeight (_ : RecordOnce) (_ : Slot) (_ : FGBlock (Fin 1)) :=
  (1, genesisRoot)
private abbrev valid (_ : RecordOnce) (_ : Slot) (_ : FGBlock (Fin 1))
    (a : Row (Fin 1)) := Window.r6w Window.initial a
private abbrev fold (_ : RecordOnce) (_ : Slot) (_ : FGBlock (Fin 1)) :
    Window.State (Fin 1) := Window.initial

private theorem carrier_premises_sat (s : Slot) (hs : s ∈ ({2, 3} : Finset Nat)) :
    V2.D.proposerOf run interface s = 7 ∧ timing.proposal s ≤ run.horizon ∧
    (∀ x K, x ∈ run.honest →
      actionSourceFG core env run timing x 0 = some (some K) →
      FGBlock.Preceq K (child s).parent) ∧
    ∃ nd, proposalStateAt env run interface s = some nd ∧
      parent nd (core.erase (child s)).parent = some (child s).parent ∧
      (fold nd s (child s).parent).h = (height (child s).parent).h ∧
      (fold nd s (child s).parent).T_h = (height (child s).parent).T_h ∧
      parentHeight nd s (child s).parent =
        ((fold nd s (child s).parent).h, (fold nd s (child s).parent).T_h.root) ∧
      ∀ a, valid nd s (child s).parent a =
        match reads.decode a with
        | none => false
        | some b => Window.r6w (fold nd s (child s).parent) b := by
  have hs' : s = 2 ∨ s = 3 := by simpa using hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hs' with rfl | rfl <;> rfl
  · rcases hs' with rfl | rfl <;> decide
  · intro x K hx hK
    have he := mixed_premises_sat.2.2.2.2.2.2.2.2.1 x hx
    have hk : K = .genesis := Option.some.inj (Option.some.inj (hK.symm.trans he))
    subst K
    exact preceq_refl _
  · rcases hs' with rfl | rfl
    · exact ⟨V2.D.Run.stateBefore env run 2 7, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨V2.D.Run.stateBefore env run 3 7, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

#print axioms carrier_premises_sat

private theorem holder_row_identity {j r : Nat} {a : Row (Fin 1)}
    (ha : HonestRowAt reads env run timing j 9 r a) : j = 0 ∧ r = 0 ∧ a = row := by
  have hj : j < 4 := (List.getElem?_eq_some_iff.mp ha.2.1).1
  interval_cases j
  · have ht : (6 : Int) = 8 * (r : Int) + 6 :=
      congrArg V2.Event.time (Option.some.inj ha.2.1)
    have hr : r = 0 := by omega
    refine ⟨rfl, hr, ?_⟩
    have hm := ha.2.2
    change (⟨.seat 6 0, a⟩ : protocol.Object) ∈ [⟨.seat 6 0, row⟩, ⟨.none, row⟩] at hm
    simpa using hm
  all_goals
    have hn : (7 : Nat) = 9 := congrArg V2.Event.node (Option.some.inj ha.2.1)
    omega

#print axioms holder_row_identity

/-- One selected U/wire/index works at every later carrier cut in this run. -/
private theorem mixed_same_rows :
    ∃ U j rSent a, U = (.genesis : FGBlock (Fin 1)) ∧ j = 0 ∧ rSent = 0 ∧ a = row ∧
      EntryAt height U 1 ∧ HonestRowAt reads env run timing j 9 rSent a ∧
      ∀ s ∈ ({2, 3} : Finset Nat), FGBlock.Preceq U (child s).parent ∧
        ValidForParent env run interface parent valid (child s).slot (core.erase (child s)) a ∧
        HeightMatch env run interface (fun b => namedEntry b.height_pair) parent parentHeight
          (child s).slot (core.erase (child s)) a := by
  have hH := mixed_premises_sat.2.2.2.2.1
  have hi : (0 : Fin 1) ∈ FGHonestSeats reads run := by rw [hH]; simp
  obtain ⟨_, _, j, rSent, a, _, _, _, _, _, _, _, _, _, ha, _⟩ := mixed_fixed_rows.2 0 hi
  obtain ⟨rfl, rfl, rfl⟩ := holder_row_identity ha
  refine ⟨.genesis, 0, 0, row, rfl, rfl, rfl, rfl, mixed_fixed_rows.1, ha, ?_⟩
  intro s hs
  have hp := carrier_premises_sat s hs
  obtain ⟨U, _, _, _, rows⟩ := healing_promotion_same_rows_holder core reads env run
    height timing interface Row.height_pair parent parentHeight valid fold
    (electorate 1) height_premises_sat (Finset.Subset.refl _) ⟨0, hi⟩
    mixed_premises_sat.2.2.2.2.2.2.2.2.2.1 mixed_premises_sat.2.2.2.2.2.2.2.2.2.2
    geometry_premises_sat.1 geometry_premises_sat.2.1 geometry_premises_sat.2.2
    hp.2.2.1 (X := child s) rfl hp.2.2.2 (fun _ _ _ a _ => ⟨a, rfl, rfl⟩)
  obtain ⟨_, _, j, rSent, a, _, _, _, _, _, _, _, _, _, ha', _, hv⟩ := rows 0 hi
  obtain ⟨rfl, rfl, rfl⟩ := holder_row_identity ha'
  exact ⟨preceq_refl _, hv rfl⟩

#print axioms mixed_same_rows

private abbrev emptyRun : V2.D.Run Nat protocol := { run with honest := {7} }
private abbrev emptyCore : FGCoreReads protocol 1 Unit Unit (Row (Fin 1)) :=
  { core with source := fun _ => none }

/-- Every fixed-row premise other than seat nonemptiness is inhabited at height zero. -/
private theorem empty_premises_sat :
    emptyRun.honest = {7} ∧ emptyRun.honest.Nonempty ∧ FGHonestSeats reads emptyRun = ∅ ∧
    OpeningEntry emptyCore env emptyRun height timing 0 0 ∧
    OpeningCoveredFG emptyCore reads env emptyRun height timing Row.height_pair
      (FGHonestSeats reads emptyRun) 0 .genesis ∧
    FixedRowsFG emptyCore reads env emptyRun height timing Row.height_pair
      (FGHonestSeats reads emptyRun) 0 0 .genesis .genesis ∧
    (∀ x K, actionSourceFG emptyCore env emptyRun timing x 0 ≠ some (some K)) := by
  have hH : FGHonestSeats reads emptyRun = ∅ := by
    ext i
    simp [FGHonestSeats_def, safetyHolder, reads, emptyRun]
  have hn (x) (K) : actionSourceFG emptyCore env emptyRun timing x 0 ≠ some (some K) := by
    intro hK
    change (postClock env emptyRun x (timing.action 0)).map (fun _ => none) = _ at hK
    cases postClock env emptyRun x (timing.action 0) <;> simp at hK
  refine ⟨rfl, ⟨7, by simp⟩, hH, ?_, ?_, ?_, hn⟩
  · exact ⟨genesisRoot, fun x K _ hK => (hn x K hK).elim⟩
  · intro i hi
    rw [hH] at hi
    exact (Finset.notMem_empty i hi).elim
  · intro i hi
    rw [hH] at hi
    exact (Finset.notMem_empty i hi).elim

#print axioms empty_premises_sat

private theorem empty_witness_rejected :
    ¬ (FGHonestSeats reads emptyRun).Nonempty ∧
    ¬ (∃ U, EntryAt height U 0) ∧
    ¬ (∃ i j r a, HonestRowAt reads env emptyRun timing j (safetyHolder reads emptyRun i) r a) ∧
    (∀ x y K L, x ∈ emptyRun.honest → y ∈ emptyRun.honest →
      actionSourceFG emptyCore env emptyRun timing x 0 = some (some K) →
      actionSourceFG emptyCore env emptyRun timing y 0 = some (some L) →
      (height K).T_h.root = (height L).T_h.root → (height K).T_h = (height L).T_h) ∧
    (∀ x K, x ∈ emptyRun.honest →
      actionSourceFG emptyCore env emptyRun timing x 0 = some (some K) →
      K.slot ≤ 0 * timing.roundSlots) := by
  refine ⟨?_, ?_, ?_, fun _ _ _ _ _ _ _ _ _ => rfl, ?_⟩
  · rw [empty_premises_sat.2.2.1]
    exact Finset.not_nonempty_empty
  · rintro ⟨U, hU⟩
    have hh : (1 : Nat) = 0 := hU.1
    omega
  · rintro ⟨i, j, r, a, ha⟩
    have hh : (9 : Nat) ∈ ({7} : Finset Nat) := ha.1
    simp at hh
  · intro x K _ hK
    exact (empty_premises_sat.2.2.2.2.2.2 x K hK).elim

#print axioms empty_witness_rejected

private abbrev frozenEnv : Generic.Env (Fin 1) :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := {0}
  horizon := 20
  events := [.tick 0 6, .tick 0 8, .tick 0 12]
  seatOf := fun _ i => i
  input := fun _ _ => ()

private theorem frozen_premises_sat :
    (∀ i, safetyHolder reads frozenRun i = (Equiv.refl (Fin 1)) i) ∧
    FGHonestSeats reads frozenRun = {0} ∧
    OpeningCovered core reads frozenEnv frozenRun height timing Row.height_pair 0 .genesis ∧
    OpeningEntry core frozenEnv frozenRun height timing 0 1 ∧
    (∀ x K, actionSourceFG core frozenEnv frozenRun timing x 0 = some (some K) →
      K = .genesis) ∧
    ∀ s ∈ ({2, 3} : Finset Nat), timing.proposal s ≤ frozenRun.horizon ∧
      ∃ nd, proposalStateAt frozenEnv frozenRun interface s = some nd ∧
        parent nd (core.erase (child s)).parent = some (child s).parent ∧
        (fold nd s (child s).parent).h = (height (child s).parent).h ∧
        (fold nd s (child s).parent).T_h = (height (child s).parent).T_h ∧
        parentHeight nd s (child s).parent =
          ((fold nd s (child s).parent).h, (fold nd s (child s).parent).T_h.root) ∧
        ∀ a, valid nd s (child s).parent a =
          match reads.decode a with
          | none => false
          | some b => Window.r6w (fold nd s (child s).parent) b := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, frozenRun]
  · intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    refine ⟨.genesis, RecordOnce.initial, 0, 0, row, rfl, ?_, ?_, ?_, le_rfl, ?_, rfl⟩
    · decide +kernel
    · decide
    · decide
    · unfold HonestRowAt
      decide +kernel
  · exact ⟨genesisRoot, fun _ _ _ _ => ⟨rfl, rfl⟩⟩
  · intro x K hK
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    have hs : actionSourceFG core frozenEnv frozenRun timing 0 0 = some (some .genesis) := rfl
    exact Option.some.inj (Option.some.inj (hK.symm.trans hs))
  · intro s hs
    have hs' : s = 2 ∨ s = 3 := by simpa using hs
    rcases hs' with rfl | rfl
    · exact ⟨by decide, V2.D.Run.stateBefore frozenEnv frozenRun 1 0,
        rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨by decide, V2.D.Run.stateBefore frozenEnv frozenRun 2 0,
        rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

#print axioms frozen_premises_sat

/-- The holder theorem recovers the complete old same-row conclusion in the frozen run. -/
private theorem frozen_same_rows (s : Slot) (hs : s ∈ ({2, 3} : Finset Nat)) :
    ∃ U, EntryAt height U 1 ∧ U.slot ≤ 0 * timing.roundSlots ∧
      FGBlock.Preceq U (child s).parent ∧
      ∀ x ∈ frozenRun.honest, ∃ K nd j rSent a,
        postClock frozenEnv frozenRun x (timing.action 0) = some nd ∧
        actionSourceFG core frozenEnv frozenRun timing x 0 = some (some K) ∧
        K ∈ (core.core nd).fg.TF ∧ Block.Preceq .genesis (core.erase K) ∧
        FGBlock.Preceq U K ∧ K.slot ≤ 0 * timing.roundSlots ∧
        (height K).h = 1 ∧ (height K).T_h = U ∧ rSent ≤ 0 ∧
        HonestRowAt reads frozenEnv frozenRun timing j x rSent a ∧
        NamesEntry Row.height_pair .progress a 1 U ∧
        ((height (child s).parent).h = 1 →
          ValidForParent frozenEnv frozenRun interface parent valid
            (child s).slot (core.erase (child s)) a ∧
          HeightMatch frozenEnv frozenRun interface (fun b => namedEntry b.height_pair)
            parent parentHeight (child s).slot (core.erase (child s)) a) := by
  have hp := frozen_premises_sat
  have hcov := (openingCoveredFG_frozen_iff core reads frozenEnv frozenRun height timing
    Row.height_pair (Equiv.refl _) hp.1 0 .genesis).2 hp.2.2.1
  have hne : (FGHonestSeats reads frozenRun).Nonempty := by rw [hp.2.1]; simp
  have hslot : ∀ x K, x ∈ frozenRun.honest →
      actionSourceFG core frozenEnv frozenRun timing x 0 = some (some K) →
      K.slot ≤ 0 * timing.roundSlots := by
    intro x K _ hK
    rw [hp.2.2.2.2.1 x K hK]
    exact le_rfl
  have hancestor : ∀ x K U, x ∈ frozenRun.honest →
      actionSourceFG core frozenEnv frozenRun timing x 0 = some (some K) →
      FGBlock.Preceq U K → U.slot ≤ K.slot := by
    intro x K U _ hK hUK
    have hk := hp.2.2.2.2.1 x K hK
    subst K
    have hu : U = .genesis := by simpa [FGBlock.Preceq, FGBlock.preceq] using hUK
    subst U
    exact le_rfl
  have hparent : ∀ x K, x ∈ frozenRun.honest →
      actionSourceFG core frozenEnv frozenRun timing x 0 = some (some K) →
      FGBlock.Preceq K (child s).parent := by
    intro x K _ hK
    rw [hp.2.2.2.2.1 x K hK]
    exact preceq_refl _
  obtain ⟨U, hU, hUs, hUP, rows⟩ := healing_promotion_same_rows_holder
    core reads frozenEnv frozenRun height timing interface Row.height_pair
    parent parentHeight valid fold (electorate 1) height_premises_sat
    (Finset.Subset.refl _) hne hp.2.2.2.1 hcov (fun _ _ _ _ _ _ _ _ _ => rfl)
    hslot hancestor hparent (X := child s) rfl (hp.2.2.2.2.2 s hs).2
    (fun _ _ _ a _ => ⟨a, rfl, rfl⟩)
  refine ⟨U, hU, hUs, hUP, ?_⟩
  intro x hx
  exact rows x (by simpa only [FGHonestSeats_def, Finset.mem_filter,
    Finset.mem_univ, true_and, hp.1, Equiv.refl_apply] using hx)

#print axioms frozen_same_rows

private theorem frozen_bridges :
    (OpeningCoveredFG core reads frozenEnv frozenRun height timing Row.height_pair
      (FGHonestSeats reads frozenRun) 0 .genesis ↔
      OpeningCovered core reads frozenEnv frozenRun height timing Row.height_pair 0 .genesis) ∧
    (∀ U, FixedRowsFG core reads frozenEnv frozenRun height timing Row.height_pair
      (FGHonestSeats reads frozenRun) 0 1 .genesis U ↔
      FixedRows core reads frozenEnv frozenRun height timing Row.height_pair 0 1 .genesis U) ∧
    (∃ U, FixedRows core reads frozenEnv frozenRun height timing Row.height_pair 0 1 .genesis U ∧
      FixedRowsFG core reads frozenEnv frozenRun height timing Row.height_pair
        (FGHonestSeats reads frozenRun) 0 1 .genesis U) ∧
    (∅ : Finset (Fin 1)) ⊂ FGHonestSeats reads frozenRun ∧
    ∀ A ⊆ FGHonestSeats reads frozenRun,
      (OpeningCovered core reads frozenEnv frozenRun height timing Row.height_pair 0 .genesis →
        OpeningCoveredFG core reads frozenEnv frozenRun height timing Row.height_pair
          A 0 .genesis) ∧
      (∀ U, FixedRows core reads frozenEnv frozenRun height timing Row.height_pair 0 1 .genesis U →
        FixedRowsFG core reads frozenEnv frozenRun height timing Row.height_pair
          A 0 1 .genesis U) := by
  have ho := openingCoveredFG_frozen_iff core reads frozenEnv frozenRun height timing
    Row.height_pair (Equiv.refl _) frozen_premises_sat.1 0 .genesis
  have hf := fixedRowsFG_frozen_iff core reads frozenEnv frozenRun height timing
    Row.height_pair (Equiv.refl _) frozen_premises_sat.1 0 1 .genesis
  refine ⟨ho, hf, ?_, ?_, ?_⟩
  · obtain ⟨U, _, _, _, rows⟩ := frozen_same_rows 2 (by simp)
    have hr : FixedRows core reads frozenEnv frozenRun height timing Row.height_pair
        0 1 .genesis U := by
      intro x hx
      obtain ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hUK, hs, hh, hu, hr, ha, hn, _⟩ := rows x hx
      exact ⟨K, nd, j, rSent, a, hnd, hK, hm, hQ, hUK, hs, hh, hu, hr, ha, hn⟩
    exact ⟨U, hr, (hf U).2 hr⟩
  · rw [frozen_premises_sat.2.1]
    simp
  · intro A hA
    have honest (i) (hi : i ∈ A) : safetyHolder reads frozenRun i ∈ frozenRun.honest := by
      simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hA hi
    exact ⟨fun h i hi => h _ (honest i hi), fun U h i hi => h _ (honest i hi)⟩

#print axioms frozen_bridges

end AvailableChain.FGCompose.Tests.PopulationPromotion
end
