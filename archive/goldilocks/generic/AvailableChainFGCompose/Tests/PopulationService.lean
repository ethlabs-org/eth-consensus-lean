module
public import Mathlib.Tactic.IntervalCases
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchBridges

set_option linter.privateModule false

noncomputable section
public section

/-! Generic ordinary-event-fold controls, not a concrete PC execution.
Both honest nodes have HEAD and action cuts. Only holder 9 emits an FG wire.
The only proposal time is 8 (slot 2); the served endpoint 18 triggers opening 1. -/
namespace AvailableChain.FGCompose.Tests.PopulationService
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
  horizon := 18
  events := [.tick 9 6, .tick 7 8, .tick 7 9, .tick 9 9, .tick 7 13,
    .tick 9 13, .tick 7 14, .tick 9 14, .tick 7 18, .tick 9 18]
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
    exact Int.ofNat.inj (show (a : Int) = (b : Int) by omega)

private abbrev obs : FGObservationReads core where
  height := height
  finality := fun _ => ⟨.genesis, 0⟩
  controls _ := ⟨.genesis, 1, 0, .genesis, false⟩
  viable _ X := X

private theorem service_premises_sat :
    run.honest = {7, 9} ∧ run.horizon = 18 ∧
    run.events = [.tick 9 6, .tick 7 8, .tick 7 9, .tick 9 9, .tick 7 13,
      .tick 9 13, .tick 7 14, .tick 9 14, .tick 7 18, .tick 9 18] ∧
    (∀ i, safetyHolder reads run i = 9) ∧ FGHonestSeats reads run = {0} ∧
    protocol.objSelfVisible (reads.encode row) = true ∧
    reads.decodeObject (reads.encode row) = some row ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    (∀ x ∈ run.honest, headAtLabel core env run timing x 2 = some .genesis) ∧
    (∀ x ∈ run.honest, headAtLabel core env run timing x 3 = some .genesis) ∧
    (∀ x ∈ run.honest,
      actionSourceFG core env run timing x 1 = some (some .genesis)) ∧
    OpeningEntry core env run height timing 1 1 ∧
    OpeningCoveredFG core reads env run height timing Row.height_pair
      (FGHonestSeats reads run) 1 .genesis := by
  refine ⟨rfl, rfl, rfl, fun _ => rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, run]
  · unfold HonestRowAt
    decide +kernel
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · intro x hx
    have hx' : x = 7 ∨ x = 9 := by simpa using hx
    rcases hx' with rfl | rfl <;> decide +kernel
  · exact ⟨genesisRoot, fun _ _ _ _ => ⟨rfl, rfl⟩⟩
  · intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨.genesis, V2.D.Run.stateBefore env run 7 9, 0, 0, row,
      ?_, ?_, ?_, ?_, by decide, ?_, rfl⟩
    · rfl
    · decide +kernel
    · decide
    · decide
    · unfold HonestRowAt
      decide +kernel

#print axioms service_premises_sat

private theorem proposal_unique {s : Slot} {B : Block}
    (h : HonestProposal env run interface s B) : s = 2 ∧ B = .genesis := by
  obtain ⟨_, o, ⟨j, hj, _⟩, hb⟩ := h
  refine ⟨?_, (Option.some.inj hb).symm⟩
  have hjlt : j < 10 := (List.getElem?_eq_some_iff.mp hj).1
  interval_cases j
  · have ht : (6 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (8 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    exact Int.ofNat.inj (show (s : Int) = 2 by omega)
  · have ht : (9 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (9 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (13 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (13 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (14 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (14 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (18 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega
  · have ht : (18 : Int) = 4 * (s : Int) :=
      Option.some.inj (congrArg (fun e => e.map V2.Event.time) hj)
    omega

#print axioms proposal_unique

private theorem mixed_service :
    FrontierLocalServiceFG core reads env run obs timing interface Row.height_pair
      2 .genesis .genesis 1 18 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, he, hc⟩ := service_premises_sat
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x s H _ _ _ hH
    change (postClock env run x (timing.vote s)).map (fun _ => Block.genesis) = some H at hH
    obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp hH
    change Block.genesis = H at h
    subst H
    decide
  · intro s B _ _ hp
    have hB := (proposal_unique hp).2
    subst B
    decide
  · intro i x _ _ _ _
    change Block.Preceq .genesis .genesis
    decide
  · intro s B hs _ hp
    have hq := (proposal_unique hp).1
    subst s
    exact (lt_irrefl _ hs).elim
  · intro r hq hv
    have hr : r = 1 := by
      change 2 ≤ r * 2 at hq
      change 8 * (r : Int) + 6 ≤ 18 at hv
      have hlo : 1 ≤ r := by
        by_contra hn
        have hz : r = 0 := Nat.eq_zero_of_not_pos hn
        subst r
        exact (by decide : ¬ ((2 : Nat) ≤ 0)) hq
      have hlo' : (1 : Int) ≤ (r : Int) := Int.ofNat_le.mpr hlo
      exact Int.ofNat.inj (show (r : Int) = 1 by omega)
    subst r
    exact ⟨hc, he, fun _ _ _ _ => rfl, fun _ => by decide⟩

#print axioms mixed_service

private theorem seed_premises_sat :
    HonestProposal env run interface 2 .genesis ∧ V2.D.proposerOf run interface 2 = 7 ∧
    2 ≤ 1 * timing.roundSlots ∧ timing.action 1 ≤ 18 ∧
    timing.gate 2 + 4 * timing.delta ≤ 18 ∧ (18 : Time) ≤ run.horizon ∧
    FrontierSeedQualification timing 1 env.t_GST 0 2 ∧
    PhaseInterval core env run obs 0 (timing.gate 2) 1 (some .genesis) false ∧
    (∀ i x, timeIdx run 0 ≤ i → i ≤ timeIdx run 18 → x ∈ run.honest →
      (core.core (run.stateBefore env i x)).fg.h_max ≤ 1) := by
  refine ⟨?_, rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, row⟩,
      ⟨1, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact Or.inr ⟨0, by decide, fun _ _ => Nat.zero_le _, by decide, by decide, by decide⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x _ _ _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro i x _ _ _
    exact le_rfl

#print axioms seed_premises_sat

private theorem mixed_saved_seed :
    StrongServedFG core reads env run obs timing interface Row.height_pair 0 1 1 18 := by
  obtain ⟨hp, _, _, _, _, hh, hqual, hphase, hcap⟩ := seed_premises_sat
  obtain ⟨_, _, _, _, _, _, _, _, hhead, _⟩ := service_premises_sat
  refine ⟨0, some .genesis, false, 2, .genesis, .genesis, le_rfl, hp, rfl, rfl,
    ?_, hqual, by decide, hphase, by decide, hh, hcap, mixed_service⟩
  intro _ x hx _
  exact hhead x hx

#print axioms mixed_saved_seed

/-- The sole negative cause: node 7 never emits any encoded FG wire. -/
private theorem nonholder_no_encoded (j : Nat) (t : Time)
    (ht : run.events[j]? = some (.tick 7 t)) (a : Row (Fin 1)) :
    reads.encode a ∉ V2.D.Run.emitsAt env run j := by
  have hj : j < 10 := (List.getElem?_eq_some_iff.mp ht).1
  interval_cases j
  all_goals first
    | have hn : (9 : Nat) = 7 := congrArg V2.Event.node (Option.some.inj ht)
      omega
    | change (⟨.seat 6 0, a⟩ : protocol.Object) ∉ [⟨.none, row⟩]
      simp
    | change (⟨.seat 6 0, a⟩ : protocol.Object) ∉ [⟨.seat 8 0, row⟩, ⟨.none, row⟩]
      simp

#print axioms nonholder_no_encoded

/-- All other local-service fields are supplied by mixed_service on these same data. -/
private theorem old_service_rejected (Qfg : FGBlock (Fin 1)) :
    ¬ FrontierLocalService core reads env run obs timing interface Row.height_pair
      2 .genesis Qfg 1 18 := by
  intro h
  have hc := (h.2.2.2.2 1 (by decide) (by decide)).1
  obtain ⟨_, _, j, rSent, a, _, _, _, _, _, ha, _⟩ := hc 7 (by decide)
  exact nonholder_no_encoded j _ ha.2.1 a ha.2.2

#print axioms old_service_rejected

/-- The eligible proposal is unique, so the old existential cannot choose an earlier seed. -/
private theorem old_saved_seed_rejected :
    ¬ StrongServed core reads env run obs timing interface Row.height_pair 0 1 1 18 := by
  rintro ⟨u, J, contested, q, Q, Qfg, _, hp, _, _, _, _, _, _, _, _, _, hs⟩
  obtain ⟨rfl, rfl⟩ := proposal_unique hp
  exact old_service_rejected Qfg hs

#print axioms old_saved_seed_rejected

private abbrev frozenEnv : Generic.Env (Fin 1) :=
  ⟨1, by decide, 0, by decide, fun _ _ => true⟩
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := {0}
  horizon := 18
  events := [.tick 0 6, .tick 0 8, .tick 0 9, .tick 0 13, .tick 0 14, .tick 0 18]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

private theorem frozen_premises_sat :
    (∀ i, safetyHolder reads frozenRun i = (Equiv.refl (Fin 1)) i) ∧
    FGHonestSeats reads frozenRun = {0} ∧
    HonestRowAt reads frozenEnv frozenRun timing 0 0 0 row ∧
    HonestProposal frozenEnv frozenRun interface 2 .genesis ∧
    OpeningCovered core reads frozenEnv frozenRun height timing Row.height_pair 1 .genesis := by
  refine ⟨fun i => Subsingleton.elim _ _, ?_, ?_, ?_, ?_⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, frozenRun]
  · unfold HonestRowAt
    decide +kernel
  · refine ⟨⟨by decide, by decide⟩, ⟨.none, row⟩,
      ⟨1, by decide +kernel, by decide +kernel⟩, rfl⟩
  · intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    refine ⟨.genesis, V2.D.Run.stateBefore frozenEnv frozenRun 4 0, 0, 0, row,
      ?_, ?_, ?_, ?_, by decide, ?_, rfl⟩
    · rfl
    · decide +kernel
    · decide
    · decide
    · unfold HonestRowAt
      decide +kernel

#print axioms frozen_premises_sat

/-- All five frozen iff bridges, plus only one-way coverage for a strict subset. -/
private theorem frozen_bridges :
    (FrontierLocalServiceFG core reads frozenEnv frozenRun obs timing interface Row.height_pair
      2 .genesis .genesis 1 18 ↔
      FrontierLocalService core reads frozenEnv frozenRun obs timing interface Row.height_pair
        2 .genesis .genesis 1 18) ∧
    (StrongServedFG core reads frozenEnv frozenRun obs timing interface Row.height_pair 0 1 1 18 ↔
      StrongServed core reads frozenEnv frozenRun obs timing interface Row.height_pair 0 1 1 18) ∧
    (FrontierHG3ResultFG core reads frozenEnv frozenRun obs timing interface Row.height_pair
      0 1 0 1 0 18 ↔
      FrontierHG3Result core reads frozenEnv frozenRun obs timing interface Row.height_pair
        0 1 0 1 0 18) ∧
    (∀ G ΔF ρbar,
      InterruptedRepairStatementFG core reads frozenEnv frozenRun obs timing interface
        Row.height_pair 0 1 4 G ΔF ρbar ↔
      InterruptedRepairStatement core reads frozenEnv frozenRun obs timing interface
        Row.height_pair 0 1 4 G ΔF ρbar) ∧
    (∀ G ΔF,
      FrontierTailStatementFG core reads frozenEnv frozenRun obs timing interface
        Row.height_pair 0 1 4 G ΔF ↔
      FrontierTailStatement core reads frozenEnv frozenRun obs timing interface
        Row.height_pair 0 1 4 G ΔF) ∧
    (∅ : Finset (Fin 1)) ⊂ FGHonestSeats reads frozenRun ∧
    (∀ A, A ⊆ FGHonestSeats reads frozenRun →
      OpeningCovered core reads frozenEnv frozenRun height timing Row.height_pair 1 .genesis →
      OpeningCoveredFG core reads frozenEnv frozenRun height timing Row.height_pair A 1 .genesis) ∧
    OpeningCoveredFG core reads frozenEnv frozenRun height timing Row.height_pair ∅ 1 .genesis := by
  obtain ⟨he, hH, _, _, hc⟩ := frozen_premises_sat
  have restrict (A : Finset (Fin 1)) (hA : A ⊆ FGHonestSeats reads frozenRun)
      (ho : OpeningCovered core reads frozenEnv frozenRun height timing Row.height_pair 1
        .genesis) :
      OpeningCoveredFG core reads frozenEnv frozenRun height timing Row.height_pair A 1
        .genesis := by
    have hall := (openingCoveredFG_frozen_iff core reads frozenEnv frozenRun height timing
      Row.height_pair (Equiv.refl _) he 1 .genesis).2 ho
    exact fun i hi => hall i (hA hi)
  refine ⟨frontierLocalServiceFG_frozen_iff core reads frozenEnv frozenRun obs timing interface
    Row.height_pair (Equiv.refl _) he 2 .genesis .genesis 1 18,
    strongServedFG_frozen_iff core reads frozenEnv frozenRun obs timing interface
      Row.height_pair 0 1 (Equiv.refl _) he 1 18,
    frontierHG3ResultFG_frozen_iff core reads frozenEnv frozenRun obs timing interface
      Row.height_pair 0 1 (Equiv.refl _) he 0 1 0 18,
    fun G ΔF ρbar => interruptedRepairStatementFG_frozen_iff core reads frozenEnv frozenRun
      obs timing interface Row.height_pair 0 1 4 (Equiv.refl _) he G ΔF ρbar,
    fun G ΔF => frontierTailStatementFG_frozen_iff core reads frozenEnv frozenRun obs timing
      interface Row.height_pair 0 1 4 (Equiv.refl _) he G ΔF, ?_, restrict,
    restrict ∅ (Finset.empty_subset _) hc⟩
  rw [hH]
  decide

#print axioms frozen_bridges

end AvailableChain.FGCompose.Tests.PopulationService
end
