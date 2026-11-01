module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchRepair
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchBridges
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchRepair

set_option linter.privateModule false

noncomputable section
namespace AvailableChain.FGCompose.Tests.PopulationSearchSeed
open AvailableChain.SimplexFG AvailableChain.KitFG

-- Private fixture support copied from the accepted PopulationService controls.
namespace Fixture

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

end Fixture

open Fixture

/-! Generic ordinary-event-fold control: the exact POP-4 mixed run, now consumed by
POP-5's saved-seed theorem. Its proposer is 7; only holder 9 releases an FG row. -/

private abbrev seedObs : FGObservationReads core where
  height := height
  finality := fun _ => ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView height (core.core nd).fg
  viable nd X := treeStoreFrameView height (core.core nd).fg X

private theorem saved_seed_premises_sat :
    FGTimingLaws timing ∧ FGObservationLaws core seedObs ∧
    HonestProposal env run interface 2 .genesis ∧
    V2.D.proposerOf run interface 2 = 7 ∧
    FrontierSeedQualification timing 1 env.t_GST 0 2 ∧
    PhaseInterval core env run seedObs 0 (timing.gate 2) 1 (some .genesis) false ∧
    FrontierProposalService core env run timing 2 .genesis ∧
    FrontierLocalServiceFG core reads env run seedObs timing interface Row.height_pair
      2 .genesis .genesis 1 (timing.gate 2) ∧
    HonestRowAt reads env run timing 0 9 0 row ∧
    (∀ x ∈ run.honest, actionSourceFG core env run timing x 1 = some (some .genesis)) := by
  obtain ⟨hp, hproposer, _, _, _, _, hqual, hphase, _⟩ := seed_premises_sat
  obtain ⟨_, _, _, _, _, _, _, hrow, hhead, _, hsource, _, _⟩ := service_premises_sat
  refine ⟨?_, ⟨fun _ => rfl, fun _ _ => rfl⟩, hp, hproposer, hqual, ?_, ?_, ?_, hrow,
    hsource⟩
  · constructor <;> first | decide | (intro s; dsimp only [timing] <;> push_cast <;> ring)
  · exact hphase
  · intro _ x hx _
    exact hhead x hx
  · obtain ⟨hhead, hparent, hstable, hlater, hopen⟩ := mixed_service
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H hx hs ht hh
      exact hhead x s H hx hs (ht.trans (by decide)) hh
    · intro s B hs ht hp
      exact hparent s B hs (ht.trans (by decide)) hp
    · intro i x hx ht hi hit
      exact hstable i x hx (ht.trans (by decide)) hi
        (hit.trans (frontierSearch_timeIdx_mono run (by decide)))
    · intro s B hs ht hp
      exact hlater s B hs (ht.trans (by decide)) hp
    · intro r hq ht
      exact hopen r hq (ht.trans (by decide))

#print axioms saved_seed_premises_sat

private theorem mixed_saved_seed_consumer :
    StrongServedFG core reads env run seedObs timing interface Row.height_pair 0 1 1 14 ∧
    V2.D.proposerOf run interface 2 = 7 ∧
    HonestRowAt reads env run timing 0 9 0 row := by
  obtain ⟨ht, ho, hp, hproposer, hqual, hphase, hservice, hlocal, hrow, _⟩ :=
    saved_seed_premises_sat
  refine ⟨?_, hproposer, hrow⟩
  exact frontierSearch_save_seed_holder core reads env run seedObs timing interface
    Row.height_pair 0 1 ho ht le_rfl le_rfl hphase hqual hp rfl rfl hservice le_rfl hlocal

#print axioms mixed_saved_seed_consumer

/-! A schedule-valid refusal fixture. The FG record ignores non-FG signatures.
Holder 9 has its actual FG row; nonholder 7's exact HEAD differs from the selected proposal. -/
private abbrev wrongHead : Block := .node .genesis 1 ⟨99⟩ 0
private abbrev missingProtocol : V2.ProtocolSpecD Unit :=
  { protocol with recordOwn := fun st o => match o.auth with
      | .seat l _ => if l = 6 then record_row_once st o.payload else st
      | .none => st }
private abbrev missingRun : V2.D.Run Nat missingProtocol where
  honest := run.honest
  horizon := 18
  events := (List.range 19).flatMap fun (t : Nat) => [.tick 7 (t : Time), .tick 9 (t : Time)]
  seatOf := run.seatOf
  input := run.input
private abbrev missingCore : FGCoreReads missingProtocol 1 Unit Unit (Row (Fin 1)) where
  core := core.core
  erase := core.erase
  source := core.source
  headVote st _ := if st.sent.isEmpty then wrongHead else .genesis
  finalityHead := core.finalityHead
  proposalFG := core.proposalFG
private abbrev missingObs : FGObservationReads missingCore where
  height := height
  finality := fun _ => ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView height (missingCore.core nd).fg
  viable nd X := treeStoreFrameView height (missingCore.core nd).fg X
private abbrev missingIface : V2.D.Interface missingProtocol where
  confirmed := interface.confirmed
  stable := interface.stable
  block := interface.block
  opening := interface.opening
  propLabel := interface.propLabel
  propDuty := interface.propDuty
  propDuty_label := interface.propDuty_label
  propLabel_single := interface.propLabel_single
  propLabel_injective := interface.propLabel_injective
private abbrev missingReads : FGSafetyReads missingProtocol 1 (Row (Fin 1)) where
  proposalErase := reads.proposalErase
  proposalRows := reads.proposalRows
  encode := reads.encode
  decode := reads.decode
  decodeObject := reads.decodeObject
  fgLabel := reads.fgLabel
  fgSeats := reads.fgSeats
  record := reads.record
  inputs := reads.inputs
  enabled := reads.enabled
  finalizedOut := reads.finalizedOut

private theorem missing_receiver_premises_sat :
    V2.D.ScheduleWellFormed env missingRun ∧ FGTimingLaws timing ∧
    FGObservationLaws missingCore missingObs ∧ missingRun.honest = {7, 9} ∧
    HonestProposal env missingRun missingIface 2 .genesis ∧
    FrontierSeedQualification timing 1 env.t_GST 0 2 ∧
    PhaseInterval missingCore env missingRun missingObs 0 (timing.gate 2) 1
      (some .genesis) false ∧
    FrontierLocalServiceFG missingCore missingReads env missingRun missingObs timing
      missingIface Row.height_pair 2 .genesis .genesis 1 (timing.gate 2) ∧
    HonestRowAt missingReads env missingRun timing 13 9 0 row ∧
    headAtLabel missingCore env missingRun timing 9 2 = some .genesis ∧
    (∀ q : Fin 5, headAtLabel missingCore env missingRun timing 7 q.val = some wrongHead) ∧
    (∀ q, AttemptJoinedAt env missingRun timing 7 q (timing.vote q)) := by
  have hrow : HonestRowAt missingReads env missingRun timing 13 9 0 row := by
    unfold HonestRowAt
    decide +kernel
  have hc : OpeningCoveredFG missingCore missingReads env missingRun height timing Row.height_pair
      (FGHonestSeats missingReads missingRun) 1 .genesis := by
    intro i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨.genesis, missingRun.stateBefore env 29 9, 13, 0, row,
      rfl, by decide +kernel, by decide, by decide, by decide, hrow, rfl⟩
  refine ⟨?_, saved_seed_premises_sat.1, ⟨fun _ => rfl, fun _ _ => rfl⟩, rfl, ?_, ?_, ?_,
    ?_, hrow, by decide +kernel, by decide +kernel, ?_⟩
  · refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
    · intro x t ht
      dsimp only [missingRun] at ht
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp ht
      have hk' : (x = 7 ∧ t = (k : Time)) ∨ (x = 9 ∧ t = (k : Time)) := by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
          V2.Event.tick.injEq] using hk
      rcases hk' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨k, by simp⟩
    · intro x hx t ht _ hh _
      obtain ⟨k, rfl⟩ := ht
      have hk : k < 19 := by change (k : Int) * 1 ≤ 18 at hh; omega
      have hx' : x = 7 ∨ x = 9 := by simpa using hx
      dsimp only [missingRun, env]
      apply List.mem_flatMap.mpr
      refine ⟨k, List.mem_range.mpr hk, ?_⟩
      rcases hx' with rfl | rfl <;> simp
  · exact ⟨⟨by decide, by decide⟩, ⟨.seat 8 0, row⟩,
      ⟨16, by decide +kernel, by decide +kernel⟩, rfl⟩
  · exact Or.inr ⟨0, by decide, fun _ _ => Nat.zero_le _, by decide, by decide, by decide⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x _ _ _
    change (missingObs.controls RecordOnce.initial).H = 1 ∧ _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H _ _ _ hH
      delta headAtLabel at hH
      obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hH
      change (if nd.sent.isEmpty then wrongHead else Block.genesis) = H at he
      rw [← he]
      split <;> decide
    · intro s B _ _ hp
      obtain ⟨_, o, _, hb⟩ := hp
      have hB : B = .genesis := (Option.some.inj hb).symm
      subst B
      decide
    · intro i x _ _ _ _
      change Block.Preceq .genesis .genesis
      decide
    · intro s B hs ht _
      change 8 < 4 * (s : Int) at hs
      change 4 * (s : Int) + 6 ≤ 14 at ht
      omega
    · intro r hqr ht
      change @LE.le Nat _ 2 (r * 2) at hqr
      change 8 * (r : Int) + 6 ≤ 14 at ht
      have hr : @Eq Nat r 1 := by omega
      subst r
      exact ⟨hc, ⟨genesisRoot, fun _ _ _ _ => ⟨rfl, rfl⟩⟩,
        fun _ _ _ _ => rfl, fun _ => by decide⟩
  · intro q
    refine ⟨rfl, ?_, ?_⟩
    · intro u _ _ hw
      have hf : true = false := hw.2
      cases hf
    · intro u _ _ hr
      simp [List.mem_flatMap] at hr

#print axioms missing_receiver_premises_sat

private theorem missing_receiver_service_rejected :
    (¬ FrontierProposalService missingCore env missingRun timing 2 .genesis) ∧
    ∀ t, ¬ StrongServedFG missingCore missingReads env missingRun missingObs timing
      missingIface Row.height_pair 0 1 1 t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heads, joined⟩ := missing_receiver_premises_sat
  have noService (q : Nat) (hq : q < 5) (ht : timing.vote q ≤ missingRun.horizon) :
      ¬ FrontierProposalService missingCore env missingRun timing q .genesis := by
    intro hs
    have hh := hs ht 7 (by decide) (joined q)
    have hw : headAtLabel missingCore env missingRun timing 7 q = some wrongHead :=
      heads ⟨q, hq⟩
    rw [hw] at hh
    cases hh
  refine ⟨noService 2 (by decide) (by decide), ?_⟩
  intro t hs
  obtain ⟨u, J, c, q, Q, Qfg, _, hp, _, _, hsvc, _, _, _, hg, hh, _⟩ := hs
  obtain ⟨_, o, _, hb⟩ := hp
  have hQ : Q = .genesis := (Option.some.inj hb).symm
  subst Q
  have hgate := hg.trans hh
  change 4 * (q : Int) + 6 ≤ 18 at hgate
  have hq : @LT.lt Nat _ q 5 := by omega
  have hvote : timing.vote q ≤ missingRun.horizon := by
    change 4 * (q : Int) + 1 ≤ 18
    omega
  exact noService q hq hvote hsvc

#print axioms missing_receiver_service_rejected

private theorem frozen_seed_premises_sat :
    FGTimingLaws timing ∧ FGObservationLaws core seedObs ∧
    (∀ i, safetyHolder reads frozenRun i = (Equiv.refl (Fin 1)) i) ∧
    HonestProposal frozenEnv frozenRun interface 2 .genesis ∧
    FrontierSeedQualification timing 1 frozenEnv.t_GST 0 2 ∧
    PhaseInterval core frozenEnv frozenRun seedObs 0 (timing.gate 2) 1
      (some .genesis) false ∧
    FrontierProposalService core frozenEnv frozenRun timing 2 .genesis ∧
    FrontierLocalServiceFG core reads frozenEnv frozenRun seedObs timing interface Row.height_pair
      2 .genesis .genesis 1 (timing.gate 2) ∧
    HonestRowAt reads frozenEnv frozenRun timing 0 0 0 row := by
  obtain ⟨he, _, hrow, hp, hcovered⟩ := frozen_premises_sat
  have hc := (openingCoveredFG_frozen_iff core reads frozenEnv frozenRun height timing
    Row.height_pair (Equiv.refl _) he 1 .genesis).2 hcovered
  refine ⟨saved_seed_premises_sat.1, saved_seed_premises_sat.2.1, he, hp, ?_, ?_, ?_, ?_, hrow⟩
  · exact Or.inr ⟨0, by decide, fun _ _ => Nat.zero_le _, by decide, by decide, by decide⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x _ _ _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro _ x _ _
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    decide +kernel
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H _ _ _ hH
      delta headAtLabel at hH
      obtain ⟨nd, _, he⟩ := Option.map_eq_some_iff.mp hH
      change Block.genesis = H at he
      subst H
      decide
    · intro s B _ _ hB
      obtain ⟨_, o, _, hb⟩ := hB
      have hB' : B = .genesis := (Option.some.inj hb).symm
      subst B
      decide
    · intro i x _ _ _ _
      change Block.Preceq .genesis .genesis
      decide
    · intro s B hs ht _
      change 8 < 4 * (s : Int) at hs
      change 4 * (s : Int) + 6 ≤ 14 at ht
      omega
    · intro r hqr ht
      change @LE.le Nat _ 2 (r * 2) at hqr
      change 8 * (r : Int) + 6 ≤ 14 at ht
      have hr : @Eq Nat r 1 := by omega
      subst r
      exact ⟨hc, ⟨genesisRoot, fun _ _ _ _ => ⟨rfl, rfl⟩⟩,
        fun _ _ _ _ => rfl, fun _ => by decide⟩

#print axioms frozen_seed_premises_sat

private theorem frozen_saved_seed_bridge :
    StrongServedFG core reads frozenEnv frozenRun seedObs timing interface Row.height_pair
      0 1 1 14 ∧
    StrongServed core reads frozenEnv frozenRun seedObs timing interface Row.height_pair
      0 1 1 14 ∧ HonestRowAt reads frozenEnv frozenRun timing 0 0 0 row := by
  obtain ⟨ht, ho, he, hp, hqual, hphase, hservice, hlocal, hrow⟩ := frozen_seed_premises_sat
  have hs := frontierSearch_save_seed_holder core reads frozenEnv frozenRun seedObs timing
    interface Row.height_pair 0 1 ho ht le_rfl le_rfl hphase hqual hp rfl rfl hservice le_rfl
    hlocal
  have bridge := strongServedFG_frozen_iff core reads frozenEnv frozenRun seedObs timing
    interface Row.height_pair 0 1 (Equiv.refl _) he 1 14
  exact ⟨hs, bridge.1 hs, hrow⟩

#print axioms frozen_saved_seed_bridge

end AvailableChain.FGCompose.Tests.PopulationSearchSeed
end
