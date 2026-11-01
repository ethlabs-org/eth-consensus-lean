module
public import AvailableChainFGCompose.Proofs.Population.Seats
public import AvailableChainFGCompose.Proofs.Population.Safety
public import AvailableChainFGCompose.Proofs.HolderClient

set_option linter.privateModule false

noncomputable section
public section

/-! Generic ordinary-event-fold controls, not concrete PC executions.
One FG holder (9), an honest nonholder (7), and a real signed release followed by a
malformed unsigned release. Both honest nodes remain in every safety conclusion. -/

namespace AvailableChain.FGCompose.Tests.Population
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

private abbrev wire : protocol.Object := ⟨.seat 6 0, row⟩
private abbrev raw : protocol.Object := ⟨.none, row⟩
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.auth with
  | .seat l _ => if l = 6 then some o.payload else none
  | .none => none
private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := id
  decode := decode
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
  events := [.tick 9 6, .tick 7 7]
  seatOf := fun _ _ => 9
  input := fun _ _ => ()
private abbrev selection : FGSelectionReads protocol 1 where
  select := fun _ => (some .genesis, some .genesis)
  clientInputs := reads.inputs

private theorem mixed_client_premises_sat :
    FGHolderClientLaws reads (electorate 1) cfg env run (ordinaryFGExecutionObs env run)
      (safetyHolder reads run) where
  holder_eq _ := rfl
  holder_inj _ _ _ := Subsingleton.elim _ _
  initial_record := rfl
  record_step x k hk := by
    change k < 6 at hk
    by_cases h9 : x = 9
    · subst x; interval_cases k <;> rfl
    by_cases h7 : x = 7
    · subst x; interval_cases k <;> rfl
    interval_cases k <;>
      simp [ordinaryFGExecutionObs, ordinaryCutState, ordinaryEntry, ordinaryEntryStep,
        ordinaryReleaseStep, V2.D.Run.stateBefore, V2.D.World.step,
        V2.D.World.init, V2.D.tick, V2.D.Run.ownSeats, V2.ProtocolSpecD.objSelfVisible,
        protocol, run, env, reads, h9, h7, Ne.symm h9, Ne.symm h7]
  holder_rows j x t i ht hi := by
    have hx : x = 9 := hi.symm
    subst hx
    have hj : j < 2 := (List.getElem?_eq_some_iff.mp ht).1
    interval_cases j
    · have ht' : t = 6 := by simpa [safetyHolder, reads, run] using ht.symm
      subst t
      have hi' : i = 0 := Subsingleton.elim _ _
      subst i
      decide
    · simp at ht
  nonholder_rows j x t ht hn := by
    have hj : j < 2 := (List.getElem?_eq_some_iff.mp ht).1
    interval_cases j
    · have hx : x = 9 := by simpa [V2.Event.node] using
        (congrArg V2.Event.node (Option.some.inj ht)).symm
      exact False.elim (hn 0 hx.symm)
    · have hxt : x = 7 ∧ t = 7 := by simpa using ht.symm
      rcases hxt with ⟨rfl, rfl⟩
      decide

private theorem mixed_wire_premises_sat : FGSafetyWireLaws reads where
  encode_injective := Function.injective_id
  decode_encode _ := rfl
  decode_auth a u hd := by
    rcases a with ⟨auth, payload⟩
    cases auth with
    | none => cases hd
    | seat l i =>
      change (if l = 6 then some payload else none) = some u at hd
      split_ifs at hd with hl
      · subst l
        have hu : payload = u := Option.some.inj hd
        subst u
        exact congrArg (V2.Auth.seat 6) (Subsingleton.elim i payload.signer)
  decoded_visible o u hd := by
    rcases o with ⟨auth, payload⟩
    cases auth with
    | none => cases hd
    | seat l i => rfl
  carried _ _ ha := False.elim (List.not_mem_nil ha)

private theorem mixed_premises_sat :
    run.honest = {7, 9} ∧ run.horizon = 20 ∧
    run.events = [.tick 9 6, .tick 7 7] ∧
    FGSafetyUnitLaws (electorate 1) ∧
    FGSelectionClientLaws selection reads ∧
    FGHolderClientLaws reads (electorate 1) cfg env run (ordinaryFGExecutionObs env run)
      (safetyHolder reads run) ∧ FGSafetyWireLaws reads ∧
    FGHonestSeats reads run = {0} ∧ historyFaulty reads run = ∅ ∧
    V2.D.Run.emitsAt env run 0 = [wire, raw] ∧
    V2.D.Run.emitsAt env run 1 = [raw] ∧ reads.decode raw = none := by
  refine ⟨rfl, rfl, rfl, ?_, ⟨fun _ => rfl⟩, mixed_client_premises_sat,
    mixed_wire_premises_sat, ?_, ?_, ?_, ?_, rfl⟩
  · exact ⟨by decide, by decide,
      fun A => by simp [Electorate.weightOf], by decide⟩
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [FGHonestSeats_def, safetyHolder, reads, run]
  · ext i
    simp [historyFaulty, safetyHolder]
  · decide
  · decide

private theorem mixed_seats_and_rows :
    (FGHonestSeats reads run).card = 1 ∧ run.honest.card = 2 ∧
    (electorate 1).IsQuorum (FGHonestSeats reads run) ∧
    (FGHonestSeats reads run).Nonempty ∧
    (electorate 1).weightOf (historyFaulty reads run) < (electorate 1).q ∧
    ((V2.D.Run.emitsAt env run 0).filter protocol.objSelfVisible).filterMap
      reads.decodeObject = [row] ∧
    (V2.D.Run.emitsAt env run 1).filterMap reads.decodeObject = [] := by
  have hU := mixed_premises_sat.2.2.2.1
  have hF := mixed_premises_sat.2.2.2.2.2.2.2.2.1
  have hf : (historyFaulty reads run).card ≤ (1 - 1) / 3 := by rw [hF]; decide
  have hQ := high_target_honest_quorum_holder reads run (electorate 1) hU hf
  refine ⟨?_, by decide, hQ,
    fgHonestSeats_nonempty_of_quorum reads run (electorate 1) (by decide) hQ,
    fg_fault_weight_of_count reads run (electorate 1) hU hf, ?_, by decide⟩
  · rw [mixed_premises_sat.2.2.2.2.2.2.2.1]; decide
  · have h := selection_tick_rows_holder reads env run (electorate 1) cfg selection
      mixed_premises_sat.2.2.2.2.1 mixed_client_premises_sat 0 0 6 rfl
    exact h.trans (by decide)

private abbrev tip : FGBlock (Fin 1) := .node .genesis 1 genesisRoot 0 [row]
private abbrev core : FGCoreReads protocol 1 Unit Unit protocol.Object where
  core nd := ⟨(), { Store.init with TF := if nd.sent = [] then {.genesis} else {tip} },
    [], []⟩
  erase := fun _ => .genesis
  source := fun _ => none
  headVote := fun _ _ => .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none
private def slashing : Gen.V2.Duty.SlashingInterface (V := Nat) protocol where
  confirmed := fun _ => .genesis
  stable := fun _ => .genesis
  block := fun _ => none
  opening := fun _ => True
  propLabel := fun s => (s : Int)
  propDuty := fun s => (s : Int)
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := Int.ofNat_injective
  finalized := fun _ => .genesis
  slashes rho v := ∃ x y t t' i,
    SlashableBetween (safetyRows core (V2.D.Run.readAt env rho t x))
      (safetyRows core (V2.D.Run.readAt env rho t' y)) i ∧ safetyHolder reads rho i = v

private theorem mixed_safety_premises_sat :
    (∀ t x, safetyCarriage reads env run (safetyRows core (V2.D.Run.readAt env run t x))) ∧
    (∀ i, safetyHolder reads run i ∈ run.honest →
      safetyNoSlash reads env run (safetyHolder reads run i)) ∧
    safetySlashesRead core reads env run slashing ∧
    row ∈ safetyRows core (V2.D.Run.readAt env run 6 9) := by
  refine ⟨?_, ?_, fun _ => Iff.rfl, by decide⟩
  · intro t x u hu
    change u ∈ Finset.biUnion (if _ then {FGBlock.genesis} else {tip}) chainRows at hu
    split_ifs at hu with hn
    · simp [chainRows] at hu
    · have hur : u = row := by simpa [tip, chainRows] using hu
      subst u
      exact ⟨wire, rfl, fun _ => ⟨0, 6, rfl, by decide⟩⟩
  · intro i hi
    exact (ordinary_obsSafetyNoSlash_iff reads env run _).1
      (safety_emitted_noSlash_obs reads (electorate 1) cfg env run _
        (ordinaryFGExecutionObs_laws env run) mixed_client_premises_sat
        mixed_wire_premises_sat i hi)

private theorem mixed_all_honest_safe :
    (∀ x ∈ run.honest, safetyNoSlash reads env run x) ∧
    Gen.V2.Duty.HonestNeverSlashed slashing run ∧
    ¬ slashing.slashes run 7 ∧ ¬ slashing.slashes run 9 := by
  have h := safety_honest_never_slashed_holder reads env run core
    mixed_safety_premises_sat.1 mixed_safety_premises_sat.2.1 slashing
    mixed_safety_premises_sat.2.2.1
  exact ⟨safety_noSlash_all_of_holder reads env run (electorate 1) cfg
    mixed_client_premises_sat mixed_wire_premises_sat mixed_safety_premises_sat.2.1,
    h, h 7 (by decide), h 9 (by decide)⟩

/-- Each old population premise fails solely because the runtime is infinite. -/
private theorem mixed_old_population_blocked :
    ¬ Nonempty (Fin 1 ≃ Nat) ∧ ¬ V2.D.Linked (fun _ => False) run := by
  constructor
  · rintro ⟨e⟩
    exact not_surjective_finite_infinite e e.surjective
  · rintro ⟨N, e, _⟩
    exact not_surjective_finite_infinite e e.surjective

private abbrev frozenEnv : Generic.Env (Fin 1) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true
private abbrev frozenRun : V2.D.Run (Fin 1) protocol where
  honest := {0}
  horizon := 20
  events := [.tick 0 6]
  seatOf := fun _ i => i
  input := fun _ _ => ()

private theorem frozen_premises_sat :
    FGHolderClientLaws reads (electorate 1) cfg frozenEnv frozenRun
      (ordinaryFGExecutionObs frozenEnv frozenRun) (safetyHolder reads frozenRun) ∧
    FGSafetyWireLaws reads ∧
    (∀ i, safetyHolder reads frozenRun i = (Equiv.refl (Fin 1)) i) ∧
    frozenRun.events = [.tick 0 6] ∧ frozenRun.horizon = 20 := by
  refine ⟨?_, mixed_wire_premises_sat, fun _ => rfl, rfl, rfl⟩
  refine ⟨fun _ => rfl, fun _ _ _ => Subsingleton.elim _ _, rfl, ?_, ?_, ?_⟩
  · intro x k hk
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    change k < 3 at hk
    interval_cases k <;> rfl
  · intro j x t i ht _
    have hx : x = 0 := Subsingleton.elim _ _
    have hi : i = 0 := Subsingleton.elim _ _
    subst x i
    have hj : j < 1 := (List.getElem?_eq_some_iff.mp ht).1
    have hj' : j = 0 := by omega
    subst j
    have ht' : t = 6 := by simpa [safetyHolder, reads, frozenRun] using ht.symm
    subst t
    decide
  · intro j x t ht hn
    exact False.elim (hn x rfl)

private def frozenSlashing : Gen.V2.Duty.SlashingInterface (V := Fin 1) protocol :=
  { slashing.toFinalityInterface with
    slashes rho v := ∃ x y t t' i,
      SlashableBetween (safetyRows core (V2.D.Run.readAt frozenEnv rho t x))
        (safetyRows core (V2.D.Run.readAt frozenEnv rho t' y)) i ∧
        safetyHolder reads rho i = v }

private theorem frozen_safety_premises_sat :
    (∀ t x, safetyCarriage reads frozenEnv frozenRun
      (safetyRows core (V2.D.Run.readAt frozenEnv frozenRun t x))) ∧
    (∀ i, safetyHolder reads frozenRun i ∈ frozenRun.honest →
      safetyNoSlash reads frozenEnv frozenRun (safetyHolder reads frozenRun i)) ∧
    safetySlashesRead core reads frozenEnv frozenRun frozenSlashing ∧
    row ∈ safetyRows core (V2.D.Run.readAt frozenEnv frozenRun 6 0) := by
  refine ⟨?_, ?_, fun _ => Iff.rfl, by decide⟩
  · intro t x u hu
    change u ∈ Finset.biUnion (if _ then {FGBlock.genesis} else {tip}) chainRows at hu
    split_ifs at hu with hn
    · simp [chainRows] at hu
    · have hur : u = row := by simpa [tip, chainRows] using hu
      subst u
      exact ⟨wire, rfl, fun _ => ⟨0, 6, rfl, by decide⟩⟩
  · intro i hi
    exact (ordinary_obsSafetyNoSlash_iff reads frozenEnv frozenRun _).1
      (safety_emitted_noSlash_obs reads (electorate 1) cfg frozenEnv frozenRun _
        (ordinaryFGExecutionObs_laws frozenEnv frozenRun) frozen_premises_sat.1
        frozen_premises_sat.2.1 i hi)

private theorem frozen_safety_and_rows :
    (∀ x ∈ frozenRun.honest, safetyNoSlash reads frozenEnv frozenRun x) ∧
    Gen.V2.Duty.HonestNeverSlashed frozenSlashing frozenRun ∧
    ((V2.D.Run.emitsAt frozenEnv frozenRun 0).filter protocol.objSelfVisible).filterMap
      reads.decodeObject = [row] := by
  refine ⟨safety_noSlash_all_of_holder reads frozenEnv frozenRun (electorate 1) cfg
    frozen_premises_sat.1 frozen_premises_sat.2.1 frozen_safety_premises_sat.2.1,
    safety_honest_never_slashed_holder reads frozenEnv frozenRun core
      frozen_safety_premises_sat.1 frozen_safety_premises_sat.2.1 frozenSlashing
      frozen_safety_premises_sat.2.2.1, ?_⟩
  have h := selection_tick_rows_holder reads frozenEnv frozenRun (electorate 1) cfg
    selection ⟨fun _ => rfl⟩ frozen_premises_sat.1 0 0 6 rfl
  exact h.trans (by decide)

#print axioms mixed_client_premises_sat
#print axioms mixed_wire_premises_sat
#print axioms mixed_premises_sat
#print axioms mixed_seats_and_rows
#print axioms mixed_safety_premises_sat
#print axioms mixed_all_honest_safe
#print axioms mixed_old_population_blocked
#print axioms frozen_premises_sat
#print axioms frozen_safety_premises_sat
#print axioms frozen_safety_and_rows

end AvailableChain.FGCompose.Tests.Population
end
