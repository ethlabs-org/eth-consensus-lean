module
public import AvailableChainFGCompose.Proofs.ObservationTransport
public import AvailableChainFGCompose.Proofs.Timing -- shake: keep (axioms)
public import AvailableChainFGCompose.Proofs.Restart

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose.Tests.P0c1
open AvailableChain.SimplexFG AvailableChain.KitFG

-- An inhabited interface model, not a protocol ExecutionValid fixture.
private noncomputable def c1Source : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private noncomputable def c1Head : FGBlock (Fin 1) := .node c1Source 2 ⟨2⟩ 0 []
private noncomputable def c1Electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
private noncomputable def c1Config : FGConfig := ⟨1⟩
private noncomputable def c1Fields := HeadFields.ofBlock c1Electorate c1Config

private noncomputable def c1Clock : FGTiming where
  delta := 1
  roundSlots := 2
  proposal s := 4 * (s : Time)
  vote s := 4 * (s : Time) + 1
  early s := 4 * (s : Time) + 2
  freeze s := 4 * (s : Time) + 3
  release s := 4 * (s : Time) + 5
  gate s := 4 * (s : Time) + 6
  action r := 8 * (r : Time) + 6

private theorem c1ClockLaws : FGTimingLaws c1Clock where
  delta_pos := by decide
  rounds := by decide
  proposal_eq _ := by simp [c1Clock]
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [c1Clock]; ring

private noncomputable abbrev c1Protocol : V2.ProtocolSpecD Unit where
  State := Nat × RecordOnce
  Label := Unit
  Duty := Unit
  signLabel _ := ()
  seats _ := 1
  Payload := Row (Fin 1)
  Durable := RecordOnce
  init := (0, RecordOnce.initial)
  clock st _ := (st.1 + 1, st.2)
  actTime _ := 14
  duties t := if t = 14 then [()] else []
  duties_spec d t := by cases d; by_cases h : t = 14 <;> simp [h, eq_comm]
  duties_nodup t := by split <;> simp
  act st _ _ := (createRowOnce c1Electorate c1Config st.2 0
    (some c1Source) (c1Fields c1Head)).1
  gossip _ _ := []
  process st _ := (st.1 + 10, st.2)
  selfVisible _ := true
  recordOwn st o := (st.1, record_row_once st.2 o.payload)
  durable st := st.2
  restore rec _ := (1, rec)
  wellFormed _ := true
  depsPresent _ _ := true
  processed _ _ := false
  excludes _ _ := false
  handles _ _ _ := False
  carries _ _ := False

private noncomputable def c1Core : FGCoreReads c1Protocol 1 Unit Unit (Row (Fin 1)) where
  core _ := ⟨(), ⟨{.genesis, c1Source, c1Head}, .genesis, .genesis, 0, 1⟩, [], []⟩
  erase _ := .genesis
  source _ := some c1Source
  headVote _ _ := .genesis
  finalityHead _ := some c1Head
  proposalFG _ _ := none

private noncomputable def c1Safety : FGSafetyReads c1Protocol 1 (Row (Fin 1)) where
  proposalErase _ := none
  proposalRows _ := []
  encode row := ⟨.seat () 0, row⟩
  decode row := some row
  decodeObject o := some o.payload
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := Prod.snd
  inputs _ := (some c1Source, c1Fields c1Head)
  enabled t := decide (t = 14)
  finalizedOut _ := .genesis

private noncomputable def c1Pair : FGSelectionReads c1Protocol 1 where
  select _ := (some c1Source, some c1Head)
  clientInputs _ := (some c1Source, c1Fields c1Head)

private noncomputable def c1Observations : FGObservationReads c1Core where
  height := simplexHeightView c1Electorate c1Config
  finality := simplexFinalityView c1Electorate c1Config
  controls nd := treeStoreControlsView (simplexHeightView c1Electorate c1Config)
    (c1Core.core nd).fg
  viable nd X := treeStoreFrameView (simplexHeightView c1Electorate c1Config)
    (c1Core.core nd).fg X

private theorem c1ObservationLaws : FGObservationLaws c1Core c1Observations :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

private theorem c1PairLaws : FGCompose.FGSelectionLaws c1Core c1Observations c1Pair
    (fun _ => True) c1Fields where
  source_eq _ _ := rfl
  head_eq _ _ := rfl
  head_held _ _ := ⟨c1Head, rfl, by simp [c1Core]⟩
  source_viable nd C _ h := by
    cases Option.some.inj h
    change c1Source ∈ c1Observations.viable c1Protocol.init
      (c1Core.core c1Protocol.init).fg.TF
    decide +kernel
  source_head nd C H _ h := by
    cases Option.some.inj (congrArg Prod.fst h)
    cases Option.some.inj (congrArg Prod.snd h)
    decide +kernel
  client_eq nd H _ h := by cases Option.some.inj h; rfl

private theorem c1ClientLaws : FGSelectionClientLaws c1Pair c1Safety := ⟨fun _ => rfl⟩

private theorem c1RowsLaws : FGSafetyClientLaws c1Safety c1Electorate c1Config where
  initial_record := rfl
  clock_record _ _ := rfl
  process_record _ _ := rfl
  restart_record _ _ := rfl
  own_record _ _ := rfl
  tick_rows E rho e hseat nd x t := by
    have hx : e 0 = x := by
      have he : e.symm x = 0 := Subsingleton.elim _ _
      rw [← he, e.apply_symm_apply]
    have hs : rho.seatOf () 0 = x := (hseat 0).trans hx
    have he : e.symm x = 0 := Subsingleton.elim _ _
    cases hr : (createRowOnce c1Electorate c1Config nd.2 0
      (some c1Source) (c1Fields c1Head)).1 <;>
      cases ha : E.awake x t <;> by_cases ht : t = 14
    all_goals simp_all [V2.D.tick, V2.D.Run.ownSeats, c1Protocol, c1Safety,
      List.finRange_succ]
    exact ⟨⟨.seat () 0, _⟩, rfl, rfl⟩

private abbrev c1Env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

private noncomputable def c1Trace : V2.D.Run Unit c1Protocol where
  honest := {()}
  horizon := 15
  events := [.tick () 14]
  seatOf _ _ := ()
  input _ _ := ()

private theorem c1Read : postClock c1Env c1Trace () 14 =
    some (1, RecordOnce.initial) := rfl

private theorem c1PairAtActualRead : ∃ i H,
    c1Trace.events[i]? = some (.tick () 14) ∧
    c1Protocol.clock (V2.D.Run.stateBefore c1Env c1Trace i ()) 14 =
      (1, RecordOnce.initial) ∧
    c1Pair.select (1, RecordOnce.initial) = (some c1Source, some H) ∧
    H ∈ (c1Core.core (1, RecordOnce.initial)).fg.TF ∧ FGBlock.Preceq c1Source H ∧
    c1Safety.inputs (1, RecordOnce.initial) = (some c1Source, c1Fields H) :=
  selection_at_read c1Core c1Safety c1Observations c1Pair (fun _ => True) c1Fields
    c1Env c1Trace c1PairLaws c1ClientLaws c1Read trivial rfl

private theorem c1Released :
    (createRowOnce c1Electorate c1Config RecordOnce.initial 0
      (some c1Source) (c1Fields c1Head)).1 =
      some ⟨0, .vote 1 genesisRoot false, none⟩ := by decide +kernel

private theorem c1ActualRows :
    ((V2.D.tick c1Env c1Trace c1Protocol.init () 14).2.filter
      c1Protocol.objSelfVisible).filterMap c1Safety.decodeObject =
        [⟨0, .vote 1 genesisRoot false, none⟩] := by
  have h := c1RowsLaws.tick_rows c1Env c1Trace (Equiv.ofUnique _ _)
    (fun _ => rfl) c1Protocol.init () 14
  simpa only [c1Safety, c1Protocol, c1Env, decide_true, and_self, ite_true,
    show (Equiv.ofUnique (Fin 1) Unit).symm () = 0 from Subsingleton.elim _ _,
    c1Released, Option.toList_some] using h

private noncomputable def c1WrongPair : FGSelectionReads c1Protocol 1 :=
  { c1Pair with clientInputs := fun _ => (some c1Source, ⟨7, ⟨9⟩, 4⟩) }

private theorem c1RejectWrongClient : ¬ FGSelectionClientLaws c1WrongPair c1Safety := by
  intro h
  have hn : c1WrongPair.clientInputs c1Protocol.init ≠
      c1Safety.inputs c1Protocol.init := by decide +kernel
  exact hn (h.inputs_eq c1Protocol.init)

private theorem c1IndependentReadsStillAgree :
    (c1WrongPair.select c1Protocol.init).1 = c1Core.source c1Protocol.init ∧
    (c1WrongPair.select c1Protocol.init).2 = c1Core.finalityHead c1Protocol.init := ⟨rfl, rfl⟩

private noncomputable def c1VoterObservations : FGObservationReads c1Core :=
  { c1Observations with viable := fun nd X =>
      c1Observations.viable nd (X.filter (fun B => decide (B = .genesis))) }

private theorem c1RejectVoterTree : ¬ FGCompose.FGSelectionLaws c1Core
    c1VoterObservations c1Pair (fun _ => True) c1Fields := by
  intro h
  have hm := h.source_viable c1Protocol.init c1Source trivial rfl
  have hn : c1Source ∉ c1VoterObservations.viable c1Protocol.init
      (c1Core.core c1Protocol.init).fg.TF := by decide +kernel
  exact hn hm

private theorem c1NumericClocks :
    c1Clock.vote 3 = 13 ∧ c1Clock.early 3 = 14 ∧ c1Clock.action 1 = 14 ∧
    c1Clock.gate 3 = 18 ∧ c1Clock.vote 3 < c1Clock.action 1 ∧
    slotStartZ c1Clock (-1) = -4 := by decide

private noncomputable def c1EmptyCore := { c1Core with source := fun _ => none }

private theorem c1OptionCuts :
    actionSourceFG c1EmptyCore c1Env c1Trace c1Clock () 1 = some none ∧
    postClock c1Env c1Trace () 15 = none ∧
    actionSourceFG c1Core c1Env c1Trace c1Clock () 1 = some (some c1Source) :=
  ⟨rfl, rfl, rfl⟩

private noncomputable def c1RestartTrace : V2.D.Run Unit c1Protocol :=
  { c1Trace with events := [.restart () 14, .tick () 14,
      .deliver () (c1Safety.encode ⟨0, .vote 1 genesisRoot false, none⟩) 14] }

private theorem c1DistinctCuts :
    (V2.D.Run.stateBeforeTime c1Env c1RestartTrace 14 ()).1 = 0 ∧
    (postClock c1Env c1RestartTrace () 14).map Prod.fst = some 2 ∧
    (afterTicks c1Env c1RestartTrace 14 ()).1 = 2 ∧
    (V2.D.Run.readAt c1Env c1RestartTrace 14 ()).1 = 12 := by decide +kernel

private theorem c1RestoreEq : FGTreeRestoreLaws c1Core := ⟨fun _ _ => rfl⟩

private def c1CutEnv : Generic.Env Unit :=
  { c1Env with awake := fun _ t => decide (t = 14) }

private theorem c1CutSchedule : V2.D.ScheduleWellFormed c1CutEnv c1RestartTrace where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by
    intro e he
    simp only [c1RestartTrace, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> decide
  honest_only := by intro e he; exact Finset.mem_singleton.mpr (Subsingleton.elim _ _)
  tick_public := by
    intro v t ht
    cases v
    have ht' : t = 14 := by simpa [c1RestartTrace] using ht
    subst t
    exact ⟨14, rfl⟩
  tick_total := by
    intro v hv t ht hn hh ha
    have ht' : t = 14 := of_decide_eq_true ha
    subst t
    cases v
    simp [c1RestartTrace]

private theorem c1SameTimeRestoreTree :
    TFAt c1Core c1CutEnv c1RestartTrace 1 () =
      (c1Core.core (V2.D.Run.stateBeforeTime c1CutEnv c1RestartTrace 14 ())).fg.TF :=
  tf_before_tick_eq_beforeTime c1Core c1CutEnv c1RestartTrace c1CutSchedule c1RestoreEq rfl

#print axioms c1SameTimeRestoreTree

#print axioms c1PairLaws
#print axioms c1RowsLaws
#print axioms c1PairAtActualRead
#print axioms c1ActualRows
#print axioms c1RejectWrongClient
#print axioms c1IndependentReadsStillAgree
#print axioms c1RejectVoterTree
#print axioms c1NumericClocks
#print axioms c1OptionCuts
#print axioms c1DistinctCuts
#print axioms c1RestoreEq

end AvailableChain.FGCompose.Tests.P0c1
end
