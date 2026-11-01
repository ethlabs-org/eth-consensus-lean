module
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport -- shake: keep (test uses)
public import AvailableChainFGSAProofs.Proofs.Finality.Rows -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge -- shake: keep (test uses)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.P0a
open AvailableChain.SimplexFG AvailableChain.FGCompose

private theorem tree_restore (p : Params) {In : Type} (c : AppCodec In) :
    FGTreeRestoreLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [fgsaCoreReads_def]
  exact congrArg (fun st => st.TF) (acRestart_fg p nd.st t)

private theorem tree_keep (p : Params) {In : Type} (c : AppCodec In) :
    FGTreeKeepLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [(tree_restore p c).restart_eq]

private theorem fgsa_retained_tree (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {i j : Nat} (hij : i ≤ j) (x : V) :
    (V2.D.Run.stateBefore E rho i x).st.fg.TF ⊆ (V2.D.Run.stateBefore E rho j x).st.fg.TF := by
  have h := tf_cumulative_all (fgsaCoreReads p c) E rho (fgsaCoreLaws p c)
    (tree_keep p c) hij x
  rw [TFAt_def, TFAt_def, fgsaCoreReads_def] at h
  exact h

private theorem strict_tick_tree (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {t : Time} (hi : rho.events[i]? = some (.tick x t)) :
    (V2.D.Run.stateBefore E rho i x).st.fg.TF =
      (V2.D.Run.stateBeforeTime E rho t x).st.fg.TF := by
  have h := tf_before_tick_eq_beforeTime (fgsaCoreReads p c) E rho hs (tree_restore p c) hi
  rw [TFAt_def, fgsaCoreReads_def] at h
  exact h

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private abbrev env : Generic.Env (Fin 3) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => false

-- A reachable, inhabited carrier-read interface model, not an ExecutionValid fixture.
-- The real FG-SA core supplier gives the injective erase map for nonempty rows.
private abbrev carrierProtocol : V2.ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := Unit
  init := true
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => false
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private def carrierRow : Row (Fin params.n) := ⟨0, .empty, none⟩
private def rowCarrier : FGBlock (Fin params.n) := .node .genesis 1 ⟨1⟩ 0 [carrierRow]

private noncomputable abbrev carrierReads :
    FGCoreReads carrierProtocol params.n Unit Unit Unit where
  core _ := ⟨(), ⟨{.genesis, rowCarrier}, .genesis, .genesis, 0, 1⟩, [], []⟩
  erase := (fgsaCoreReads params unitCodec).erase
  source := fun _ => some rowCarrier
  headVote := fun _ _ => (fgsaCoreReads params unitCodec).erase rowCarrier
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem carrier_core_laws : FGCoreLaws carrierReads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf _ _ := fun _ h => h
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases Option.some.inj h; simp
  erase_inj := (fgsaCoreLaws params unitCodec).erase_inj

private theorem carrier_restore_laws : FGTreeRestoreLaws carrierReads := ⟨fun _ _ => rfl⟩

private noncomputable abbrev carrierTrace : V2.D.Run (Fin 3) carrierProtocol where
  honest := {0}
  horizon := 1
  events := [.restart 0 1, .tick 0 1]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

private theorem carrier_schedule : V2.D.ScheduleWellFormed env carrierTrace where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> norm_num [V2.Event.time]
  honest_only := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [V2.Event.node]
  tick_public := by
    intro v t ht
    have ht' : v = 0 ∧ t = 1 := by simpa using ht
    have ht1 := ht'.2
    subst t
    exact ⟨1, by norm_num⟩
  tick_total := by intro v hv t ht hn hh ha; cases ha

private theorem carrier_head_laws : FGHeadLaws carrierReads env carrierTrace where
  head_mem _ _ _ _ := ⟨rowCarrier, by simp, rfl⟩
  parent_closed _ _ B hB := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB ⊢
    rcases hB with rfl | rfl <;> simp [rowCarrier, FGBlock.parent]

private theorem carrier_row_reachable :
    0 < params.n ∧ carrierRow ∈ rowCarrier.rows ∧
      rowCarrier ∈ TFAt carrierReads env carrierTrace 0 0 ∧
      rowCarrier ∈ TFAt carrierReads env carrierTrace 1 0 := by
  refine ⟨by decide, by simp [rowCarrier, FGBlock.rows], ?_, ?_⟩ <;> simp [TFAt]

private theorem carrier_equal_time_state_differs :
    V2.D.Run.stateBefore env carrierTrace 1 0 ≠
      V2.D.Run.stateBeforeTime env carrierTrace 1 0 := by decide

private theorem inhabited_strict_chain_read :
    FGCompose.ChainRowsBefore carrierReads env carrierTrace rowCarrier 2 :=
  chainRows_of_head_all carrierReads env carrierTrace carrier_core_laws carrier_head_laws
    carrier_schedule carrier_restore_laws (x := 0) (by simp)
    (s := 1) (t := 1) (by rfl) 2 (by norm_num)

private theorem inhabited_row_holds_before :
    ∃ x t, x ∈ carrierTrace.honest ∧ t < 2 ∧
      Gen.V2.Duty.HoldsBefore env carrierTrace
        (fun nd => rowCarrier ∈ (carrierReads.core nd).fg.TF) t x := by
  exact inhabited_strict_chain_read rowCarrier (AvailableChain.KitFG.preceq_refl _)
    carrierRow carrier_row_reachable.2.1

-- An inhabited FG electorate and two faulty nodes with no FG seat.
-- This is a population interface model, not an ExecutionValid fixture.
private abbrev trace : V2.D.Run (Fin 3) (fgsa params unitCodec) where
  honest := {0}
  horizon := 1
  events := []
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

private theorem off_electorate_counts :
    (Finset.univ.filter (fun i : Fin params.n =>
      safetyHolder (fgsaSafetyReads params unitCodec) trace i ∉ trace.honest)).card = 0 ∧
    (Gen.V2.Duty.faulty trace).card = 2 := by decide

private theorem fg_strict_premise :
    (Finset.univ.filter (fun i : Fin params.n =>
      safetyHolder (fgsaSafetyReads params unitCodec) trace i ∉ trace.honest)).card <
        2 * Gen.Pure.qF params.n - params.n := by decide

private theorem node_strict_premise_fails :
    ¬ (Gen.V2.Duty.faulty trace).card < 2 * Gen.Pure.qF params.n - params.n := by decide

private theorem no_run_blocks (B : FGBlock (Fin params.n)) :
    ¬ safetyRunBlock (fgsaCoreReads params unitCodec) (fgsaSafetyReads params unitCodec)
      env trace B := by
  simp [safetyRunBlock, V2.D.Run.emits, trace]

private theorem no_emitted_slash (x : Fin 3) :
    safetyNoSlash (fgsaSafetyReads params unitCodec) env trace x := by
  intro a b ha
  obtain ⟨k, t, hk, _⟩ := ha
  simp at hk

private theorem off_electorate_bound :
    safetyBound (fgsaCoreReads params unitCodec) (fgsaSafetyReads params unitCodec)
      params.E env trace :=
  safety_fault_count_bound_fg_lt (fgsaCoreReads params unitCodec)
    (fgsaSafetyReads params unitCodec) params.E env trace (fgsaSafetyUnitLaws params)
    (fun B hB => False.elim (no_run_blocks B hB)) (fun x _ => no_emitted_slash x)
    fg_strict_premise

#print axioms tree_restore
#print axioms tree_keep
#print axioms fgsa_retained_tree
#print axioms strict_tick_tree
#print axioms carrier_core_laws
#print axioms carrier_restore_laws
#print axioms carrier_schedule
#print axioms carrier_head_laws
#print axioms carrier_row_reachable
#print axioms carrier_equal_time_state_differs
#print axioms inhabited_strict_chain_read
#print axioms inhabited_row_holds_before
#print axioms off_electorate_counts
#print axioms fg_strict_premise
#print axioms node_strict_premise_fails
#print axioms off_electorate_bound
#print axioms AvailableChain.FGSA.Run.kmid_chainRows_of_head
#print axioms AvailableChain.FGSA.Run.kmid_head_held_from
#print axioms AvailableChain.FGSA.Run.finality_action_source
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_finalizedMonotone_restart

end AvailableChain.FGSA.Run.Tests.P0a
end
