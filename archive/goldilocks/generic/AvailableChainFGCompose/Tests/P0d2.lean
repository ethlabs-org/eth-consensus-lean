module
public import AvailableChainFGCompose.Proofs.RowPermission

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d2
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev d2g_E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev d2g_cfg : FGConfig := ⟨4⟩
private abbrev d2g_hd : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev d2g_row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev d2g_old : RecordOnce := record_row_once RecordOnce.initial d2g_row

-- Inhabited pure client inputs. These are not ExecutionValid protocol fixtures.
private theorem d2g_fresh_send :
    (createRowOnce d2g_E d2g_cfg RecordOnce.initial 0 (some .genesis) d2g_hd).1 =
      some d2g_row := by decide +kernel

private theorem d2g_pair_permission :
    namedEntry (height_pair Record.initial (some (1, genesisRoot)) none) =
      some (1, genesisRoot) :=
  p0d2_pair_of_lock _ _ _ _ (Or.inl rfl)

private theorem d2g_fresh_coverage :
    (∃ a, (createRowOnce d2g_E d2g_cfg RecordOnce.initial 0 (some .genesis) d2g_hd).1 =
      some a ∧ namedEntry a.height_pair = some (1, genesisRoot)) ∨
      ∃ b ∈ RecordOnce.initial.sent, namedEntry b.1 = some (1, genesisRoot) := by
  apply p0d2_once_coverage d2g_E d2g_cfg RecordOnce.initial 0 (some .genesis) d2g_hd
    1 genesisRoot recordInv_initial
  · intro g U timeout fp hm
    cases hm
  · exact d2g_pair_permission

private theorem d2g_prior_history : FGRowRecordHistory d2g_old := by
  constructor
  · exact (recordInv_createRowOnce d2g_E d2g_cfg (Λ := RecordOnce.initial) recordInv_initial
      0 (some .genesis) d2g_hd)
  · intro g U timeout fp hm
    change (.vote g U timeout, fp) ∈ [d2g_row.onceKey] at hm
    have he := List.mem_singleton.mp hm
    have hg : g = 1 := by cases he; rfl
    have hU : U = genesisRoot := by cases he; rfl
    have ht : timeout = false := by cases he; rfl
    subst g U timeout
    exact ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩

private theorem d2g_prior_coverage :
    ∃ b ∈ d2g_old.sent, namedEntry b.1 = some (1, genesisRoot) := by
  have hp : namedEntry (height_pair d2g_old.toRecord (some (1, genesisRoot))
      (finality_pair d2g_old.toRecord d2g_hd)) = some (1, genesisRoot) := by
    decide +kernel
  rcases p0d2_once_coverage d2g_E d2g_cfg d2g_old 0 (some .genesis) d2g_hd
      1 genesisRoot d2g_prior_history.invariant d2g_prior_history.sent_history hp with
      ⟨a, ha, _⟩ | hold
  · have hn : (createRowOnce d2g_E d2g_cfg d2g_old 0 (some .genesis) d2g_hd).1 = none := by
      decide +kernel
    rw [hn] at ha
    cases ha
  · exact hold

-- Negative control: permission cannot imply a fresh send after a prior identical row.
private theorem d2g_prior_no_fresh :
    (createRowOnce d2g_E d2g_cfg d2g_old 0 (some .genesis) d2g_hd).1 = none := by
  decide +kernel

-- Negative control: a different lock at the selected height blocks the computed pair.
private theorem d2g_wrong_lock :
    let Λ := Record.initial.with_lock 1 ⟨9⟩
    ¬ (own_lock Λ 1 none = none ∨ own_lock Λ 1 none = some genesisRoot) ∧
      namedEntry (height_pair Λ (some (1, genesisRoot)) none) = none := by
  decide +kernel

-- A durable resume keeps the full sent key and suppresses the same entry.
private theorem d2g_durable_resume :
    clientRunOnce d2g_E d2g_cfg 0
      (clientRecordOnce d2g_E d2g_cfg 0 RecordOnce.initial [(some .genesis, d2g_hd)])
      [(some .genesis, d2g_hd)] = [] := by
  decide +kernel

-- Labelled generic interface trace; this is not an FG-SA ExecutionValid fixture.
-- The engine signs the fresh row, records it, restarts, and suppresses the repeat.
noncomputable section
private abbrev d2t_P : V2.ProtocolSpecD Unit where
  State := RecordOnce
  Label := Unit
  Duty := Time
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := RecordOnce
  init := RecordOnce.initial
  clock := fun nd _ => nd
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun nd _ _ => (createRowOnce d2g_E d2g_cfg nd 0 (some .genesis) d2g_hd).1
  gossip := fun _ _ => []
  process := fun nd _ => nd
  selfVisible := fun _ => true
  recordOwn := fun nd o => match o.auth with
    | .seat _ i => record_row_once nd { o.payload with signer := i }
    | .none => nd
  durable := id
  restore := fun nd _ => nd
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev d2t_S : FGSafetyReads d2t_P 1 d2t_P.Object where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := id
  decode := fun o => match o.auth with
    | .seat _ i => some { o.payload with signer := i }
    | .none => none
  decodeObject := fun o => match o.auth with
    | .seat _ i => some { o.payload with signer := i }
    | .none => none
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := id
  inputs := fun _ => (some .genesis, d2g_hd)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

private abbrev d2t_entry (a : d2t_P.Object) := namedEntry a.payload.height_pair
private abbrev d2t_wire : d2t_P.Object := ⟨.seat () 0, d2g_row⟩
private abbrev d2t_T : FGTiming where
  delta := 1
  roundSlots := 2
  proposal := fun s => 4 * s
  vote := fun s => 4 * s + 1
  early := fun s => 4 * s + 2
  freeze := fun s => 4 * s + 3
  release := fun s => 4 * s + 5
  gate := fun s => 4 * s + 6
  action := fun r => 4 * (r * 2 : Nat) + 6

private theorem d2t_timing : FGTimingLaws d2t_T where
  delta_pos := by decide
  rounds := by decide
  proposal_eq := by intro s; simp
  vote_eq := by intro s; rfl
  early_eq := by intro s; rfl
  freeze_eq := by intro s; rfl
  release_eq := by intro s; rfl
  gate_eq := by intro s; rfl
  action_eq := by intro r; rfl

private abbrev d2t_env : Generic.Env (Fin 1) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ t => decide (t = 6 ∨ t = 14)

private abbrev d2t_run : V2.D.Run (Fin 1) d2t_P where
  honest := {0}
  horizon := 14
  events := [.tick 0 6, .restart 0 14, .tick 0 14]
  seatOf := fun _ i => i
  input := fun _ _ => ()

private theorem d2t_schedule : V2.D.ScheduleWellFormed d2t_env d2t_run where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by
    intro ev hm
    change ev ∈ [.tick 0 6, .restart 0 14, .tick 0 14] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  honest_only := by
    intro ev hm
    change ev ∈ [.tick 0 6, .restart 0 14, .tick 0 14] at hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide
  tick_public := by
    intro x t hm
    change V2.Event.tick x t ∈ [.tick 0 6, .restart 0 14, .tick 0 14] at hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
      reduceCtorEq, or_false, false_or] at hm
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨14, rfl⟩
  tick_total := by
    intro x _ t _ _ _ ha
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    have ht : t = 6 ∨ t = 14 := of_decide_eq_true ha
    rcases ht with rfl | rfl <;> simp

private theorem d2t_client : FGSafetyClientLaws d2t_S d2g_E d2g_cfg where
  initial_record := rfl
  clock_record _ _ := rfl
  process_record _ _ := rfl
  restart_record _ _ := rfl
  own_record := by
    intro nd o
    cases o with
    | mk auth payload => cases auth <;> rfl
  tick_rows := by
    intro V _ E rho e he nd x t
    have hx : e 0 = x := by
      rw [← e.apply_symm_apply x]
      congr 1
      exact Subsingleton.elim _ _
    have hs : e.symm x = 0 := Subsingleton.elim _ _
    have hseat : rho.seatOf () 0 = x := (he 0).trans hx
    have hsigner : ∀ u : Row (Fin 1), { u with signer := (0 : Fin 1) } = u := by
      intro u
      have hu : u.signer = 0 := Subsingleton.elim _ _
      cases u
      cases hu
      rfl
    cases ha : E.awake x t <;>
      cases hr : (createRowOnce d2g_E d2g_cfg nd 0 (some .genesis) d2g_hd).1 <;>
      simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ha, hs, hr, hseat]
    rename_i u
    change [{ u with signer := (0 : Fin 1) }] = [u]
    rw [hsigner]

private theorem d2t_wires : FGRowPermissionWireLaws d2t_S d2t_entry where
  decoded_wire := by
    intro o u hu
    refine ⟨o, rfl, hu, ?_⟩
    cases o with
    | mk auth payload =>
      cases auth with
      | none => cases hu
      | seat label i => cases hu; rfl

private theorem d2t_permission (nd : RecordOnce)
    (hnd : nd = RecordOnce.initial ∨ nd = d2g_old) :
    FGRowPermissionInputs d2t_S (simplexHeightView d2g_E d2g_cfg) nd .genesis := by
  refine ⟨rfl, ?_⟩
  rcases hnd with rfl | rfl <;> exact Or.inl (by decide +kernel)

private theorem d2t_fresh_origin :
    HonestRowAt d2t_S d2t_env d2t_run d2t_T 0 0 0 d2t_wire := by
  refine ⟨by decide, rfl, ?_⟩
  decide +kernel

private theorem d2t_restart_record :
    V2.D.Run.stateBefore d2t_env d2t_run 1 0 = d2g_old ∧
    V2.D.Run.stateBefore d2t_env d2t_run 2 0 = d2g_old ∧
    d2t_run.events[1]? = some (.restart 0 (d2t_T.action 1)) := by
  refine ⟨?_, ?_, rfl⟩ <;> rfl

private theorem d2t_prior_origin :
    ∀ b ∈ (d2t_S.record (V2.D.Run.stateBefore d2t_env d2t_run 2 0)).sent,
      ∃ j rSent a, j < 2 ∧ HonestRowAt d2t_S d2t_env d2t_run d2t_T j 0 rSent a ∧
        d2t_entry a = namedEntry b.1 := by
  rw [d2t_restart_record.2.1]
  intro b hb
  have hb' : b = d2g_row.onceKey := List.mem_singleton.mp hb
  subst b
  exact ⟨0, 0, d2t_wire, by decide, d2t_fresh_origin, rfl⟩

-- Apply the actual consumer at the fresh action, with every premise supplied.
private theorem d2t_fresh_covered :
    ∃ j rSent a, rSent ≤ 0 ∧ HonestRowAt d2t_S d2t_env d2t_run d2t_T j 0 rSent a ∧
      d2t_entry a = some (1, genesisRoot) := by
  apply rowPermission_covered d2t_S (simplexHeightView d2g_E d2g_cfg) d2g_E d2g_cfg
    d2t_T d2t_timing d2t_env d2t_run d2t_client d2t_entry d2t_wires
    (Equiv.refl _) (fun _ => rfl) d2t_schedule (fun _ => rfl) 0 (by decide)
    0 0 RecordOnce.initial rfl rfl .genesis
    (d2t_permission _ (Or.inl rfl)) ⟨recordInv_initial, ?_⟩ ?_ rfl rfl
  · intro g U timeout fp hm; cases hm
  · intro b hb; cases hb

-- At round 1 the same node emits no wire; coverage must use round 0's full wire.
private theorem d2t_repeat_suppressed :
    V2.D.Run.emitsAt d2t_env d2t_run 2 = [] := by decide +kernel

private theorem d2t_restart_covered :
    ∃ j rSent a, rSent ≤ 1 ∧ HonestRowAt d2t_S d2t_env d2t_run d2t_T j 0 rSent a ∧
      d2t_entry a = some (1, genesisRoot) := by
  apply rowPermission_covered d2t_S (simplexHeightView d2g_E d2g_cfg) d2g_E d2g_cfg
    d2t_T d2t_timing d2t_env d2t_run d2t_client d2t_entry d2t_wires
    (Equiv.refl _) (fun _ => rfl) d2t_schedule (fun _ => rfl) 0 (by decide)
    1 2 d2g_old rfl d2t_restart_record.2.1 .genesis
    (d2t_permission _ (Or.inr rfl)) d2g_prior_history d2t_prior_origin rfl rfl

-- Check the consumer's witness, including its earlier index and numerical bound.
private theorem d2t_exact_prior_witness :
    ∃ j rSent a, j = 0 ∧ rSent = 0 ∧ a = d2t_wire ∧ j < 2 ∧ rSent ≤ 1 ∧
      HonestRowAt d2t_S d2t_env d2t_run d2t_T j 0 rSent a ∧
      d2t_entry a = some (1, genesisRoot) := by
  obtain ⟨j, rSent, a, hr, hj, he⟩ := d2t_restart_covered
  have hja : j = 0 ∧ rSent = 0 ∧ a = d2t_wire := by
    rcases hj with ⟨_, ht, ha⟩
    have hidx : j < 3 := (List.getElem?_eq_some_iff.mp ht).1
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · have ht' : 6 = 4 * ((rSent : Int) * 2) + 6 := by
        exact Option.some.inj (congrArg (fun ev => ev.map V2.Event.time) ht)
      have hround : rSent = 0 := by omega
      have hwire : a = d2t_wire := List.mem_singleton.mp ha
      exact ⟨rfl, hround, hwire⟩
    · cases ht
    · rw [d2t_repeat_suppressed] at ha; cases ha
  exact ⟨j, rSent, a, hja.1, hja.2.1, hja.2.2, by omega, hr, hj, he⟩

end

#print axioms d2g_fresh_send
#print axioms d2g_pair_permission
#print axioms d2g_fresh_coverage
#print axioms d2g_prior_history
#print axioms d2g_prior_coverage
#print axioms d2g_prior_no_fresh
#print axioms d2g_wrong_lock
#print axioms d2g_durable_resume
#print axioms AvailableChain.FGCompose.rowPermission_covered
#print axioms d2t_timing
#print axioms d2t_schedule
#print axioms d2t_client
#print axioms d2t_wires
#print axioms d2t_permission
#print axioms d2t_fresh_origin
#print axioms d2t_restart_record
#print axioms d2t_prior_origin
#print axioms d2t_fresh_covered
#print axioms d2t_repeat_suppressed
#print axioms d2t_restart_covered
#print axioms d2t_exact_prior_witness

end AvailableChain.FGCompose.Tests.P0d2
end
