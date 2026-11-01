module
public import AvailableChainFGCompose.Proofs.Finality.History -- shake: keep (window law fixture)
public import AvailableChainFGCompose.Proofs.Finality.RecordInv

set_option linter.privateModule false

public section
namespace AvailableChain.FGCompose.Tests.P0d7a2
open AvailableChain.SimplexFG AvailableChain.KitFG

-- The approved layer repair is equal to the original own-release predicate.
private theorem d7g_own_origin_expansion
    {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
    {n : Nat} {Wire : Type} (S : FGSafetyReads P n Wire) (T : FGTiming)
    (E : Generic.Env V) (rho : V2.D.Run V P) :
    HighRecordOwnOrigin S T E rho =
      (∀ j x o u, x ∈ rho.honest →
        o ∈ V2.D.Engine.ownReleasedAt E rho x j →
        S.decodeObject o = some u →
        ∃ r a, HonestRowAt S E rho T j x r a ∧ S.decode a = some u) := by
  simp only [HighRecordOwnOrigin, V2.D.Engine.ownReleasedAt_def]

-- Client and freshness fixture; no full certificate-origin instance is claimed.
private abbrev d7g_E : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev d7g_cfg : FGConfig := ⟨4⟩
private abbrev d7g_hd : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev d7g_boot : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev d7g_X : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [d7g_boot]
private abbrev d7g_Y : FGBlock (Fin 1) := .node d7g_X 2 ⟨2⟩ 0 []
private abbrev d7g_Z : FGBlock (Fin 1) := .node .genesis 1 ⟨9⟩ 0 [d7g_boot]
private abbrev d7g_row : Row (Fin 1) := ⟨0, .vote 2 ⟨1⟩ false, none⟩
private abbrev d7g_old : RecordOnce := record_row_once RecordOnce.initial d7g_row
private abbrev d7g_source (nd : RecordOnce) := if nd.sent.isEmpty then d7g_X else d7g_Y

private theorem d7g_parent_paths :
    d7g_X ≠ .genesis ∧ d7g_Y.parent = d7g_X ∧ FGBlock.Preceq d7g_X d7g_Y ∧
      (derive d7g_E d7g_cfg d7g_X).h = 2 ∧ (derive d7g_E d7g_cfg d7g_Y).h = 2 := by
  decide +kernel

private theorem d7g_current :
    (createRowOnce d7g_E d7g_cfg RecordOnce.initial 0 (some d7g_X) d7g_hd).1 =
      some d7g_row := by decide +kernel

private theorem d7g_guard_choice :
    height_pair d7g_old.toRecord (some (2, ⟨1⟩)) none = .vote 2 ⟨1⟩ false := by
  exact high_record_target_choice _ _ _ _ (Or.inr (by decide +kernel)) rfl (Or.inl rfl)
    (by intro f h; cases h)

private theorem d7g_prior :
    (createRowOnce d7g_E d7g_cfg d7g_old 0 (some d7g_Y) d7g_hd).1 = none ∧
      d7g_row.onceKey ∈ d7g_old.sent := by decide +kernel

private theorem d7g_timeout_rejected :
    ¬ HighRecordGuard_W (record_row_once RecordOnce.initial
      (⟨0, .vote 2 ⟨1⟩ true, none⟩ : Row (Fin 1))) 2 d7g_X := by
  intro h
  have hf : true = false := h.2.1
  cases hf

private theorem d7g_wrong_target_rejected :
    ¬ HighRecordGuard_W (record_row_once RecordOnce.initial
      (⟨0, .vote 2 ⟨9⟩ false, none⟩ : Row (Fin 1))) 2 d7g_X := by
  intro h
  rcases h.1 with h | h <;> cases h

private theorem d7g_finality_lock :
    height_pair Record.initial (some (2, ⟨1⟩)) (some ⟨2, ⟨1⟩⟩) = .vote 2 ⟨1⟩ false ∧
    height_pair Record.initial (some (2, ⟨1⟩)) (some ⟨2, ⟨9⟩⟩) = .empty := by
  decide +kernel

noncomputable section
private abbrev d7t_P : V2.ProtocolSpecD Unit where
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
  act := fun nd _ _ => (createRowOnce d7g_E d7g_cfg nd 0 (some (d7g_source nd)) d7g_hd).1
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

private abbrev d7t_S : FGSafetyReads d7t_P 1 d7t_P.Object where
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
  inputs := fun nd => (some (d7g_source nd), d7g_hd)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

private abbrev d7t_entry (a : d7t_P.Object) := namedEntry a.payload.height_pair
private abbrev d7t_wire : d7t_P.Object := ⟨.seat () 0, d7g_row⟩
private abbrev d7t_T : FGTiming where
  delta := 1
  roundSlots := 2
  proposal := fun s => 4 * s
  vote := fun s => 4 * s + 1
  early := fun s => 4 * s + 2
  freeze := fun s => 4 * s + 3
  release := fun s => 4 * s + 5
  gate := fun s => 4 * s + 6
  action := fun r => 4 * (r * 2 : Nat) + 6

private theorem d7t_timing : FGTimingLaws d7t_T where
  delta_pos := by decide
  rounds := by decide
  proposal_eq := by intro s; simp
  vote_eq := by intro s; rfl
  early_eq := by intro s; rfl
  freeze_eq := by intro s; rfl
  release_eq := by intro s; rfl
  gate_eq := by intro s; rfl
  action_eq := by intro r; rfl

private abbrev d7t_env : Generic.Env (Fin 1) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ t => decide (t = 6 ∨ t = 14)

private abbrev d7t_run : V2.D.Run (Fin 1) d7t_P where
  honest := {0}
  horizon := 14
  events := [.tick 0 6, .restart 0 14, .tick 0 14]
  seatOf := fun _ i => i
  input := fun _ _ => ()

private theorem d7t_schedule : V2.D.ScheduleWellFormed d7t_env d7t_run where
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

private theorem d7t_client : FGSafetyClientLaws d7t_S d7g_E d7g_cfg where
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
      cases hr : (createRowOnce d7g_E d7g_cfg nd 0 (some (d7g_source nd)) d7g_hd).1 <;>
      simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, ha, hs, hr, hseat]
    rename_i u
    change [{ u with signer := (0 : Fin 1) }] = [u]
    rw [hsigner]

private theorem d7t_wires : FGRowPermissionWireLaws d7t_S d7t_entry where
  decoded_wire := by
    intro o u hu
    refine ⟨o, rfl, hu, ?_⟩
    cases o with
    | mk auth payload =>
      cases auth with
      | none => cases hu
      | seat label i => cases hu; rfl

private abbrev d7t_D : FGHistoryWireReads d7t_S where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer a := match a.auth with | .seat _ i => some i | .none => none
  decode_height a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl
  decode_finality a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl
  decode_signer a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl

private theorem d7t_fresh_origin :
    HonestRowAt d7t_S d7t_env d7t_run d7t_T 0 0 0 d7t_wire := by
  refine ⟨by decide, rfl, ?_⟩
  decide +kernel

private theorem d7t_restart_record :
    V2.D.Run.stateBefore d7t_env d7t_run 1 0 = d7g_old ∧
    V2.D.Run.stateBefore d7t_env d7t_run 2 0 = d7g_old ∧
    d7t_run.events[1]? = some (.restart 0 (d7t_T.action 1)) := by
  exact ⟨rfl, rfl, rfl⟩

private theorem d7t_suppressed :
    V2.D.Run.emitsAt d7t_env d7t_run 2 = [] := by decide +kernel

private theorem d7t_only_row {j r : Nat} {x : Fin 1} {a : d7t_P.Object}
    (ha : HonestRowAt d7t_S d7t_env d7t_run d7t_T j x r a) :
    j = 0 ∧ x = 0 ∧ r = 0 ∧ a = d7t_wire := by
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  rcases ha with ⟨_, ht, ha⟩
  have hidx : j < 3 := (List.getElem?_eq_some_iff.mp ht).1
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl | rfl
  · have ht' : 6 = 4 * ((r : Int) * 2) + 6 := by
      exact Option.some.inj (congrArg (fun ev => ev.map V2.Event.time) ht)
    have hr : r = 0 := by omega
    have hw : a = d7t_wire := List.mem_singleton.mp ha
    exact ⟨rfl, rfl, hr, hw⟩
  · cases ht
  · rw [d7t_suppressed] at ha; cases ha

private theorem d7t_emission :
    HighRecordEmission d7t_S d7t_T d7t_env d7t_run d7g_E d7g_cfg := by
  intro j x r a u ha hd
  obtain ⟨rfl, rfl, rfl, rfl⟩ := d7t_only_row ha
  have hu : d7g_row = u := Option.some.inj hd
  subst u
  exact d7g_current

private theorem d7t_own : HighRecordOwnOrigin d7t_S d7t_T d7t_env d7t_run := by
  rw [HighRecordOwnOrigin_def]
  intro j x o u _hx ho hd
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  rw [V2.D.Engine.ownReleasedAt_def] at ho
  split at ho
  · rename_i hnode
    have hem := (List.mem_filter.mp ho).1
    have hidx : j < 3 := by
      by_contra hn
      have hnone : d7t_run.events[j]? = none := List.getElem?_eq_none (by change 3 ≤ j; omega)
      rw [hnone] at hnode
      cases hnode
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    · have hw : o = d7t_wire := List.mem_singleton.mp hem
      subst o
      exact ⟨0, d7t_wire, d7t_fresh_origin, hd⟩
    · cases hem
    · rw [d7t_suppressed] at hem; cases hem
  · cases ho

private theorem d7t_fresh_after_restart :
    HighRecordFresh 3 (d7t_S.record (V2.D.Run.stateBefore d7t_env d7t_run 2 0)) := by
  apply high_record_fresh_at_cut (D := d7t_D) d7t_client d7t_emission d7t_own 2 0 3 (by decide)
  intro j r a h _hj ha hh
  obtain ⟨rfl, _, rfl, rfl⟩ := d7t_only_row ha
  have he : 2 = h := Option.some.inj hh
  omega

private theorem d7t_prior_exact :
    ∃ j r a, j = 0 ∧ r = 0 ∧ a = d7t_wire ∧ j < 2 ∧
      HonestRowAt d7t_S d7t_env d7t_run d7t_T j 0 r a ∧
      d7t_D.heightPair a = .vote 2 ⟨1⟩ false :=
  ⟨0, 0, d7t_wire, rfl, rfl, rfl, by decide, d7t_fresh_origin, rfl⟩

private def d7t_erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (d7t_erase p) s r (encFGBody x rs)

private theorem d7t_erase_inj : Function.Injective d7t_erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [d7t_erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [d7t_erase] at h
    | node q t u y ts =>
      simp only [d7t_erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private theorem d7t_reflect (A B : FGBlock (Fin 1))
    (h : Block.Preceq (d7t_erase A) (d7t_erase B)) : FGBlock.Preceq A B := by
  induction B with
  | genesis =>
    have he : d7t_erase A = d7t_erase .genesis := of_decide_eq_true h
    exact d7t_erase_inj he ▸ preceq_refl _
  | node P slot root app rows ih =>
    change (decide (d7t_erase A = d7t_erase (.node P slot root app rows)) ||
      Block.preceq (d7t_erase A) (d7t_erase P)) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with he | hp
    · exact d7t_erase_inj (of_decide_eq_true he) ▸ preceq_refl _
    · exact preceq_node_of_preceq slot root app rows (ih hp)

private abbrev d7t_R : FGCoreReads d7t_P 1 Unit Unit d7t_P.Object where
  core _ := ⟨(), ⟨{.genesis, d7g_X, d7g_Y}, .genesis, .genesis, 0, 2⟩, [], []⟩
  erase := d7t_erase
  source nd := some (d7g_source nd)
  headVote _ _ := d7t_erase d7g_Y
  finalityHead _ := some d7g_Y
  proposalFG _ _ := none

private abbrev d7t_O : FGObservationReads d7t_R where
  height := KitFG.Window.certificateHeight d7g_E d7g_cfg 2
  finality := KitFG.Window.certificateFinality d7g_E d7g_cfg 2
  controls nd := treeStoreControlsView (simplexHeightView d7g_E d7g_cfg) (d7t_R.core nd).fg
  viable _ trees := trees

private abbrev d7t_point : FGServicePoint :=
  ⟨⟨0, 0, 1, 0, 0, d7t_erase d7g_X⟩, 2, d7t_erase d7g_Y, 8⟩

private theorem d7t_source_cases {x : Fin 1} {r : Nat} {C : FGBlock (Fin 1)}
    (h : actionSourceFG d7t_R d7t_env d7t_run d7t_T x r = some (some C)) :
    C = d7g_X ∨ C = d7g_Y := by
  obtain ⟨nd, _, hs⟩ := Option.map_eq_some_iff.mp h
  have he : d7g_source nd = C := Option.some.inj hs
  unfold d7g_source at he
  split at he
  · exact Or.inl he.symm
  · exact Or.inr he.symm

private theorem d7t_history (horizon : Time) :
    FGHistoricalHighChain d7t_R d7t_O d7t_T d7t_env d7t_run d7t_point horizon := by
  intro x z r q C B _hx _hz hC hB _hc _hb _hr _hq
  rcases d7t_source_cases hC with rfl | rfl <;>
    rcases d7t_source_cases hB with rfl | rfl
  all_goals exact ⟨by unfold Block.Compatible; decide +kernel,
    by unfold Block.Compatible; decide +kernel⟩

private theorem d7t_pre_service_sources :
    actionSourceFG d7t_R d7t_env d7t_run d7t_T 0 0 = some (some d7g_X) ∧
    actionSourceFG d7t_R d7t_env d7t_run d7t_T 0 1 = some (some d7g_Y) ∧
    d7t_T.action 0 < d7t_point.serviceStart := by
  decide +kernel

private theorem d7t_equal_height_entry :
    (d7t_O.height d7g_X).T_h = (d7t_O.height d7g_Y).T_h := by
  exact high_source_entry_eq d7t_history
    (KitFG.Window.windowCertificateLaws d7g_E d7g_cfg 2
      (by unfold Electorate.IsQuorum; decide +kernel) (by decide))
    d7t_reflect 0 0 0 1 d7g_X d7g_Y (by decide) (by decide) d7t_pre_service_sources.1
    d7t_pre_service_sources.2.1 (by unfold high; decide +kernel)
    (by unfold high; decide +kernel) (by decide +kernel)


private abbrev d7t_badR : FGCoreReads d7t_P 1 Unit Unit d7t_P.Object :=
  { d7t_R with source := fun nd => some (if nd.sent.isEmpty then d7g_Z else d7g_Y) }

private abbrev d7t_badO : FGObservationReads d7t_badR where
  height := KitFG.Window.certificateHeight d7g_E d7g_cfg 2
  finality := KitFG.Window.certificateFinality d7g_E d7g_cfg 2
  controls nd := d7t_O.controls nd
  viable _ trees := trees

-- A high row from the earlier fork has a real parent path and a different entry.
private theorem d7t_fork_nontrivial :
    d7g_Z ≠ .genesis ∧ (d7t_O.height d7g_Z).h = 2 ∧
      (d7t_O.height d7g_Z).T_h ≠ (d7t_O.height d7g_Y).T_h ∧
      ¬ Block.Compatible (d7t_erase d7g_Z) (d7t_erase d7g_Y) := by
  unfold Block.Compatible
  decide +kernel

private theorem d7t_reject_historical_fork :
    ¬ FGHistoricalHighChain d7t_badR d7t_badO d7t_T d7t_env d7t_run d7t_point 14 := by
  intro h
  have bad := (h 0 0 0 1 d7g_Z d7g_Y (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)).1
  exact d7t_fork_nontrivial.2.2.2 bad


-- This second trace starts with genesis and signs the boot certificate before storing X.
private abbrev d7v_source (nd : RecordOnce) : FGBlock (Fin 1) :=
  if nd.sent.isEmpty then .genesis else if nd.sent.length = 1 then d7g_X else d7g_Y
private abbrev d7v_W : FGBlock (Fin 1) := .node d7g_Y 3 ⟨3⟩ 0 [d7g_row]
private def d7v_duties (t : Time) : List Nat :=
  if 6 ≤ t ∧ (t - 6) % 8 = 0 then [((t - 6) / 8).toNat] else []
private theorem d7v_duty_spec (d : Nat) (t : Time) :
    d ∈ d7v_duties t ↔ d7t_T.action d = t := by
  unfold d7v_duties
  by_cases ht : 6 ≤ t ∧ (t - 6) % 8 = 0
  · rw [ite_eq_left ht]
    simp only [List.mem_singleton]
    change _ ↔ 4 * ((d : Int) * 2) + 6 = t
    simp only [Time] at *
    omega
  · rw [ite_eq_right ht]
    simp only [List.not_mem_nil, false_iff]
    intro he
    apply ht
    change 4 * ((d : Int) * 2) + 6 = t at he
    simp only [Time] at *
    constructor
    · omega
    · have hsub : t - 6 = (d : Int) * 8 := by omega
      rw [hsub]
      omega

private abbrev d7v_P : V2.ProtocolSpecD Unit where
  State := RecordOnce
  Label := Unit
  Duty := Nat
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := RecordOnce
  init := RecordOnce.initial
  clock := fun nd _ => nd
  actTime := d7t_T.action
  duties := d7v_duties
  duties_spec := d7v_duty_spec
  duties_nodup := by intro t; unfold d7v_duties; split <;> simp
  act := fun nd _ _ => (createRowOnce d7g_E d7g_cfg nd 0 (some (d7v_source nd)) d7g_hd).1
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

private abbrev d7v_S : FGSafetyReads d7v_P 1 d7v_P.Object where
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
  inputs := fun nd => (some (d7v_source nd), d7g_hd)
  enabled := fun t => decide (6 ≤ t ∧ (t - 6) % 8 = 0)
  finalizedOut := fun _ => .genesis

private abbrev d7v_entry (a : d7v_P.Object) := namedEntry a.payload.height_pair
private abbrev d7v_boot : d7v_P.Object := ⟨.seat () 0, d7g_boot⟩
private abbrev d7v_wire : d7v_P.Object := ⟨.seat () 0, d7g_row⟩
private abbrev d7v_env : Generic.Env (Fin 1) :=
  { d7t_env with Δ := 2, Δ_pos := by decide, awake := fun _ _ => true }
private abbrev d7v_run : V2.D.Run (Fin 1) d7v_P where
  honest := {0}
  horizon := 24
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8, .tick 0 10, .tick 0 12,
    .tick 0 14, .deliver 0 d7v_wire 15, .tick 0 16, .tick 0 18, .tick 0 20, .restart 0 22,
      .tick 0 22, .tick 0 24]
  seatOf := fun _ i => i
  input := fun _ _ => ()

private theorem d7v_client : FGSafetyClientLaws d7v_S d7g_E d7g_cfg where
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
    by_cases ht : 6 ≤ t ∧ 8 ∣ t - 6
    all_goals
      cases ha : E.awake x t <;>
        cases hr : (createRowOnce d7g_E d7g_cfg nd 0 (some (d7v_source nd)) d7g_hd).1 <;>
        simp [V2.D.tick, V2.D.Run.ownSeats, List.finRange_succ, d7v_duties,
          ht, ha, hs, hr, hseat]
    all_goals exact congrArg List.singleton (hsigner _)

private theorem d7v_wires : FGRowPermissionWireLaws d7v_S d7v_entry where
  decoded_wire := by
    intro o u hu
    refine ⟨o, rfl, hu, ?_⟩
    cases o with
    | mk auth payload =>
      cases auth with
      | none => cases hu
      | seat label i => cases hu; rfl

private abbrev d7v_D : FGHistoryWireReads d7v_S where
  heightPair a := a.payload.height_pair
  finalityPair a := a.payload.finality_pair
  signer a := match a.auth with | .seat _ i => some i | .none => none
  decode_height a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl
  decode_finality a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl
  decode_signer a u h := by
    cases a with
    | mk auth p =>
      cases auth with
      | none => cases h
      | seat l i => cases h; rfl


private theorem d7v_schedule : V2.D.ScheduleWellFormed d7v_env d7v_run where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by
    intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl <;> decide
  honest_only := by
    intro ev hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl <;> decide
  tick_public := by
    intro x t hm
    simp only [List.mem_cons, List.mem_nil_iff, V2.Event.tick.injEq,
      reduceCtorEq, or_false, false_or] at hm
    rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩
  tick_total := by
    intro x _ t hpub _ hhor _
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    obtain ⟨d, hd⟩ := hpub
    have hd' : t = (d : Int) * 2 := hd
    have hhor' : t ≤ 24 := hhor
    have hbound : d ≤ 12 := by simp only [Time] at *; omega
    interval_cases d <;> subst t <;> simp

private theorem d7v_boot_origin :
    HonestRowAt d7v_S d7v_env d7v_run d7t_T 3 0 0 d7v_boot := by
  refine ⟨by decide, rfl, ?_⟩
  decide +kernel
private theorem d7v_high_origin :
    HonestRowAt d7v_S d7v_env d7v_run d7t_T 7 0 1 d7v_wire := by
  refine ⟨by decide, rfl, ?_⟩
  decide +kernel
private theorem d7v_suppressed : V2.D.Run.emitsAt d7v_env d7v_run 13 = [] := by
  decide +kernel
private theorem d7v_outputs (j : Nat) : V2.D.Run.emitsAt d7v_env d7v_run j =
    if j = 3 then [d7v_boot] else if j = 7 then [d7v_wire] else [] := by
  by_cases hj : j < 15
  · interval_cases j <;> decide +kernel
  · have hn : d7v_run.events[j]? = none := List.getElem?_eq_none (by change 15 ≤ j; omega)
    have h3 : j ≠ 3 := by omega
    have h7 : j ≠ 7 := by omega
    simp [V2.D.Run.emitsAt, hn, h3, h7]
private theorem d7v_only_row {j r : Nat} {x : Fin 1} {a : d7v_P.Object}
    (ha : HonestRowAt d7v_S d7v_env d7v_run d7t_T j x r a) :
    (j = 3 ∧ x = 0 ∧ r = 0 ∧ a = d7v_boot) ∨
      (j = 7 ∧ x = 0 ∧ r = 1 ∧ a = d7v_wire) := by
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  obtain ⟨_, ht, ha⟩ := ha
  rw [d7v_outputs] at ha
  split at ha
  · rename_i hj
    subst j
    have ht' : 6 = 4 * ((r : Int) * 2) + 6 := by
      exact Option.some.inj (congrArg (fun ev => ev.map V2.Event.time) ht)
    exact Or.inl ⟨rfl, rfl, by omega, List.mem_singleton.mp ha⟩
  · split at ha
    · rename_i hj
      subst j
      have ht' : 14 = 4 * ((r : Int) * 2) + 6 := by
        exact Option.some.inj (congrArg (fun ev => ev.map V2.Event.time) ht)
      exact Or.inr ⟨rfl, rfl, by omega, List.mem_singleton.mp ha⟩
    · cases ha
private theorem d7v_emission :
    HighRecordEmission d7v_S d7t_T d7v_env d7v_run d7g_E d7g_cfg := by
  intro j x r a u ha hd
  rcases d7v_only_row ha with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals cases hd; decide +kernel
private theorem d7v_own : HighRecordOwnOrigin d7v_S d7t_T d7v_env d7v_run := by
  rw [HighRecordOwnOrigin_def]
  intro j x o u _ ho hd
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  rw [V2.D.Engine.ownReleasedAt_def] at ho
  split at ho
  · have hem := (List.mem_filter.mp ho).1
    rw [d7v_outputs] at hem
    split at hem
    · rename_i hj
      subst j
      have hw : o = d7v_boot := List.mem_singleton.mp hem
      subst o
      exact ⟨0, d7v_boot, d7v_boot_origin, hd⟩
    · split at hem
      · rename_i hj
        subst j
        have hw : o = d7v_wire := List.mem_singleton.mp hem
        subst o
        exact ⟨1, d7v_wire, d7v_high_origin, hd⟩
      · cases hem
  · cases ho

private abbrev d7v_R : FGCoreReads d7v_P 1 Unit Unit d7v_P.Object where
  core nd := ⟨(), ⟨if nd.sent.isEmpty then {.genesis} else
    if nd.sent.length = 1 then {.genesis, d7g_X} else
      {.genesis, d7g_X, d7g_Y, d7v_W}, .genesis,
    if nd.sent.length ≤ 1 then .genesis else d7g_X,
    if nd.sent.isEmpty then 0 else if nd.sent.length = 1 then 1 else 2,
    if nd.sent.isEmpty then 1 else if nd.sent.length = 1 then 2 else 3⟩, [],
    if nd.sent.isEmpty then [] else if nd.sent.length = 1 then [d7v_boot] else
      [d7v_boot, d7v_wire]⟩
  erase := d7t_erase
  source nd := some (d7v_source nd)
  headVote _ _ := d7t_erase d7g_Y
  finalityHead _ := some d7g_Y
  proposalFG _ _ := none
private abbrev d7v_O : FGObservationReads d7v_R where
  height := KitFG.Window.certificateHeight d7g_E d7g_cfg 2
  finality := KitFG.Window.certificateFinality d7g_E d7g_cfg 2
  controls nd := treeStoreControlsView (simplexHeightView d7g_E d7g_cfg) (d7v_R.core nd).fg
  viable _ trees := trees
private abbrev d7v_point : FGServicePoint :=
  ⟨⟨0, 0, 1, 1, 0, d7t_erase d7g_X⟩, 2, d7t_erase d7g_X, 20⟩
private theorem d7v_cert : FGCertificateLaws d7g_E d7v_O.height d7v_O.finality :=
  KitFG.Window.windowCertificateLaws d7g_E d7g_cfg 2
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide)
private theorem d7v_names :
    HighRecordNames d7v_R d7v_S d7v_O d7t_T d7v_env d7v_run d7v_D := by
  intro j x r a e ha hn
  rcases d7v_only_row ha with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨.genesis, ?_, ?_⟩
    · decide +kernel
    · exact (Option.some.inj hn).symm
  · refine ⟨d7g_X, ?_, ?_⟩
    · decide +kernel
    · exact (Option.some.inj hn).symm
private theorem d7v_source_cases {x : Fin 1} {r : Nat} {C : FGBlock (Fin 1)}
    (h : actionSourceFG d7v_R d7v_env d7v_run d7t_T x r = some (some C)) :
    C = .genesis ∨ C = d7g_X ∨ C = d7g_Y := by
  obtain ⟨nd, _, hs⟩ := Option.map_eq_some_iff.mp h
  have he : d7v_source nd = C := Option.some.inj hs
  unfold d7v_source at he
  split at he
  · exact Or.inl he.symm
  · split at he
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr he.symm)
private theorem d7v_history (horizon : Time) :
    FGHistoricalHighChain d7v_R d7v_O d7t_T d7v_env d7v_run d7v_point horizon := by
  intro x z r q C B _ _ hC hB hc hb _ _
  rcases d7v_source_cases hC with rfl | rfl | rfl <;>
    rcases d7v_source_cases hB with rfl | rfl | rfl
  all_goals first
    | exact False.elim (by change 2 ≤ 1 at hc; omega)
    | exact False.elim (by change 2 ≤ 1 at hb; omega)
    | exact ⟨by unfold Block.Compatible; decide +kernel,
        by unfold Block.Compatible; decide +kernel⟩
private theorem d7v_head : HighRecordHead d7v_R d7v_S d7v_O d7v_env d7v_run := by
  intro i x t hx
  exact Or.inl rfl

private abbrev d7v_afterBoot := record_row_once RecordOnce.initial d7g_boot
private abbrev d7v_afterHigh := record_row_once d7v_afterBoot d7g_row
private theorem d7v_state (i : Nat) (x : Fin 1) :
    V2.D.Run.stateBefore d7v_env d7v_run i x =
      if i ≤ 3 then RecordOnce.initial else if i ≤ 7 then d7v_afterBoot else d7v_afterHigh := by
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  by_cases hi : i < 15
  · interval_cases i <;> rfl
  · rw [V2.D.Run.stateBefore, List.take_of_length_le (by change 15 ≤ i; omega)]
    have h0 : ¬ i ≤ 3 := by omega
    have h1 : ¬ i ≤ 7 := by omega
    simp only [h0, h1, ite_false]
    rfl
private theorem d7v_carried (i : Nat) (x : Fin 1) (W : FGBlock (Fin 1))
    (hW : W ∈ (d7v_R.core (V2.D.Run.stateBefore d7v_env d7v_run i x)).fg.TF)
    (a : Row (Fin 1)) (ha : a ∈ chainRows W) :
    (a = d7g_boot ∧ 3 < i) ∨ (a = d7g_row ∧ 7 < i) := by
  rw [d7v_state] at hW
  split at hW
  · have hgen : W = .genesis := by
      simpa [RecordOnce.initial, d7v_afterBoot, d7v_afterHigh, record_row_once] using hW
    subst W
    cases ha
  · rename_i h0
    split at hW
    · rename_i h1
      have hcases : W = .genesis ∨ W = d7g_X := by
        simpa [RecordOnce.initial, d7v_afterBoot, d7v_afterHigh, record_row_once] using hW
      rcases hcases with rfl | rfl
      · cases ha
      · have he : a = d7g_boot := by simpa [chainRows] using ha
        exact Or.inl ⟨he, by omega⟩
    · rename_i h1
      have hcases : W = .genesis ∨ W = d7g_X ∨ W = d7g_Y ∨ W = d7v_W := by
        simpa [RecordOnce.initial, d7v_afterBoot, d7v_afterHigh, record_row_once] using hW
      rcases hcases with rfl | rfl | rfl | rfl
      · cases ha
      · have he : a = d7g_boot := by simpa [chainRows] using ha
        exact Or.inl ⟨he, by omega⟩
      · have he : a = d7g_boot := by simpa [chainRows] using ha
        exact Or.inl ⟨he, by omega⟩
      · have he : a = d7g_boot ∨ a = d7g_row := by simpa [chainRows, or_comm] using ha
        rcases he with he | he
        · exact Or.inl ⟨he, by omega⟩
        · exact Or.inr ⟨he, by omega⟩
private theorem d7v_stored_origin (i : Nat) (x : Fin 1) (W : FGBlock (Fin 1))
    (hW : HeldAt d7v_R d7v_env d7v_run i x W) (a : Row (Fin 1))
    (ha : a ∈ chainRows W) :
    ∃ (wire : d7v_P.Object) (r : Nat), d7v_S.decode wire = some a ∧
      d7v_D.signer wire = some a.signer ∧
      ∀ z, RowSigner d7v_S d7v_run d7v_D.signer wire z → z ∈ d7v_run.honest →
        HonestRowBefore d7v_S d7v_env d7v_run d7t_T i z r wire := by
  rcases d7v_carried i x W hW.2 a ha with ⟨rfl, hi⟩ | ⟨rfl, hi⟩
  · refine ⟨d7v_boot, 0, rfl, rfl, ?_⟩
    intro z _ _
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    exact ⟨3, hi, d7v_boot_origin⟩
  · refine ⟨d7v_wire, 1, rfl, rfl, ?_⟩
    intro z _ _
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    exact ⟨7, hi, d7v_high_origin⟩
private theorem d7v_row_origin (i : Nat) (x : Fin 1) (W carrier : FGBlock (Fin 1))
    (hW : W ∈ (d7v_R.core (V2.D.Run.stateBefore d7v_env d7v_run i x)).fg.TF)
    (a : Row (Fin 1)) (hpath : FGBlock.Preceq carrier W) (ha : a ∈ carrier.rows) :
    ∃ y r, ∃ wire : d7v_P.Object,
      HonestRowBefore d7v_S d7v_env d7v_run d7t_T i y r wire ∧
      d7v_S.decode wire = some a ∧ a ∈ carrier.rows ∧
      ∃ C, actionSourceFG d7v_R d7v_env d7v_run d7t_T y r = some (some C) ∧
        namedEntry a.height_pair = some ((d7v_O.height C).h, (d7v_O.height C).T_h.root) ∧
        FGBlock.Preceq (d7v_O.height C).T_h C ∧ True := by
  have hchain : a ∈ chainRows W := by
    exact mem_chainRows_of_carrier hpath ha
  rcases d7v_carried i x W hW a hchain with ⟨rfl, hi⟩ | ⟨rfl, hi⟩
  · exact ⟨0, 0, d7v_boot, ⟨3, hi, d7v_boot_origin⟩, rfl, ha, .genesis,
      by decide +kernel, rfl, by decide +kernel, trivial⟩
  · exact ⟨0, 1, d7v_wire, ⟨7, hi, d7v_high_origin⟩, rfl, ha, d7g_X,
      by decide +kernel, rfl, by decide +kernel, trivial⟩
private theorem d7v_quorum_zero (Q : Finset (Fin 1)) (hQ : d7g_E.IsQuorum Q) : 0 ∈ Q := by
  by_contra h
  have he : Q = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have hk0 : k = 0 := Subsingleton.elim _ _
    exact h (hk0 ▸ hk)
  subst Q
  have hf : ¬ d7g_E.IsQuorum ∅ := by unfold Electorate.IsQuorum; decide +kernel
  exact hf hQ
private theorem d7v_qc : RQCOrigin d7v_R d7v_S d7v_env d7v_run d7v_O d7t_T
    (fun _ C wire => wire.payload ∈ C.rows) (fun _ _ _ => True) d7g_E := by
  intro i x W _ hW
  refine ⟨?_, ?_, ?_⟩
  · intro m X Q rows _ _ _ _ hQ hrows
    have hk := d7v_quorum_zero Q hQ
    have hr := hrows 0 hk
    obtain ⟨y, r, wire, hb, hd, hc, C, hs, hn, hp, ht⟩ :=
      d7v_row_origin i x W (rows 0).1 hW (rows 0).2 hr.1 hr.2.1
    refine ⟨0, hk, y, r, wire, hb, hd, ?_, C, hs, hn, hp, ht⟩
    have hpayload : wire.payload = (rows 0).2 := by
      cases wire with
      | mk auth payload =>
        cases auth with
        | none => cases hd
        | seat l k =>
          have he := Option.some.inj hd
          rw [← he]
          have hk : k = payload.signer := Subsingleton.elim _ _
          cases hk
          rfl
    simpa only [hpayload] using hc
  · intro Q rows _ hQ hrows
    have hk := d7v_quorum_zero Q hQ
    have hr := hrows 0 hk
    obtain ⟨y, r, wire, hb, hd, hc, C, hs, hn, hp, ht⟩ :=
      d7v_row_origin i x W (rows 0).1 hW (rows 0).2 hr.1 hr.2.1
    refine ⟨0, hk, y, r, wire, hb, hd, ?_, C, hs, hn, hp, ht⟩
    have hpayload : wire.payload = (rows 0).2 := by
      cases wire with
      | mk auth payload =>
        cases auth with
        | none => cases hd
        | seat l k =>
          have he := Option.some.inj hd
          rw [← he]
          have hk : k = payload.signer := Subsingleton.elim _ _
          cases hk
          rfl
    simpa only [hpayload] using hc
  · intro hf
    have hzero : (d7v_O.finality W).F = .genesis := by
      rw [d7v_state] at hW
      split at hW
      · have hw : W = .genesis := by
          simpa [RecordOnce.initial, d7v_afterBoot, d7v_afterHigh, record_row_once] using hW
        subst W; rfl
      · split at hW
        · have hw : W = .genesis ∨ W = d7g_X := by
            simpa [RecordOnce.initial, d7v_afterBoot, d7v_afterHigh, record_row_once] using hW
          rcases hw with rfl | rfl <;> decide +kernel
        · have hw : W = .genesis ∨ W = d7g_X ∨ W = d7g_Y ∨ W = d7v_W := by
              simpa [RecordOnce.initial, d7v_afterBoot, d7v_afterHigh, record_row_once] using hW
          rcases hw with rfl | rfl | rfl | rfl <;> decide +kernel
    exact (hf hzero).elim

private theorem d7v_store_empty :
    FGStoreInvariant d7v_O.height d7v_O.finality (d7v_R.core RecordOnce.initial).fg := by
  constructor
  · intro B hB
    change B ∈ ({.genesis} : Finset (FGBlock (Fin 1))) at hB
    simp only [Finset.mem_singleton] at hB
    rcases hB with rfl
    decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · constructor
    · exact ⟨.genesis, by decide +kernel, by decide +kernel, rfl, rfl⟩
    · intro B hB _
      change B ∈ ({.genesis} : Finset (FGBlock (Fin 1))) at hB
      simp only [Finset.mem_singleton] at hB
      rcases hB with rfl
      decide +kernel
  · decide +kernel
  · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem d7v_store_boot :
    FGStoreInvariant d7v_O.height d7v_O.finality (d7v_R.core d7v_afterBoot).fg := by
  constructor
  · intro B hB
    change B ∈ ({.genesis, d7g_X} : Finset (FGBlock (Fin 1))) at hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · constructor
    · exact ⟨d7g_X, by decide +kernel, by decide +kernel, rfl, rfl⟩
    · intro B hB _
      change B ∈ ({.genesis, d7g_X} : Finset (FGBlock (Fin 1))) at hB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | rfl <;> decide +kernel
  · decide +kernel
  · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem d7v_store_high :
    FGStoreInvariant d7v_O.height d7v_O.finality (d7v_R.core d7v_afterHigh).fg := by
  constructor
  · intro B hB
    change B ∈ ({.genesis, d7g_X, d7g_Y, d7v_W} : Finset (FGBlock (Fin 1))) at hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl | rfl | rfl <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · constructor
    · exact ⟨d7v_W, by decide +kernel, by decide +kernel, rfl, rfl⟩
    · intro B hB _
      change B ∈ ({.genesis, d7g_X, d7g_Y, d7v_W} : Finset (FGBlock (Fin 1))) at hB
      simp only [Finset.mem_insert, Finset.mem_singleton] at hB
      rcases hB with rfl | rfl | rfl | rfl <;> decide +kernel
  · decide +kernel
  · exact ⟨.genesis, by decide +kernel, rfl⟩

private theorem d7v_store (i : Nat) (x : Fin 1) (_ : x ∈ d7v_run.honest) :
    FGStoreInvariant d7v_O.height d7v_O.finality
      (d7v_R.core (V2.D.Run.stateBefore d7v_env d7v_run i x)).fg := by
  rw [d7v_state]
  split
  · exact d7v_store_empty
  · split
    · exact d7v_store_boot
    · exact d7v_store_high

private theorem d7v_height (C : FGBlock (Fin 1)) :
    ((derive d7g_E d7g_cfg C).h, (derive d7g_E d7g_cfg C).T_h.root) =
      ((d7v_O.height C).h, (d7v_O.height C).T_h.root) := by
  exact congrArg (fun h : FGHeight (Fin 1) => (h.h, h.T_h.root))
    (KitFG.Window.windowHeightBridge d7g_E d7g_cfg 2 (by decide) C).symm
private theorem d7v_highX : high d7v_R d7v_O d7v_point.reset d7g_X := by
  unfold high; decide +kernel
private theorem d7v_highY : high d7v_R d7v_O d7v_point.reset d7g_Y := by
  unfold high; decide +kernel

private theorem d7v_record_restart : ∃ entry : Nat → BlockId, entry 2 = ⟨1⟩ ∧
    HighRecordInvariant 1 entry
      (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 12 0)) ∧
    HighRecordInvariant 1 entry
      (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 13 0)) ∧
    d7v_run.events[12]? = some (.restart 0 22) ∧
    (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 13 0)).target 2 = some ⟨1⟩ ∧
    d7g_row.onceKey ∈ (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 13 0)).sent := by
  obtain ⟨entry, sources, records⟩ := high_entry_record_invariant d7v_history d7v_cert
    d7t_reflect d7v_qc d7v_head d7v_client d7v_emission d7v_own d7v_names
  refine ⟨entry, sources 0 1 d7g_X (by decide) (by decide +kernel) d7v_highX,
    records 12 0 (by decide), records 13 0 (by decide), rfl, rfl, ?_⟩
  decide +kernel
private theorem d7v_complete : ∀ j x r a,
    HonestRowAt d7v_S d7v_env d7v_run d7t_T j x r a →
    ∃ u, d7v_S.decode a = some u ∧
      RowComplete d7v_S d7v_run d7v_D.signer (fun _ => true) x a := by
  intro j x r a ha
  rcases d7v_only_row ha with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨d7g_boot, rfl, rfl, 0, rfl, rfl⟩
  · exact ⟨d7g_row, rfl, rfl, 0, rfl, rfl⟩
private theorem d7v_enabled (r : Nat) : d7v_S.enabled (d7t_T.action r) = true := by
  apply decide_eq_true
  change 6 ≤ 4 * ((r : Int) * 2) + 6 ∧ (4 * ((r : Int) * 2) + 6 - 6) % 8 = 0
  omega
private theorem d7v_current_consumer :
    ∃ j a, HonestRowAt d7v_S d7v_env d7v_run d7t_T j 0 1 a ∧
      RowComplete d7v_S d7v_run d7v_D.signer (fun _ => true) 0 a ∧
      d7v_D.heightPair a = .vote 2 ⟨1⟩ false := by
  apply high_target_first_row d7v_history d7v_cert d7t_reflect d7v_qc d7v_head
    (fun _ => rfl) d7v_height d7v_client d7v_emission d7v_own d7v_names
    d7v_complete d7v_wires (Equiv.refl _) (fun _ => rfl) d7t_timing d7v_schedule
    d7v_enabled 0 (by decide) 1 d7g_X (by decide +kernel) d7v_highX rfl
  intro j q a h hq ha hh
  rcases d7v_only_row ha with ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, _, rfl, rfl⟩
  · have he : 1 = h := Option.some.inj hh
    subst h
    decide +kernel
  · omega
private theorem d7v_prior_consumer :
    ∃ j r a, r ≤ 2 ∧ HonestRowAt d7v_S d7v_env d7v_run d7t_T j 0 r a ∧
      RowComplete d7v_S d7v_run d7v_D.signer (fun _ => true) 0 a ∧
      d7v_D.heightPair a = .vote 2 ⟨1⟩ false ∧ j = 7 ∧ r = 1 ∧ a = d7v_wire := by
  obtain ⟨j, r, a, hr, ha, hc, hp⟩ := high_target_row_covered
    d7v_history d7v_cert d7t_reflect d7v_qc d7v_head (fun _ => rfl) d7v_height
    d7v_client d7v_emission d7v_own d7v_names d7v_complete d7v_wires
    (Equiv.refl _) (fun _ => rfl) d7t_timing d7v_schedule d7v_enabled
    0 (by decide) 2 d7g_Y (by decide +kernel) d7v_highY rfl
  refine ⟨j, r, a, hr, ha, hc, hp, ?_⟩
  rcases d7v_only_row ha with ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, _, rfl, rfl⟩
  · cases hp
  · exact ⟨rfl, rfl, rfl⟩
private theorem d7v_unit : FGSafetyUnitLaws d7g_E where
  n_pos := by decide
  total := by decide +kernel
  weight := by intro A; simp [Electorate.weightOf]
  quorum := by decide +kernel
private theorem d7v_fault_bound :
    (Gen.V2.Duty.faulty d7v_run).card ≤ (1 - 1) / 3 := by
  decide +kernel
private theorem d7v_honest_quorum :
    d7g_E.IsQuorum (Finset.univ.filter (fun k => safetyHolder d7v_S d7v_run k ∈
      d7v_run.honest)) :=
  high_target_honest_quorum (Equiv.refl _) (fun _ => rfl) d7v_unit d7v_fault_bound
private theorem d7v_receipts :
    TRowsReceipt d7v_R d7v_S d7v_env d7v_run d7t_T (fun _ => []) 2 := by
  intro j y r a ha _ x _
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  rcases d7v_only_row ha with ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, _, rfl, rfl⟩
  all_goals unfold HeldBefore Gen.V2.Duty.HoldsBefore rowHeld; decide +kernel
private theorem d7v_quorum_original_receipt :
    ∃ rows : Fin 1 → d7v_P.Object, ∀ i ∈ (Finset.univ : Finset (Fin 1)),
      rows i = d7v_wire ∧
      HonestRowAt d7v_S d7v_env d7v_run d7t_T 7 0 1 (rows i) ∧
      HeldBefore d7v_R d7v_env d7v_run (fun _ => []) 0 (rows i) 16 ∧
      d7v_run.events[8]? = some (.deliver 0 (rows i) 15) ∧ (15 : Time) < 16 := by
  obtain ⟨_, rows, hrows⟩ := high_target_quorum_covered
    d7v_history d7v_cert d7t_reflect d7v_qc d7v_head (fun _ => rfl) d7v_height
    d7v_client d7v_emission d7v_own d7v_names d7v_complete d7v_wires
    (Equiv.refl _) (fun _ => rfl) d7t_timing d7v_schedule d7v_enabled d7v_unit
    d7v_fault_bound (fun _ => []) 2 (by decide) d7v_receipts (fun _ _ _ _ _ => rfl)
    2 d7g_Y d7v_highY (by
      intro x _
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      decide +kernel) (by decide) (by decide)
  refine ⟨rows, ?_⟩
  intro i _
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  obtain ⟨j, r, _, ha, _, _, hp, hr⟩ := hrows 0 (by decide)
  rcases d7v_only_row ha with ⟨hj, _, hround, hw⟩ | ⟨hj, _, hround, hw⟩
  · rw [hw] at hp; cases hp
  · subst j; subst r
    exact ⟨hw, ha, hr 0 (by decide), by rw [hw]; rfl, by decide⟩
private theorem d7v_actual_receipt :
    d7v_run.events[8]? = some (.deliver 0 d7v_wire 15) ∧
      HonestRowAt d7v_S d7v_env d7v_run d7t_T 7 0 1 d7v_wire ∧
      (15 : Time) < 16 := ⟨rfl, d7v_high_origin, by decide⟩
private theorem d7v_stored_qc_consumer : ∃ entry : Nat → BlockId,
    entry 2 = ⟨1⟩ ∧ ∃ k ∈ ({0} : Finset (Fin 1)), ∃ a ∈ chainRows d7v_W,
      a.signer = k ∧ a.height_pair = .vote 2 (entry 2) false := by
  have hweight : d7g_E.weightOf (historyFaulty d7v_S d7v_run) < d7g_E.q := by
    unfold historyFaulty
    decide +kernel
  obtain ⟨entry, _, stored⟩ := ff2_stored_high_qc_identity d7v_history d7v_cert
    d7t_reflect d7v_qc d7v_head d7v_client d7v_emission d7v_own d7v_names
    hweight d7v_stored_origin
  obtain ⟨he, _, _, _, _, _, _, _, _, hrows⟩ :=
    (stored 9 0 d7v_W ⟨by decide, by decide +kernel⟩).1 2 ⟨1⟩ {0}
      (by decide) (by unfold Electorate.IsQuorum; decide +kernel) (by
        intro k hk
        have hk0 : k = 0 := Subsingleton.elim _ _
        subst k
        exact ⟨d7g_row, by decide +kernel, rfl, rfl⟩)
  exact ⟨entry, he.symm, hrows⟩
private theorem d7v_selected_qc_consumer : ∃ entry : Nat → BlockId,
    entry 2 = ⟨1⟩ ∧ ∃ k ∈ ({0} : Finset (Fin 1)),
      d7g_row.height_pair = .vote 2 (entry 2) false := by
  obtain ⟨entry, _, selected⟩ := ff2_high_qc_identity d7v_history d7v_cert
    d7t_reflect d7v_qc d7v_head d7v_client d7v_emission d7v_own d7v_names d7v_store
  obtain ⟨he, _, _, _, _, _, _, _, _, hrows⟩ :=
    (selected 9 0 d7v_W (by decide) (by decide +kernel)).1 2 d7g_X {0}
      (fun _ => (d7v_W, d7g_row)) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by unfold Electorate.IsQuorum; decide +kernel) (by
        intro k _
        have hk0 : k = 0 := Subsingleton.elim _ _
        subst k
        exact ⟨by decide +kernel, by decide +kernel, rfl, rfl⟩)
  exact ⟨entry, he.symm, hrows⟩

private theorem d7v_shield (cutoff : Time) :
    HighRecordShieldRows d7v_R d7v_S d7v_O d7t_T d7v_env d7v_run d7v_D
      d7g_X 2 cutoff := by
  intro j x r a y U timeout ha _ hp
  rcases d7v_only_row ha with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · cases hp
    exact ⟨by decide, by intro h; cases h⟩
  · cases hp
    exact ⟨by decide, fun _ => rfl⟩
private theorem d7v_seed (cutoff start : Time) (hcut : cutoff ≤ start) :
    HighRecordSeedLeaves d7v_R d7v_S d7v_O d7t_T d7v_env d7v_run d7v_D
      { d7v_point with serviceStart := start } d7g_X 2 cutoff :=
  ⟨rfl, rfl, by change 2 ≤ 2; decide, hcut, d7v_shield cutoff⟩
private theorem d7v_shield_nonempty (cutoff start : Time) (hcut : cutoff ≤ start) :
    ∃ entry : Nat → BlockId, entry 2 = ⟨1⟩ ∧
      HighRecordInvariant 1 entry
        (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 8 0)) ∧
      HighRecordInvariant 1 entry
        (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 13 0)) := by
  obtain ⟨entry, sources, records, _⟩ := shield_high_entry_record_invariant
    (pt := { d7v_point with serviceStart := start }) d7v_history d7v_cert
    d7t_reflect d7v_qc d7v_head d7v_client d7v_emission d7v_own d7v_names
    d7g_X 2 cutoff (d7v_seed cutoff start hcut)
  exact ⟨entry, sources 0 1 d7g_X (by decide) (by decide +kernel) d7v_highX,
    records 8 0 (by decide), records 13 0 (by decide)⟩
private theorem d7v_old_seed_record :
    HighRecordInvariant 1 (fun _ => (d7v_O.height d7g_X).T_h.root)
      (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 8 0)) := by
  apply shield_record_before_cut d7v_client d7v_emission d7v_own d7g_X 2 15
    (by decide) (d7v_shield 15) 8 0 (by decide)
  intro j r a _ ha
  rcases d7v_only_row ha with ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, _, rfl, rfl⟩ <;> decide
-- Each cut pair is checked with the same actual signed history and nonempty record.
private theorem d7v_shield_intervals (cutoff start : Time)
    (hm : (cutoff, start) ∈ ([(15, 20), (14, 20), (10, 20), (10, 12)] : List (Time × Time))) :
    HighRecordSeedLeaves d7v_R d7v_S d7v_O d7t_T d7v_env d7v_run d7v_D
      { d7v_point with serviceStart := start } d7g_X 2 cutoff ∧
    ∃ entry : Nat → BlockId, entry 2 = ⟨1⟩ ∧
      HighRecordInvariant 1 entry
        (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 8 0)) ∧
      HighRecordInvariant 1 entry
        (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 13 0)) := by
  have hcut : cutoff ≤ start := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  exact ⟨d7v_seed cutoff start hcut, d7v_shield_nonempty cutoff start hcut⟩
private theorem d7v_interval_times :
    HonestRowAt d7v_S d7v_env d7v_run d7t_T 7 0 1 d7v_wire ∧
    d7t_T.action 1 < 15 ∧ 14 = d7t_T.action 1 ∧
    (10 ≤ d7t_T.action 1 ∧ d7t_T.action 1 < 20) ∧ 12 ≤ d7t_T.action 1 :=
  ⟨d7v_high_origin, by decide, rfl, by decide, by decide⟩
private theorem d7v_shield_boundary_strict :
    HighRecordShieldRows d7v_R d7v_S d7v_O d7t_T d7v_env d7v_run d7v_D d7g_Z 2 14 ∧
    ¬ HighRecordShieldRows d7v_R d7v_S d7v_O d7t_T d7v_env d7v_run d7v_D d7g_Z 2 15 := by
  constructor
  · intro j x r a y U timeout ha ht hp
    rcases d7v_only_row ha with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · cases hp; exact ⟨by decide, by intro h; cases h⟩
    · exact (lt_irrefl _ ht).elim
  · intro shield
    have wrong := (shield 7 0 1 d7v_wire 2 ⟨1⟩ false d7v_high_origin (by decide) rfl).2 rfl
    cases wrong
private theorem d7v_no_timeout_at_any_cut :
    ∀ i, (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run i 0)).timeout 2 = false := by
  obtain ⟨_, _, records, _⟩ := shield_high_entry_record_invariant d7v_history d7v_cert
    d7t_reflect d7v_qc d7v_head d7v_client d7v_emission d7v_own d7v_names
    d7g_X 2 10 (d7v_seed 10 20 (by decide))
  intro i
  exact (records i 0 (by decide) 2 (by decide)).2.1
private theorem d7v_timeout_row_rejected :
    ¬ ∃ j r, HonestRowAt d7v_S d7v_env d7v_run d7t_T j 0 r
      (⟨.seat () 0, ⟨0, .vote 2 ⟨1⟩ true, none⟩⟩ : d7v_P.Object) := by
  rintro ⟨j, r, ha⟩
  rcases d7v_only_row ha with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h

private theorem d7v_current_exact :
    ∃ j a, j = 7 ∧ a = d7v_wire ∧
      HonestRowAt d7v_S d7v_env d7v_run d7t_T j 0 1 a ∧
      d7v_run.events[8]? = some (.deliver 0 a 15) ∧
      HeldBefore d7v_R d7v_env d7v_run (fun _ => []) 0 a 16 := by
  obtain ⟨j, a, ha, _, hp⟩ := d7v_current_consumer
  rcases d7v_only_row ha with ⟨_, _, hround, _⟩ | ⟨hj, _, _, hw⟩
  · cases hround
  · subst j; subst a
    exact ⟨7, d7v_wire, rfl, rfl, ha, rfl, d7v_receipts 7 0 1 d7v_wire ha
      (by decide) 0 (by decide)⟩
private theorem d7v_old_higher_fresh :
    HighRecordFresh 3 (d7v_S.record (V2.D.Run.stateBefore d7v_env d7v_run 8 0)) := by
  obtain ⟨_, _, _, old⟩ := shield_high_entry_record_invariant d7v_history d7v_cert
    d7t_reflect d7v_qc d7v_head d7v_client d7v_emission d7v_own d7v_names
    d7g_X 2 15 (d7v_seed 15 20 (by decide))
  apply (old 8 0 (by decide) ?_).2 3 (by decide)
  intro j r a _ ha
  rcases d7v_only_row ha with ⟨rfl, _, rfl, rfl⟩ | ⟨rfl, _, rfl, rfl⟩ <;> decide
-- The earlier client-only fixture cannot supply the full origin law at prefix zero.
private theorem d7v_reject_premature_certificate
    (stored : d7t_P.State → FGBlock (Fin 1) → d7t_P.Object → Prop)
    (service : Fin 1 → Nat → FGBlock (Fin 1) → Prop) :
    ¬ RQCOrigin d7t_R d7t_S d7t_env d7t_run d7t_O d7t_T stored service d7g_E := by
  intro h
  obtain ⟨k, _, z, r, wire, ⟨j, hj, _⟩, _⟩ :=
    (h 0 0 d7g_X (by decide) (by decide +kernel)).1 1 .genesis {0}
      (fun _ => (d7g_X, d7g_boot)) (by decide) (by decide +kernel)
      (by decide +kernel) rfl (by unfold Electorate.IsQuorum; decide +kernel) (by
        intro k _
        have hk : k = 0 := Subsingleton.elim _ _
        subst k
        exact ⟨by decide +kernel, by decide +kernel, rfl, rfl⟩)
  omega

end

#print axioms d7g_own_origin_expansion
#print axioms d7g_parent_paths
#print axioms d7g_current
#print axioms d7g_guard_choice
#print axioms d7g_prior
#print axioms d7g_timeout_rejected
#print axioms d7g_wrong_target_rejected
#print axioms d7g_finality_lock
#print axioms d7t_client
#print axioms d7t_fresh_origin
#print axioms d7t_restart_record
#print axioms d7t_suppressed
#print axioms d7t_emission
#print axioms d7t_own
#print axioms d7t_fresh_after_restart
#print axioms d7t_prior_exact

#print axioms d7t_history
#print axioms d7t_pre_service_sources
#print axioms d7t_equal_height_entry
#print axioms d7t_fork_nontrivial
#print axioms d7t_reject_historical_fork

#print axioms d7v_duty_spec
#print axioms d7v_client
#print axioms d7v_wires
#print axioms d7v_schedule
#print axioms d7v_boot_origin
#print axioms d7v_high_origin
#print axioms d7v_suppressed
#print axioms d7v_outputs
#print axioms d7v_only_row
#print axioms d7v_emission
#print axioms d7v_own
#print axioms d7v_cert
#print axioms d7v_names
#print axioms d7v_source_cases
#print axioms d7v_history
#print axioms d7v_head
#print axioms d7v_state
#print axioms d7v_carried
#print axioms d7v_stored_origin
#print axioms d7v_row_origin
#print axioms d7v_quorum_zero
#print axioms d7v_qc
#print axioms d7v_store_empty
#print axioms d7v_store_boot
#print axioms d7v_store_high
#print axioms d7v_store
#print axioms d7v_height
#print axioms d7v_highX
#print axioms d7v_highY
#print axioms d7v_record_restart
#print axioms d7v_complete
#print axioms d7v_enabled
#print axioms d7v_current_consumer
#print axioms d7v_prior_consumer
#print axioms d7v_unit
#print axioms d7v_fault_bound
#print axioms d7v_honest_quorum
#print axioms d7v_receipts
#print axioms d7v_quorum_original_receipt
#print axioms d7v_actual_receipt
#print axioms d7v_stored_qc_consumer
#print axioms d7v_selected_qc_consumer
#print axioms d7v_shield
#print axioms d7v_seed
#print axioms d7v_shield_nonempty
#print axioms d7v_old_seed_record
#print axioms d7v_shield_intervals
#print axioms d7v_interval_times
#print axioms d7v_shield_boundary_strict
#print axioms d7v_no_timeout_at_any_cut
#print axioms d7v_timeout_row_rejected

#print axioms d7v_current_exact

#print axioms d7v_old_higher_fresh

#print axioms d7v_reject_premature_certificate

end AvailableChain.FGCompose.Tests.P0d7a2
end
