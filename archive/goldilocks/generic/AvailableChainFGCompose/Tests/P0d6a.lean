module
public import AvailableChainFGCompose.Proofs.Healing.ResetCut

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose.Tests.P0d6a
open AvailableChain.SimplexFG AvailableChain.KitFG

-- A reachable interface trace with an actual signed row. This is not a production fixture.
private def d6g_X : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private def d6g_Y : FGBlock (Fin 1) := .node d6g_X 2 ⟨2⟩ 0 []
private def d6g_row : Row (Fin 1) := ⟨0, .vote 2 ⟨1⟩ false, none⟩

private def d6g_erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (d6g_erase p) s r (encFGBody x rs)

private theorem d6g_erase_inj : Function.Injective d6g_erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [d6g_erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [d6g_erase] at h
    | node q t u y ts =>
      simp only [d6g_erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private abbrev d6g_protocol : V2.ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Unit
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := Bool
  init := false
  clock := fun st _ => st
  actTime := fun _ => 22
  duties := fun t => if t = 22 then [()] else []
  duties_spec := by intro d t; cases d; by_cases h : t = 22 <;> simp [h, eq_comm]
  duties_nodup := by intro t; split <;> simp
  act := fun _ _ _ => some d6g_row
  gossip := fun _ _ => []
  process := fun _ _ => true
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := id
  restore := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private noncomputable def d6g_object (a : Row (Fin 1)) : d6g_protocol.Object := ⟨.seat () 0, a⟩

private noncomputable abbrev d6g_reads :
    FGCoreReads d6g_protocol 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨if st then {.genesis, d6g_X, d6g_Y} else {.genesis, d6g_X},
    .genesis, .genesis, 0, if st then 3 else 2⟩, [], []⟩
  erase := d6g_erase
  source := fun _ => some d6g_X
  headVote := fun _ _ => d6g_erase d6g_X
  finalityHead := fun _ => some d6g_X
  proposalFG := fun _ _ => none

private theorem d6g_core : FGCoreLaws d6g_reads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ := by cases st <;> simp
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem st C h := by cases Option.some.inj h; cases st <;> simp
  erase_inj := d6g_erase_inj

private theorem d6g_keep : FGTreeKeepLaws d6g_reads := ⟨fun _ _ => Finset.Subset.refl _⟩

private def d6g_height (B : FGBlock (Fin 1)) : FGHeight (Fin 1) :=
  ⟨B, B.slot, if B = .genesis then 1 else if B = d6g_X then 2 else 3,
    B, ∅, ∅, 0, .genesis⟩

private noncomputable abbrev d6g_obs : FGObservationReads d6g_reads where
  height := d6g_height
  finality := fun _ => ⟨.genesis, 0⟩
  controls nd := treeStoreControlsView d6g_height (d6g_reads.core nd).fg
  viable := fun _ X => X

private theorem d6g_invariant (st : Bool) :
    FGStoreInvariant d6g_obs.height d6g_obs.finality (d6g_reads.core st).fg := by
  cases st <;> constructor
  all_goals simp_all [d6g_height, d6g_X, d6g_Y, FGBlock.parent,
    FGBlock.Preceq, FGBlock.preceq, lexKey]

private noncomputable abbrev d6g_safety : FGSafetyReads d6g_protocol 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := d6g_object
  decode := some
  decodeObject := fun o => some o.payload
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (some d6g_X, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun t => decide (t = 22)
  finalizedOut := fun _ => .genesis

private def d6g_timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal := fun s => 4 * s
  vote := fun s => 4 * s + 1
  early := fun s => 4 * s + 2
  freeze := fun s => 4 * s + 3
  release := fun s => 4 * s + 5
  gate := fun s => 4 * s + 6
  action := fun r => 8 * r + 6

private theorem d6g_timing_laws : FGTimingLaws d6g_timing where
  delta_pos := by decide
  rounds := by decide
  proposal_eq _ := by simp [d6g_timing]
  vote_eq _ := rfl
  early_eq _ := by simp [d6g_timing]
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [d6g_timing]; ring

private abbrev d6g_env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ t => decide (t = 22)

private noncomputable abbrev d6g_trace : V2.D.Run Unit d6g_protocol where
  honest := {()}
  horizon := 22
  events := [.restart () 22, .tick () 22, .deliver () (d6g_object d6g_row) 22]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem d6g_schedule : V2.D.ScheduleWellFormed d6g_env d6g_trace where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                   rcases he with rfl | rfl | rfl <;> decide
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have ht' : t = 22 := by simpa using ht
    subst t
    exact ⟨22, by norm_num⟩
  tick_total := by
    intro v hv t ht hn hh ha
    have : t = 22 := of_decide_eq_true ha
    subst t
    simp

private theorem d6g_actual_row : HonestRowAt d6g_safety d6g_env d6g_trace d6g_timing
    1 () 2 d6g_row := by
  unfold HonestRowAt
  decide

private theorem d6g_source_height : ∀ {j x r a h e},
    HonestRowAt d6g_safety d6g_env d6g_trace d6g_timing j x r a →
    namedEntry a.height_pair = some (h, e) → ∃ C,
      actionSourceFG d6g_reads d6g_env d6g_trace d6g_timing x r = some (some C) ∧
      h = (d6g_obs.height C).h := by
  intro j x r a h e ha he
  have hj : j = 1 := by
    have hget := ha.2.1
    have hl : j < 3 := by
      have := List.getElem?_eq_some_iff.mp hget
      exact this.1
    interval_cases j <;> simp_all [d6g_trace, d6g_timing]
  subst j
  have hr : r = 2 := by
    have htime : 22 = 8 * (r : Time) + 6 := by
      simpa [d6g_trace, d6g_timing] using ha.2.1
    have hrn : (22 : Nat) = 8 * r + 6 := by exact_mod_cast htime
    omega
  subst r
  have harow : a = d6g_row := by
    have hem := ha.2.2
    simp [V2.D.Run.emitsAt, V2.D.tick, d6g_protocol,
      d6g_trace, d6g_env, d6g_object, V2.D.Run.ownSeats] at hem
    exact hem.symm
  subst a
  have he' : (2 : Nat) = h ∧ (⟨1⟩ : BlockId) = e := by
    simpa [namedEntry, d6g_row] using he
  have hh : h = 2 := he'.1.symm
  subst h
  cases x
  exact ⟨d6g_X, by decide, by decide⟩

private theorem d6g_equal_time_cap : 2 ≤ honestFrontier d6g_reads d6g_env d6g_trace 22 :=
  reset_row_cap d6g_timing d6g_reads d6g_safety d6g_env d6g_trace d6g_obs
    (fun a => namedEntry a.height_pair) d6g_core d6g_keep
    (fun _i _x => d6g_invariant _) d6g_schedule d6g_source_height d6g_actual_row rfl le_rfl rfl

private theorem d6g_delivery_included :
    honestFrontier d6g_reads d6g_env d6g_trace 22 = 3 := by decide

private theorem d6g_cut_is_inclusive :
    honestFrontier d6g_reads d6g_env d6g_trace 22 =
      frontierAtIdx d6g_reads d6g_env d6g_trace (timeIdx d6g_trace 22) :=
  reset_inclusive_frontier d6g_reads d6g_env d6g_trace d6g_schedule 22

-- A tick-only or strict-time read loses the block delivered at the same time.
private theorem d6g_tick_cut_too_small :
    frontierAtIdx d6g_reads d6g_env d6g_trace (afterTicksIdx d6g_trace 22) <
      honestFrontier d6g_reads d6g_env d6g_trace 22 := by decide

private theorem d6g_restart_retains_source : d6g_X ∈ TFAt d6g_reads d6g_env d6g_trace 3 () :=
  tf_cumulative_all d6g_reads d6g_env d6g_trace d6g_core d6g_keep (by decide : 0 ≤ 3) ()
    (by simp [TFAt, V2.D.Run.stateBefore, V2.D.World.init])

private theorem d6g_last_cut_event :
    ∃ start ev, d6g_trace.events[start]? = some ev ∧ ev.time = 22 ∧
      timeIdx d6g_trace 22 = start + 1 :=
  (reset_inclusive_start_iff d6g_env d6g_trace d6g_schedule 22).mpr
    ⟨.deliver () (d6g_object d6g_row) 22, by simp, rfl⟩

private theorem d6g_no_event_at_other_time :
    ¬ ∃ start ev, d6g_trace.events[start]? = some ev ∧ ev.time = 30 ∧
      timeIdx d6g_trace 30 = start + 1 := by
  rw [reset_inclusive_start_iff d6g_env d6g_trace d6g_schedule]
  simp [V2.Event.time]

private noncomputable abbrev d6g_empty : V2.D.Run Unit d6g_protocol :=
  { d6g_trace with honest := ∅, events := [] }

private theorem d6g_empty_schedule : V2.D.ScheduleWellFormed d6g_env d6g_empty where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := List.nodup_nil
  in_horizon := by simp
  honest_only := by simp
  tick_public := by simp
  tick_total := by simp

private theorem d6g_empty_distinction :
    muOf d6g_safety d6g_env d6g_empty d6g_timing
      (fun a => namedEntry a.height_pair) 30 = 1 ∧
    resetCutFrontier d6g_reads d6g_env d6g_empty d6g_timing d6g_timing_laws 0 = 0 ∧
    ¬ d6g_empty.honest.Nonempty := by
  have ho : oldRowHeights d6g_safety d6g_env d6g_empty d6g_timing
      (fun a => namedEntry a.height_pair) 30 = ∅ := by
    ext h
    simp [oldRowHeights, HonestRowAt, d6g_empty]
  simp [muOf, ho, resetCutFrontier, honestFrontier, d6g_empty]

#print axioms d6g_source_height
#print axioms d6g_equal_time_cap
#print axioms d6g_cut_is_inclusive
#print axioms d6g_tick_cut_too_small
#print axioms d6g_restart_retains_source
#print axioms d6g_last_cut_event
#print axioms d6g_no_event_at_other_time
#print axioms d6g_empty_schedule
#print axioms d6g_empty_distinction

end AvailableChain.FGCompose.Tests.P0d6a
end
