module
public import AvailableChainFGCompose.Proofs.Finality.History

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose.Tests.P0d7a1
open AvailableChain.SimplexFG AvailableChain.KitFG

-- A reachable interface trace with an actual signed row. This is not a production fixture.
private def d7g_first : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private def d7g_X : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [d7g_first]
private def d7g_row : Row (Fin 1) := ⟨0, .vote 2 ⟨1⟩ false, none⟩
private def d7g_Y : FGBlock (Fin 1) := .node d7g_X 2 ⟨2⟩ 0 [d7g_row]
private def d7g_last : Row (Fin 1) := ⟨0, .vote 3 ⟨2⟩ false, none⟩

private def d7g_erase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (d7g_erase p) s r (encFGBody x rs)

private theorem d7g_erase_inj : Function.Injective d7g_erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [d7g_erase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [d7g_erase] at h
    | node q t u y ts =>
      simp only [d7g_erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

private abbrev d7g_protocol : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Fin 3
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := Nat
  init := 0
  clock := fun st _ => st
  actTime := fun d => 8 * (d.val + 1) + 6
  duties := fun t => if t = 14 then [0] else if t = 22 then [1]
    else if t = 30 then [2] else []
  duties_spec := by
    intro d t
    fin_cases d <;> by_cases h : t = 14 <;> by_cases k : t = 22 <;>
      by_cases l : t = 30 <;> simp_all [eq_comm]
  duties_nodup := by intro t; split_ifs <;> simp
  act := fun _ d _ => some (if d = 0 then d7g_first else if d = 1 then d7g_row else d7g_last)
  gossip := fun _ _ => []
  process := fun st _ => st + 1
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

private noncomputable def d7g_object (a : Row (Fin 1)) : d7g_protocol.Object := ⟨.seat () 0, a⟩

private noncomputable abbrev d7g_reads :
    FGCoreReads d7g_protocol 1 Unit Unit (Row (Fin 1)) where
  core st := ⟨(), ⟨if st = 0 then {.genesis} else if st = 1 then {.genesis, d7g_X}
    else {.genesis, d7g_X, d7g_Y}, .genesis, .genesis, 0, st + 1⟩, [], []⟩
  erase := d7g_erase
  source := fun st => some (if st = 0 then .genesis else if st = 1 then d7g_X else d7g_Y)
  headVote := fun _ _ => d7g_erase d7g_X
  finalityHead := fun _ => some d7g_X
  proposalFG := fun _ _ => none

private def d7g_electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private def d7g_cfg : FGConfig := ⟨4⟩
private def d7g_height := KitFG.Window.certificateHeight d7g_electorate d7g_cfg 2
private def d7g_finality := KitFG.Window.certificateFinality d7g_electorate d7g_cfg 2

private noncomputable abbrev d7g_safety : FGSafetyReads d7g_protocol 1 (Row (Fin 1)) where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := d7g_object
  decode := some
  decodeObject := fun o => some o.payload
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := fun _ => RecordOnce.initial
  inputs := fun _ => (some d7g_X, ⟨0, ⟨0⟩, 0⟩)
  enabled := fun t => decide (t = 22)
  finalizedOut := fun _ => .genesis

private def d7g_timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal := fun s => 4 * s
  vote := fun s => 4 * s + 1
  early := fun s => 4 * s + 2
  freeze := fun s => 4 * s + 3
  release := fun s => 4 * s + 5
  gate := fun s => 4 * s + 6
  action := fun r => 8 * r + 6

private theorem d7g_timing_laws : FGTimingLaws d7g_timing where
  delta_pos := by decide
  rounds := by decide
  proposal_eq _ := by simp [d7g_timing]
  vote_eq _ := rfl
  early_eq _ := by simp [d7g_timing]
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq r := by simp [d7g_timing]; ring

private abbrev d7g_env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ t => decide (t = 14 ∨ t = 22 ∨ t = 30)

private noncomputable abbrev d7g_trace : V2.D.Run Unit d7g_protocol where
  honest := {()}
  horizon := 30
  events := [.tick () 14, .deliver () (d7g_object d7g_first) 15,
    .tick () 22, .deliver () (d7g_object d7g_row) 23, .tick () 30]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private theorem d7g_schedule : V2.D.ScheduleWellFormed d7g_env d7g_trace where
  horizon_nonneg := by decide
  sorted := by decide
  nodup := by decide
  in_horizon := by intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                   rcases he with rfl | rfl | rfl | rfl | rfl <;> decide
  honest_only := by intro e he; simp
  tick_public := by
    intro v t ht
    have h : t = 14 ∨ t = 22 ∨ t = 30 := by simpa [d7g_trace] using ht
    rcases h with rfl | rfl | rfl
    · exact ⟨14, by norm_num⟩
    · exact ⟨22, by norm_num⟩
    · exact ⟨30, by norm_num⟩
  tick_total := by
    intro v hv t ht hn hh ha
    have h : t = 14 ∨ t = 22 ∨ t = 30 := of_decide_eq_true ha
    rcases h with rfl | rfl | rfl <;> simp

private theorem d7g_actual_first : HonestRowAt d7g_safety d7g_env d7g_trace d7g_timing
    0 () 1 d7g_first := by unfold HonestRowAt; decide +kernel

private theorem d7g_actual_row : HonestRowAt d7g_safety d7g_env d7g_trace d7g_timing
    2 () 2 d7g_row := by unfold HonestRowAt; decide +kernel

private def d7g_wire : FGHistoryWireReads d7g_safety where
  heightPair := Row.height_pair
  finalityPair := Row.finality_pair
  signer := fun a => some a.signer
  decode_height _ _ h := by cases Option.some.inj h; rfl
  decode_finality _ _ h := by cases Option.some.inj h; rfl
  decode_signer _ _ h := by cases Option.some.inj h; rfl

private theorem d7g_weight :
    d7g_electorate.weightOf (historyFaulty d7g_safety d7g_trace) < d7g_electorate.q := by
  decide +kernel

private theorem d7g_state_zero (i : Nat) (hi : i ≤ 1) :
    V2.D.Run.stateBefore d7g_env d7g_trace i () = 0 := by
  interval_cases i <;> decide +kernel

private theorem d7g_state_one (i : Nat) (hi : 2 ≤ i) (hj : i ≤ 3) :
    V2.D.Run.stateBefore d7g_env d7g_trace i () = 1 := by
  interval_cases i <;> decide +kernel

private theorem d7g_origin :
    RawHistoryOrigin d7g_reads d7g_safety d7g_env d7g_trace d7g_timing d7g_wire := by
  intro i x B hh u hu
  cases x
  have hm := hh.2
  change B ∈ (if V2.D.Run.stateBefore d7g_env d7g_trace i () = 0 then
    {(FGBlock.genesis : FGBlock (Fin 1))}
    else if V2.D.Run.stateBefore d7g_env d7g_trace i () = 1 then {FGBlock.genesis, d7g_X}
    else {FGBlock.genesis, d7g_X, d7g_Y}) at hm
  have first (hi : 1 < i) (he : u = d7g_first) :
      ∃ a r, d7g_safety.decode a = some u ∧ d7g_wire.signer a = some u.signer ∧
        ∃ k o t, k < i ∧ d7g_trace.events[k]? = some (.deliver () o t) ∧
          ∀ z, RowSigner d7g_safety d7g_trace d7g_wire.signer a z →
            z ∈ d7g_trace.honest → HonestRowBefore d7g_safety d7g_env d7g_trace
              d7g_timing i z r a ∧ d7g_timing.action r ≤ t := by
    subst u
    refine ⟨d7g_first, 1, rfl, rfl, 1, d7g_object d7g_first, 15, hi, rfl, ?_⟩
    intro z hz hh
    cases z
    exact ⟨⟨0, by omega, d7g_actual_first⟩, by decide⟩
  split at hm
  · have he : B = .genesis := Finset.mem_singleton.mp hm
    subst B
    simp [chainRows] at hu
  · have hi : 1 < i := by
      by_contra hn
      have := d7g_state_zero i (by omega)
      contradiction
    split at hm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · simp [chainRows] at hu
      · exact first hi (by simpa [chainRows, d7g_X] using hu)
    · have hj : 3 < i := by
        by_contra hn
        have := d7g_state_one i (by omega) (by omega)
        contradiction
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · simp [chainRows] at hu
      · exact first hi (by simpa [chainRows, d7g_X] using hu)
      · have he : u = d7g_row ∨ u = d7g_first := by
          simpa [chainRows, d7g_Y, d7g_X] using hu
        rcases he with rfl | he
        · refine ⟨d7g_row, 2, rfl, rfl, 3, d7g_object d7g_row, 23, hj, rfl, ?_⟩
          intro z hz hh
          cases z
          exact ⟨⟨2, by omega, d7g_actual_row⟩, by decide⟩
        · exact first hi he

private theorem d7g_rows_bound : ∀ j z r a h t,
    HonestRowAt d7g_safety d7g_env d7g_trace d7g_timing j z r a →
    historyRowHeight d7g_safety d7g_wire a = some h → eventTime d7g_trace j = some t →
    t < 30 → h ≤ 2 := by
  intro j z r a h t hj ha ht hearly
  have hget := hj.2.1
  have hjl : j < 5 := (List.getElem?_eq_some_iff.mp hget).1
  have hj0 : j = 0 ∨ j = 2 := by
    interval_cases j <;> simp_all [eventTime, d7g_trace, d7g_timing, V2.Event.time]
  rcases hj0 with rfl | rfl
  all_goals
    have hem := hj.2.2
    simp [V2.D.Run.emitsAt, V2.D.tick, d7g_protocol, d7g_trace,
      d7g_env, d7g_object, V2.D.Run.ownSeats] at hem
    subst a
    have he := Option.some.inj ha
    change _ = h at he
    omega

private theorem d7g_held : HeldAt d7g_reads d7g_env d7g_trace 4 () d7g_Y := by
  unfold HeldAt
  decide +kernel

private theorem d7g_nonempty : ¬ d7g_electorate.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

private theorem d7g_certificates : FGCertificateLaws d7g_electorate d7g_height d7g_finality :=
  KitFG.Window.windowCertificateLaws d7g_electorate d7g_cfg 2 d7g_nonempty (by decide)

private theorem d7g_before : (d7g_height d7g_Y).h ≤ 3 :=
  raw_causal_cap_before (R := d7g_reads) (S := d7g_safety) (E := d7g_env)
    (rho := d7g_trace) (T := d7g_timing) (D := d7g_wire) (Ef := d7g_electorate)
    (H := d7g_height) (f := d7g_finality)
    (hc := d7g_certificates)
    (horigin := d7g_origin) d7g_schedule d7g_weight 2 30 d7g_rows_bound
    4 () d7g_Y (by decide) d7g_held

private theorem d7g_at_tick : (d7g_height d7g_Y).h ≤ 3 :=
  raw_causal_cap_at_tick (R := d7g_reads) (S := d7g_safety) (E := d7g_env)
    (rho := d7g_trace) (T := d7g_timing) (D := d7g_wire) (Ef := d7g_electorate)
    (H := d7g_height) (f := d7g_finality)
    (hc := d7g_certificates)
    (horigin := d7g_origin) d7g_schedule d7g_weight 2 30 d7g_rows_bound
    4 () d7g_Y () rfl d7g_held

private theorem d7g_through_action : (d7g_height d7g_Y).h ≤ 3 := by
  apply raw_causal_cap_through_action (R := d7g_reads) (S := d7g_safety) (E := d7g_env)
    (rho := d7g_trace) (T := d7g_timing) (D := d7g_wire) (Ef := d7g_electorate)
    (H := d7g_height) (f := d7g_finality)
    (hc := d7g_certificates)
    (horigin := d7g_origin) d7g_schedule d7g_weight
    (by intro a b hab; dsimp [d7g_timing]; exact_mod_cast (by omega : 8*a+6 < 8*b+6))
    2 2 _ _ 4 () d7g_Y (by decide) d7g_held
  · intro j z r a h t hj ha ht hearly
    exact d7g_rows_bound j z r a h t hj ha ht (hearly.trans_le (by decide))
  · intro j z a h hj ha
    apply d7g_rows_bound j z 2 a h 22 hj ha
    · unfold eventTime
      rw [hj.2.1]
      rfl
    · decide

-- The row is sent at action 2 and carried at a later delivery to the same node.
private theorem d7g_earlier_carried :
    HonestRowBefore d7g_safety d7g_env d7g_trace d7g_timing 4 () 2 d7g_row ∧
    d7g_row ∈ d7g_Y.rows ∧ d7g_trace.events[3]? = some (.deliver () (d7g_object d7g_row) 23) :=
  ⟨⟨2, by decide, d7g_actual_row⟩, by change d7g_row ∈ [d7g_row]; simp, rfl⟩

private theorem d7g_pre_one : ∀ j z r a h t,
    HonestRowAt d7g_safety d7g_env d7g_trace d7g_timing j z r a →
    historyRowHeight d7g_safety d7g_wire a = some h → eventTime d7g_trace j = some t →
    t < d7g_timing.action 2 → h ≤ 1 := by
  intro j z r a h t hj ha ht hearly
  have hget := hj.2.1
  have hjl : j < 5 := (List.getElem?_eq_some_iff.mp hget).1
  have hj0 : j = 0 := by
    change t < 22 at hearly
    interval_cases j
    · rfl
    · simp at hget
    · have eq : (22 : Time) = t := by
        simpa [eventTime, d7g_trace, V2.Event.time] using ht
      have bad : (22 : Time) < 22 := eq.symm ▸ hearly
      exact (lt_irrefl _ bad).elim
    · simp at hget
    · have eq : (30 : Time) = t := by
        simpa [eventTime, d7g_trace, V2.Event.time] using ht
      have bad : (30 : Time) < 22 := eq.symm ▸ hearly
      exact (not_lt_of_ge (by decide : (22 : Time) ≤ 30) bad).elim
  subst j
  have hem := hj.2.2
  simp [V2.D.Run.emitsAt, V2.D.tick, d7g_protocol, d7g_trace,
    d7g_env, d7g_object, V2.D.Run.ownSeats] at hem
  subst a
  have he := Option.some.inj ha
  change 1 = h at he
  omega

-- The weaker pre-action premise holds, but the current row and endpoint exceed its cap.
private theorem d7g_current_action_required :
    (d7g_height d7g_Y).h > 2 ∧
    ¬ (∀ j z a h, HonestRowAt d7g_safety d7g_env d7g_trace d7g_timing j z 2 a →
      historyRowHeight d7g_safety d7g_wire a = some h → h ≤ 1) := by
  refine ⟨by decide +kernel, ?_⟩
  intro h
  have bad := h 2 () d7g_row 2 d7g_actual_row rfl
  omega

private theorem d7g_strict_boundary :
    eventTime d7g_trace 2 = some (d7g_timing.action 2) ∧
    ¬ d7g_timing.action 2 < 22 ∧
    ¬ HeldAt d7g_reads d7g_env d7g_trace (V2.D.Run.idxBefore d7g_trace 22) () d7g_Y := by
  unfold HeldAt
  decide +kernel

private def d7g_F : FGBlock (Fin 1) := .node d7g_Y 3 ⟨3⟩ 0
  [⟨0, .vote 3 d7g_Y.root false, some ⟨2, d7g_X.root⟩⟩]

private theorem d7g_retained_crossing :
    KitFG.Window.RetainedW d7g_electorate d7g_cfg 2 d7g_Y 2 d7g_X ∧
    KitFG.Window.CoveredW d7g_electorate d7g_cfg 2 d7g_F 2 d7g_X ∧
    ¬ KitFG.Window.RetainedW d7g_electorate d7g_cfg 2 d7g_F 2 d7g_X := by
  unfold KitFG.Window.RetainedW KitFG.Window.CoveredW
  decide +kernel

-- A cumulative-store observation with no earlier delivery fails the origin law.
private noncomputable abbrev d7g_bad_reads :
    FGCoreReads d7g_protocol 1 Unit Unit (Row (Fin 1)) :=
  { d7g_reads with core := fun _ =>
      ⟨(), ⟨{.genesis, d7g_X, d7g_Y}, .genesis, .genesis, 0, 3⟩, [], []⟩ }

private theorem d7g_missing_delivery_rejected :
    ¬ RawHistoryOrigin d7g_bad_reads d7g_safety d7g_env d7g_trace d7g_timing d7g_wire := by
  intro h
  have hh : HeldAt d7g_bad_reads d7g_env d7g_trace 0 () d7g_Y := by
    unfold HeldAt
    decide +kernel
  have hu : d7g_row ∈ chainRows d7g_Y := by
    simp [chainRows, d7g_Y, d7g_X]
  obtain ⟨a, r, ha, hs, k, o, t, hk, _⟩ := h 0 () d7g_Y hh d7g_row hu
  omega

#print axioms d7g_origin
#print axioms d7g_before
#print axioms d7g_at_tick
#print axioms d7g_through_action
#print axioms d7g_earlier_carried
#print axioms d7g_pre_one
#print axioms d7g_current_action_required
#print axioms d7g_missing_delivery_rejected
#print axioms d7g_strict_boundary
#print axioms d7g_retained_crossing

end AvailableChain.FGCompose.Tests.P0d7a1
end
