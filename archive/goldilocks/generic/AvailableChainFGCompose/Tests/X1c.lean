module
public import AvailableChainFGCompose.Proofs.HolderClient

set_option linter.privateModule false

noncomputable section
public section

/-! Driver-interface controls, not concrete PC executions. One FG seat, two honest runtime
nodes, an actual own write, raw restore, and a later suppressed repeat. Every consumer's
premises below refer to this exact driver fold, with horizon 20 beyond every deadline. -/

namespace AvailableChain.FGCompose.Tests.X1c
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev electorate : Electorate (Fin 1) := ⟨fun _ => 1, fun _ => by decide⟩
private abbrev cfg : FGConfig := ⟨4⟩
private abbrev head : HeadFields := ⟨0, genesisRoot, 0⟩
private abbrev row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev old : RecordOnce := record_row_once RecordOnce.initial row
private def rec (st : Nat × Bool) : RecordOnce := if st.1 = 0 then RecordOnce.initial else old

private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Nat × Bool
  Label := Unit
  Duty := Time
  signLabel := fun _ => ()
  seats := fun _ => 1
  Payload := Row (Fin 1)
  Durable := Nat
  init := (0, false)
  clock := fun st _ => (st.1, true)
  actTime := id
  duties := fun t => [t]
  duties_spec := by intro d t; simp
  duties_nodup := by intro t; simp
  act := fun st _ _ => (createRowOnce electorate cfg (rec st) 0 (some .genesis) head).1
  gossip := fun _ _ => []
  process := fun st _ => st
  selfVisible := fun _ => true
  recordOwn := fun st _ => (1, st.2)
  durable := Prod.fst
  restore := fun d _ => (d, false)
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev wire : protocol.Object := ⟨.seat () 0, row⟩
private abbrev decode (o : protocol.Object) : Option (Row (Fin 1)) :=
  match o.auth with
  | .seat _ i => some { o.payload with signer := i }
  | .none => none

private abbrev reads : FGSafetyReads protocol 1 protocol.Object where
  proposalErase := fun _ => none
  proposalRows := fun _ => []
  encode := id
  decode := decode
  decodeObject := decode
  fgLabel := ()
  fgSeats := Equiv.refl _
  record := rec
  inputs := fun _ => (some .genesis, head)
  enabled := fun _ => true
  finalizedOut := fun _ => .genesis

private abbrev env : Generic.Env (Fin 2) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun x t => decide ((x = 0 ∧ (t = 6 ∨ t = 14)) ∨ (x = 1 ∧ t = 15))

private abbrev run : V2.D.Run (Fin 2) protocol where
  honest := {0, 1}
  horizon := 20
  events := [.tick 0 6, .restart 0 14, .tick 0 14, .tick 1 15]
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

private abbrev holder : Fin 1 → Fin 2 := fun _ => 0

private def hook (st : protocol.State)
    (op : FGDependencyOperation Unit (FGReceiptToken (Fin 2) protocol.Object) protocol.Object) :
    FGDependencyProgram protocol.State :=
  .finish (match op with
    | .ownRecord o => protocol.recordOwn st o
    | .idle => (st.1, false)
    | .ordinary _ => (st.1, false)
    | .rebuild _ => (st.1, false)
    | _ => st)

private def work (st : protocol.State) (e : V2.Event (Fin 2) protocol.Object) :
    List (FGDependencyCommand Unit (FGReceiptToken (Fin 2) protocol.Object) protocol.Object) :=
  match e with
  | .tick x t =>
    [.step .idle,
     .step (if st.2 then
       match (dependencyReleased env run st x t).head? with
       | some o => .ownRecord o
       | none => .idle
       else .idle),
     .step (.ordinary wire)]
  | .restart _ t => [.step (.reconstruct t), .step .idle, .step (.rebuild t)]
  | .deliver _ _ _ => []

private abbrev driver : FGDependencyDriver (Fin 2) Unit protocol where
  enter := fun st _ _ => st
  enterProgram := fun st _ _ => .finish st
  hookProgram := hook
  drain := fun st => (st.1, false)
  reconstruct := fun st _ => st
  rebuild := fun st _ => (st.1, false)
  retry := fun st _ _ _ => st
  work := work
  inheritRefusal := fun st _ _ => st
  notify := fun st _ _ => st
  replay := fun st _ _ => st

private def state (x : Fin 2) (k : Nat) : protocol.State :=
  (if x = 0 ∧ 3 ≤ k then 1 else 0,
   decide ((x = 0 ∧ (k = 1 ∨ k = 11)) ∨ (x = 1 ∧ k = 16)))

private abbrev trace (x : Fin 2) : FGDependencyTrace protocol.State where
  length := 20
  state := state x
  time := fun k => ((run.events[k / 5]?).map V2.Event.time).getD 0
  start := fun j => 5 * j
  entryCut := fun j => 5 * j + 1
  dutyCut := fun j => 5 * j + 2
  done := fun j => 5 * j + 4
  readCut := fun j => 5 * j + 2
  hookRead := fun _ _ _ _ _ => False

private def operation (x : Fin 2) (k : Nat) :
    FGDependencyOperation Unit (FGReceiptToken (Fin 2) protocol.Object) protocol.Object :=
  if x = 0 ∧ k = 2 then .ownRecord wire else
  match k % 5, run.events[k / 5]? with
  | 0, some (.tick y t) => if y = x then .clock t else .idle
  | 0, some (.restart y t) => if y = x then .restore t else .idle
  | 1, some (.restart _ t) => .reconstruct t
  | 3, some (.restart _ t) => .rebuild t
  | 3, some (.tick _ _) => .ordinary wire
  | _, _ => .idle

private abbrev obs : FGExecutionObs (Fin 2) protocol :=
  driverFGExecutionObs env run driver trace operation

private theorem node_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  have := x.isLt
  rcases x with ⟨x, hx⟩
  interval_cases x <;> simp

private theorem event_cases {j : Nat} {e : V2.Event (Fin 2) protocol.Object}
    (he : run.events[j]? = some e) :
    (j = 0 ∧ e = .tick 0 6) ∨ (j = 1 ∧ e = .restart 0 14) ∨
    (j = 2 ∧ e = .tick 0 14) ∨ (j = 3 ∧ e = .tick 1 15) := by
  rcases j with _ | _ | _ | _ | j <;> simp at he
  · exact Or.inl ⟨rfl, he.symm⟩
  · exact Or.inr (Or.inl ⟨rfl, he.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, he.symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, he.symm⟩))

private theorem prefix_state (x : Fin 2) (j : Nat) :
    obs.stateBefore j x = (if x = 0 ∧ 0 < j then 1 else 0, false) := by
  by_cases hj : j < 4
  · rcases node_cases x with rfl | rfl <;> interval_cases j <;> rfl
  · have ht : run.events.take j = run.events :=
      List.take_of_length_le (by exact Nat.le_of_not_gt hj)
    change ((run.events.take j).zipIdx).foldl _ _ = _
    rw [ht]
    simp only [show 0 < j by omega, and_true]
    rcases node_cases x with rfl | rfl <;> rfl

private theorem released (x : Fin 2) (j : Nat) :
    obs.released x j = if x = 0 ∧ j = 0 then [wire] else [] := by
  rcases node_cases x with rfl | rfl <;>
    rcases j with _ | _ | _ | _ | j <;> rfl

private theorem own_writes (x : Fin 2) (k : Nat) :
    obs.ownWrites x k = if x = 0 ∧ k = 2 then [wire] else [] := by
  by_cases hk : k < 20
  · rcases node_cases x with rfl | rfl <;> interval_cases k <;> rfl
  · simp only [driverFGExecutionObs, show ¬ k < (trace x).length from hk, ite_false]
    rw [ite_eq_right (by omega)]

private theorem no_accepts (x : Fin 2) (k : Nat) (o : FGReceiptToken (Fin 2) protocol.Object) :
    ¬ obs.accepts x k o := by
  rintro ⟨hk, b, hb⟩
  change k < 20 at hk
  rcases node_cases x with rfl | rfl <;> interval_cases k <;> cases hb

private theorem execution_laws : FGExecutionObsLaws env run obs where
  init_state x := by rw [prefix_state]; simp
  start_state j e x he := by
    rw [prefix_state]
    rcases event_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases node_cases x with rfl | rfl <;> rfl
  done_state j e x he := by
    rw [prefix_state]
    rcases event_cases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases node_cases x with rfl | rfl <;> rfl
  cut_order j e x he := by
    have hj : j < 4 := (List.getElem?_eq_some_iff.mp he).1
    change 5 * j < 5 * j + 1 ∧ 5 * j + 1 ≤ 5 * j + 2 ∧
      5 * j + 2 ≤ 5 * j + 4 ∧ 5 * j + 4 ≤ 20
    omega
  event_order i j ei ej x hi hj hij := by
    change 5 * i + 4 < 5 * j
    omega
  segment_time j e x k he hk hk' := by
    change 5 * j ≤ k at hk
    change k ≤ 5 * j + 4 at hk'
    change ((run.events[k / 5]?).map V2.Event.time).getD 0 = e.time
    rw [show k / 5 = j by omega, he]
    rfl
  tick_entry j x t he := by
    rcases event_cases he with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      cases h <;> rfl
  restart_entry j x t he := by
    rcases event_cases he with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> cases h
    rfl
  released_tick j x t he := by
    rcases event_cases he with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      cases h <;> rfl
  released_other j x hn := by
    rw [released]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact False.elim (hn 6 rfl)
    · rfl
  tick_done j x t he := by
    rcases event_cases he with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      cases h <;> rfl
  accept_origin x k o h := False.elim (no_accepts x k o h)
  accept_time x k o h := False.elim (no_accepts x k o h)
  tail_state j x hj := by
    rw [prefix_state, prefix_state]
    have : 0 < j := by change 4 ≤ j at hj; omega
    change (if x = 0 ∧ 0 < j then 1 else 0, false) =
      (if x = 0 ∧ 0 < 4 then 1 else 0, false)
    simp only [this, and_true, Nat.zero_lt_succ]
  own_source x k hw := by
    rw [own_writes] at hw
    split_ifs at hw with h
    · obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, 0, 6, rfl, by decide, by decide⟩
    · exact False.elim (hw rfl)
  own_state x k hw := by
    rw [own_writes] at hw
    split_ifs at hw with h
    · obtain ⟨rfl, rfl⟩ := h
      rfl
    · exact False.elim (hw rfl)
  own_complete j x t he := by
    rcases event_cases he with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      cases h <;> rfl

private theorem client_laws : FGHolderClientLaws reads electorate cfg env run obs holder where
  holder_eq _ := rfl
  holder_inj := fun a b _ => Subsingleton.elim a b
  initial_record := rfl
  record_step x k hk := by
    change k < 20 at hk
    rcases node_cases x with rfl | rfl <;> interval_cases k <;> rfl
  holder_rows j x t i he hi := by
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    change 0 = x at hi
    subst x
    rcases event_cases he with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      cases h <;> rfl
  nonholder_rows j x t he hn := by
    have hx : x = 1 := (node_cases x).resolve_left (fun h => hn 0 h.symm)
    subst x
    rw [obsOwnReleased_def, released,
      ite_eq_right (by intro h; exact (by decide : (1 : Fin 2) ≠ 0) h.1)]
    rfl

private abbrev timing : FGTiming where
  delta := 1
  roundSlots := 2
  proposal := fun s => 4 * s
  vote := fun s => 4 * s + 1
  early := fun s => 4 * s + 2
  freeze := fun s => 4 * s + 3
  release := fun s => 4 * s + 5
  gate := fun s => 4 * s + 6
  action := fun r => 4 * (r * 2 : Nat) + 6

private theorem timing_laws : FGTimingLaws timing where
  delta_pos := by decide
  rounds := by decide
  proposal_eq := by intro s; simp
  vote_eq := by intro s; rfl
  early_eq := by intro s; rfl
  freeze_eq := by intro s; rfl
  release_eq := by intro s; rfl
  gate_eq := by intro s; rfl
  action_eq := by intro r; rfl

private theorem schedule : V2.D.ScheduleWellFormed env run where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  honest_only := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  tick_public := by
    intro x t he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with h | h | h | h <;> cases h
    · exact ⟨6, rfl⟩
    · exact ⟨14, rfl⟩
    · exact ⟨15, rfl⟩
  tick_total := by
    intro x hx t ht ht' hphase ha
    have ha' := of_decide_eq_true ha
    rcases ha' with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> simp

private abbrev entry (a : protocol.Object) := namedEntry a.payload.height_pair

private theorem wire_laws : FGSafetyWireLaws reads where
  encode_injective := Function.injective_id
  decode_encode _ := rfl
  decode_auth a u h := by
    rcases a with ⟨auth, payload⟩
    cases auth with
    | none => cases h
    | seat l i => cases h; rfl
  decoded_visible o u h := by
    rcases o with ⟨auth, payload⟩
    cases auth with
    | none => cases h
    | seat l i => rfl
  carried o a h := False.elim (List.not_mem_nil h)

private theorem permission_wire_laws : FGRowPermissionWireLaws reads entry where
  decoded_wire o u h := by
    refine ⟨o, rfl, h, ?_⟩
    rcases o with ⟨auth, payload⟩
    cases auth with
    | none => cases h
    | seat l i => cases h; rfl

private theorem initial_history : FGRowRecordHistory RecordOnce.initial where
  invariant := recordInv_initial
  sent_history _ _ _ _ h := False.elim (List.not_mem_nil h)

private theorem old_history : FGRowRecordHistory old where
  invariant := recordInv_createRowOnce electorate cfg (Λ := RecordOnce.initial)
    recordInv_initial 0 (some .genesis) head
  sent_history h T timeout fp hm := by
    change (.vote h T timeout, fp) ∈ [row.onceKey] at hm
    have he := List.mem_singleton.mp hm
    cases he
    exact ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩

private theorem permission (j : Nat) :
    FGRowPermissionInputs reads (simplexHeightView electorate cfg)
      (obsDutyState obs 0 j) .genesis := by
  refine ⟨rfl, ?_⟩
  change own_lock (rec (state 0 (5 * j + 2))).toRecord 1
      (finality_pair (rec (state 0 (5 * j + 2))).toRecord head) = none ∨ _
  unfold rec state
  split_ifs <;> exact Or.inl (by decide +kernel)

private theorem common_premises_sat :
    FGExecutionObsLaws env run obs ∧ FGHolderClientLaws reads electorate cfg env run obs holder ∧
    V2.D.ScheduleWellFormed env run ∧ FGSafetyWireLaws reads ∧
    FGRowPermissionWireLaws reads entry ∧ FGTimingLaws timing ∧
    ({holder 0} : Finset (Fin 2)).Nonempty ∧ holder 0 ∈ run.honest ∧
    (∀ e ∈ run.events, e.time < run.horizon) ∧ 16 < run.horizon := by
  refine ⟨execution_laws, client_laws, schedule, wire_laws, permission_wire_laws,
    timing_laws, ⟨holder 0, Finset.mem_singleton_self _⟩, by decide, ?_, by decide⟩
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> decide

private theorem nonholder_premises_sat :
    FGExecutionObsLaws env run obs ∧ FGHolderClientLaws reads electorate cfg env run obs holder ∧
    run.events[3]? = some (.tick 1 15) ∧ (∀ i, holder i ≠ 1) ∧
    env.awake 1 15 = true ∧ 1 ∈ run.honest ∧ 16 < run.horizon :=
  ⟨common_premises_sat.1, common_premises_sat.2.1, rfl, fun _ => by change (0 : Fin 2) ≠ 1; decide,
    rfl, by decide, by decide⟩

private theorem nonholder_no_fg_release :
    (obsOwnReleased obs 1 3).filterMap reads.decodeObject = [] :=
  client_laws.nonholder_rows 3 1 15 rfl nonholder_premises_sat.2.2.2.1

private theorem extra_node_premises_sat :
    FGExecutionObsLaws env run obs ∧ FGHolderClientLaws reads electorate cfg env run obs holder ∧
    FGSafetyWireLaws reads ∧ holder 0 ∈ run.honest ∧
    (∃ x ∈ run.honest, ∀ i, holder i ≠ x) ∧ 16 < run.horizon :=
  ⟨execution_laws, client_laws, wire_laws, by decide,
    ⟨1, by decide, fun _ => by change (0 : Fin 2) ≠ 1; decide⟩,
    by decide⟩

private theorem extra_node_no_slash : obsSafetyNoSlash reads run obs (holder 0) :=
  safety_emitted_noSlash_driver reads electorate cfg env run driver trace operation
    execution_laws client_laws wire_laws 0 (by decide)

private theorem restart_premises_sat :
    FGExecutionObsLaws env run obs ∧ FGHolderClientLaws reads electorate cfg env run obs holder ∧
    run.events[0]? = some (.tick (holder 0) 6) ∧
    run.events[1]? = some (.restart (holder 0) 14) ∧
    run.events[2]? = some (.tick (holder 0) 14) ∧ holder 0 ∈ run.honest ∧
    ({holder 0} : Finset (Fin 2)).Nonempty ∧ 16 < run.horizon :=
  ⟨execution_laws, client_laws, rfl, rfl, rfl, by decide,
    ⟨holder 0, Finset.mem_singleton_self _⟩, by decide⟩

private theorem restart_own_record_survives :
    reads.record (obs.cutState 0 (obs.entry 0 1)) = old ∧
    reads.record (obs.stateBefore 2 0) = old ∧
    (obsOwnReleasedBefore obs 0 3).filterMap reads.decodeObject = [row] := by
  have h := safety_client_trace_driver reads electorate cfg env run driver trace operation
    execution_laws client_laws 0 (by decide) 3
  refine ⟨rfl, rfl, ?_⟩
  rw [h.2]
  rfl

private abbrev wrongHead : HeadFields := ⟨1, ⟨9⟩, 0⟩
private abbrev wrongReads : FGSafetyReads protocol 1 protocol.Object :=
  { reads with inputs := fun _ => (some .genesis, wrongHead) }

private theorem wrong_finality_premises_sat :
    FGExecutionObsLaws env run obs ∧ FGHolderClientLaws reads electorate cfg env run obs holder ∧
    run.events[0]? = some (.tick (holder 0) 6) ∧ holder 0 ∈ run.honest ∧
    env.awake (holder 0) 6 = true ∧ reads.enabled 6 = true ∧
    (wrongReads.inputs (obsDutyState obs 0 0)).1 =
      (reads.inputs (obsDutyState obs 0 0)).1 ∧
    (wrongReads.inputs (obsDutyState obs 0 0)).2 ≠
      (reads.inputs (obsDutyState obs 0 0)).2 ∧ 16 < run.horizon :=
  ⟨execution_laws, client_laws, rfl, by decide, rfl, rfl, rfl, by decide, by decide⟩

private theorem wrong_finality_rejected :
    ¬ FGHolderClientLaws wrongReads electorate cfg env run obs holder := by
  intro h
  have hr := h.holder_rows 0 0 6 0 rfl rfl
  change [row] = [] at hr
  cases hr

private theorem fresh_origin :
    ∀ b ∈ (reads.record (obs.stateBefore 0 (holder 0))).sent,
      ∃ k rSent a, k < 0 ∧ obsHonestRowAt reads run obs timing k (holder 0) rSent a ∧
        entry a = namedEntry b.1 := by
  intro b hb
  cases hb

private theorem prior_origin :
    ∀ b ∈ (reads.record (obs.stateBefore 2 (holder 0))).sent,
      ∃ k rSent a, k < 2 ∧ obsHonestRowAt reads run obs timing k (holder 0) rSent a ∧
        entry a = namedEntry b.1 := by
  intro b hb
  change b ∈ [row.onceKey] at hb
  have hb' := List.mem_singleton.mp hb
  subst b
  exact ⟨0, 0, wire, by decide, ⟨by decide, rfl, List.mem_singleton_self _⟩, rfl⟩

private theorem current_coverage_premises_sat :
    FGExecutionObsLaws env run obs ∧ FGHolderClientLaws reads electorate cfg env run obs holder ∧
    V2.D.ScheduleWellFormed env run ∧ FGRowPermissionWireLaws reads entry ∧
    FGTimingLaws timing ∧ holder 0 ∈ run.honest ∧
    run.events[0]? = some (.tick (holder 0) (timing.action 0)) ∧
    FGRowPermissionInputs reads (simplexHeightView electorate cfg)
      (obsDutyState obs (holder 0) 0) .genesis ∧
    FGRowRecordHistory (reads.record (obsDutyState obs (holder 0) 0)) ∧
    (∀ b ∈ (reads.record (obs.stateBefore 0 (holder 0))).sent,
      ∃ k rSent a, k < 0 ∧ obsHonestRowAt reads run obs timing k (holder 0) rSent a ∧
        entry a = namedEntry b.1) ∧
    env.awake (holder 0) (timing.action 0) = true ∧
    reads.enabled (timing.action 0) = true ∧ 16 < run.horizon :=
  ⟨execution_laws, client_laws, schedule, permission_wire_laws, timing_laws, by decide,
    rfl, permission 0, initial_history, fresh_origin, rfl, rfl, by decide⟩

private theorem prior_coverage_premises_sat :
    FGExecutionObsLaws env run obs ∧ FGHolderClientLaws reads electorate cfg env run obs holder ∧
    V2.D.ScheduleWellFormed env run ∧ FGRowPermissionWireLaws reads entry ∧
    FGTimingLaws timing ∧ holder 0 ∈ run.honest ∧
    run.events[2]? = some (.tick (holder 0) (timing.action 1)) ∧
    FGRowPermissionInputs reads (simplexHeightView electorate cfg)
      (obsDutyState obs (holder 0) 2) .genesis ∧
    FGRowRecordHistory (reads.record (obsDutyState obs (holder 0) 2)) ∧
    (∀ b ∈ (reads.record (obs.stateBefore 2 (holder 0))).sent,
      ∃ k rSent a, k < 2 ∧ obsHonestRowAt reads run obs timing k (holder 0) rSent a ∧
        entry a = namedEntry b.1) ∧
    env.awake (holder 0) (timing.action 1) = true ∧
    reads.enabled (timing.action 1) = true ∧ 16 < run.horizon :=
  ⟨execution_laws, client_laws, schedule, permission_wire_laws, timing_laws, by decide,
    rfl, permission 2, old_history, prior_origin, rfl, rfl, by decide⟩

private theorem current_coverage :
    ∃ a, obsHonestRowAt reads run obs timing 0 (holder 0) 0 a ∧
      a = wire ∧ entry a = some (1, genesisRoot) := by
  have h := rowPermission_covered_driver reads electorate cfg env run driver trace operation
    (simplexHeightView electorate cfg) timing entry execution_laws client_laws timing_laws
    permission_wire_laws schedule (fun _ => rfl) 0 0 0 .genesis (by decide) rfl
    (permission 0) initial_history fresh_origin rfl rfl
  rcases h with ⟨a, ha, he⟩ | ⟨k, rSent, a, hk, _⟩
  · exact ⟨a, ha, List.mem_singleton.mp ha.2.2, he⟩
  · omega

private theorem prior_coverage :
    ∃ k rSent a, k < 2 ∧ rSent ≤ 1 ∧ obsHonestRowAt reads run obs timing k 0 rSent a ∧
      a = wire ∧ entry a = some (1, genesisRoot) := by
  have h := rowPermission_covered_driver reads electorate cfg env run driver trace operation
    (simplexHeightView electorate cfg) timing entry execution_laws client_laws timing_laws
    permission_wire_laws schedule (fun _ => rfl) 0 2 1 .genesis (by decide) rfl
    (permission 2) old_history prior_origin rfl rfl
  rcases h with ⟨a, ha, _⟩ | ⟨k, rSent, a, hk, hr, ha, he⟩
  · have : a ∈ ([] : List protocol.Object) := ha.2.2
    cases this
  · have hm := ha.2.2
    change a ∈ obs.released 0 k at hm
    rw [released] at hm
    split_ifs at hm with hk0
    · exact ⟨k, rSent, a, hk, hr, ha, List.mem_singleton.mp hm, he⟩
    · cases hm

#print axioms nonholder_premises_sat
#print axioms nonholder_no_fg_release
#print axioms extra_node_premises_sat
#print axioms extra_node_no_slash
#print axioms restart_premises_sat
#print axioms restart_own_record_survives
#print axioms wrong_finality_premises_sat
#print axioms wrong_finality_rejected
#print axioms current_coverage_premises_sat
#print axioms prior_coverage_premises_sat
#print axioms current_coverage
#print axioms prior_coverage

end AvailableChain.FGCompose.Tests.X1c
end
