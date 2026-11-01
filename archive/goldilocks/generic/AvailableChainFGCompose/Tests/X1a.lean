module
public import AvailableChainFGCompose.Proofs.ExecutionObs

set_option linter.privateModule false

public section

/-! Controls for the shared execution observation. Level: generic event fold (an interface
model, not an ExecutionValid protocol fixture). The positive instance is the ordinary
Duty fold on an explicit run with an equal-time restart and tick, then a delivery. Each
probe fails exactly one stated law: `*_isolated` proves every other law of the probe.
A second, row-bearing run controls strict history: a non-genesis block with a row is
admitted late; it has no early causal cap, and the HEAD bridge applies at a real witness. -/

namespace AvailableChain.FGCompose.Tests.X1a
open AvailableChain.SimplexFG

private theorem rows_nil (rs : List (Row (Fin 0))) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons row _ => exact Fin.elim0 row.signer

private def erase : FGBlock (Fin 0) → Block
  | .genesis => .genesis
  | .node p s r x _ => .node (erase p) s r x

private theorem erase_inj : Function.Injective erase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp [erase] at h ⊢
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [erase] at h
    | node p' s' r' x' rs' =>
      simp only [erase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hx⟩ := h
      have hpp := ih hp
      subst p' s' r' x'
      rw [rows_nil rs, rows_nil rs']

-- Each operation changes the counter, so a dropped or reordered event is visible.
private abbrev protocol : V2.ProtocolSpecD Unit where
  State := Nat
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := Unit
  init := 0
  clock := fun st _ => st + 1
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun st _ => st + 10
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun _ => ()
  restore := fun _ _ => 100
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private abbrev env : Generic.Env Unit where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

private noncomputable abbrev obj : protocol.Object := ⟨.none, ()⟩

private noncomputable abbrev mkRun (es : List (V2.Event Unit protocol.Object)) :
    V2.D.Run Unit protocol where
  honest := {()}
  horizon := 5
  events := es
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

/-- Restart and tick at the same time 1, then a delivery at 2. -/
private noncomputable abbrev trace : V2.D.Run Unit protocol :=
  mkRun [.restart () 1, .tick () 1, .deliver () obj 2]

private noncomputable abbrev obs : FGExecutionObs Unit protocol :=
  ordinaryFGExecutionObs env trace

/-! ### Positive instance: every premise is proved on the explicit run. -/

private theorem exec_laws : FGExecutionObsLaws env trace obs :=
  ordinaryFGExecutionObs_laws env trace

private noncomputable abbrev reads : FGCoreReads protocol 0 Unit Unit Unit where
  core _ := ⟨(), Store.init, [], []⟩
  erase := erase
  source := fun _ => some .genesis
  headVote := fun _ _ => erase .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem core_laws : FGCoreLaws reads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf _ _ := fun _ h => h
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases Option.some.inj h; exact Finset.mem_singleton_self _
  erase_inj := erase_inj

private theorem head_laws : FGHeadLaws reads env trace where
  head_mem _ _ _ _ := ⟨.genesis, Finset.mem_singleton_self _, rfl⟩
  parent_closed _ _ B hB := by
    have : B = .genesis := by simpa [Store.init] using hB
    subst this
    exact hB

private theorem restore_laws : FGTreeRestoreLaws reads := ⟨fun _ _ => rfl⟩

private theorem core_obs : FGObservedCoreLaws reads trace obs :=
  ordinaryFGExecutionObs_core env trace reads core_laws head_laws restore_laws

private theorem finality_obs : FGObservedFinalityLaws reads trace obs :=
  ordinaryFGExecutionObs_finality env trace reads core_laws
    (fun _ _ => KitFG.preceq_refl _) ⟨fun _ _ => rfl⟩

/-- Inspected cuts: raw restore, clock (duty), completion, raw delivery entry. -/
private theorem inspected_cuts :
    obs.cutState () (obs.entry () 0) = 100 ∧ obs.cutState () (obs.duty () 1) = 101 ∧
      obs.cutState () (obs.done () 1) = 101 ∧ obs.cutState () (obs.done () 2) = 111 ∧
      obs.cutLength () = 9 := by
  decide

/-- The equal-time restart cut precedes the tick cut, both at time 1. -/
private theorem equal_time_order :
    obs.done () 0 < obs.start () 1 ∧ obs.cutTime () (obs.done () 0) = 1 ∧
      obs.cutTime () (obs.start () 1) = 1 :=
  ⟨exec_laws.event_order 0 1 _ _ () rfl rfl (by decide),
    exec_laws.segment_time 0 _ () _ rfl (by decide) le_rfl,
    exec_laws.segment_time 1 _ () _ rfl le_rfl (by decide)⟩

/-- The delivery is accepted at its entry step with its original token. -/
private theorem delivery_accepted :
    obs.accepts () 6 (fgEventToken trace () 2 obj 2) :=
  ⟨2, obj, 2, rfl, rfl, rfl⟩

private theorem delivery_origin :
    (fgEventToken trace () 2 obj 2).receiptTime ≤ obs.cutTime () 6 ∧
      trace.events[(fgEventToken trace () 2 obj 2).eventIndex]? = some (.deliver () obj 2) :=
  ⟨exec_laws.accept_time _ _ _ delivery_accepted,
    (exec_laws.accept_origin _ _ _ delivery_accepted).2.2.1⟩

/-- The HEAD read at the tick's duty cut is held there. -/
private theorem head_at_duty :
    ∃ B ∈ (reads.core (obs.cutState () (obs.duty () 1))).fg.TF,
      reads.erase B = reads.headVote (obs.cutState () (obs.duty () 1)) 0 :=
  core_obs.head_mem 1 () 1 0 rfl

/-! ### Isolated probes -/

private theorem ev_cases {j : Nat} {e : V2.Event Unit protocol.Object}
    (h : trace.events[j]? = some e) :
    (j = 0 ∧ e = .restart () 1) ∨ (j = 1 ∧ e = .tick () 1) ∨
      (j = 2 ∧ e = .deliver () obj 2) := by
  rcases j with _ | _ | _ | j
  · simp at h; subst h; exact Or.inl ⟨rfl, rfl⟩
  · simp at h; subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · simp at h; subst h; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp at h

private theorem rel_step_nil (st : protocol.State) (e : V2.Event Unit protocol.Object) :
    ordinaryReleaseStep env trace () st e = [] := by
  cases e with
  | tick y t =>
    change (if y = () then _ else []) = []
    split_ifs <;> rfl
  | restart y t => rfl
  | deliver y o t => rfl

private theorem obs_rel_nil (j : Nat) : obs.released () j = [] := by
  change ((trace.events[j]?).map (ordinaryReleaseStep env trace () _)).getD [] = []
  cases h : trace.events[j]? with
  | none => rfl
  | some e => exact rel_step_nil _ e

private theorem obs_own_nil (k : Nat) : obs.ownWrites () k = [] := by
  change (if k % 3 = 1 then (obs.released () (k / 3)).filter _ else []) = []
  rw [obs_rel_nil]
  split_ifs <;> rfl

/-- Probe A drops the tick's clock effect from every later state (a consistent run
without the tick's clock). Only `tick_entry` fails. -/
private noncomputable abbrev droppedTick : FGExecutionObs Unit protocol :=
  { obs with
    stateBefore := fun j x => if 2 ≤ j then obs.stateBefore j x - 1 else obs.stateBefore j x
    cutState := fun x k => if 4 ≤ k then obs.cutState x k - 1 else obs.cutState x k }

private theorem dropped_fails : ¬ FGExecutionObsLaws env trace droppedTick := by
  intro h
  have := h.tick_entry 1 () 1 rfl
  revert this
  decide

private theorem dropped_isolated
    (tick_entry : ∀ j x t, trace.events[j]? = some (.tick x t) →
      droppedTick.cutState x (droppedTick.entry x j) =
        protocol.clock (droppedTick.cutState x (droppedTick.start x j)) t) :
    FGExecutionObsLaws env trace droppedTick where
  init_state x := by cases x; decide
  start_state j e x h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  done_state j e x h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  cut_order := exec_laws.cut_order
  event_order := exec_laws.event_order
  segment_time := exec_laws.segment_time
  tick_entry := tick_entry
  restart_entry j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  released_tick j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  released_other := exec_laws.released_other
  tick_done j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  accept_origin := exec_laws.accept_origin
  accept_time := exec_laws.accept_time
  tail_state j x h := by
    have h3 : 3 ≤ j := h
    change (if 2 ≤ j then obs.stateBefore j x - 1 else obs.stateBefore j x) =
      (if 2 ≤ 3 then obs.stateBefore 3 x - 1 else obs.stateBefore 3 x)
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    exact congrArg (· - 1) (exec_laws.tail_state j x h)
  own_source x k h := by cases x; exact absurd (obs_own_nil k) h
  own_state x k h := by cases x; exact absurd (obs_own_nil k) h
  own_complete := exec_laws.own_complete

/-- The permutation that swaps the cut blocks of the equal-time events 0 and 1. -/
private def perm (k : Nat) : Nat := if k < 3 then k + 3 else if k < 6 then k - 3 else k

/-- Probe B keeps every state but places the cuts of the equal-time tick before those of
the restart. Only `event_order` fails. -/
private noncomputable abbrev reversedCuts : FGExecutionObs Unit protocol :=
  { obs with
    cutState := fun x k => obs.cutState x (perm k)
    cutTime := fun x k => obs.cutTime x (perm k)
    start := fun _ j => if j = 0 then 3 else if j = 1 then 0 else 3 * j
    entry := fun _ j => if j = 0 then 4 else if j = 1 then 1 else 3 * j + 1
    duty := fun _ j => if j = 0 then 4 else if j = 1 then 1 else 3 * j + 1
    done := fun _ j => if j = 0 then 5 else if j = 1 then 2 else 3 * j + 2
    accepts := fun x k o => obs.accepts x (perm k) o }

private theorem reversed_cuts_fail : ¬ FGExecutionObsLaws env trace reversedCuts := by
  intro h
  have := h.event_order 0 1 _ _ () rfl rfl (by decide)
  revert this
  decide

private theorem reversed_isolated
    (event_order : ∀ (i j : Nat) (ei ej : V2.Event Unit protocol.Object) x,
      trace.events[i]? = some ei → trace.events[j]? = some ej → i < j →
        reversedCuts.done x i < reversedCuts.start x j) :
    FGExecutionObsLaws env trace reversedCuts where
  init_state := exec_laws.init_state
  start_state j e x h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  done_state j e x h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  cut_order j e x h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  event_order := event_order
  segment_time j e x k h h1 h2 := by
    cases x
    rcases ev_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change 3 ≤ k at h1; change k ≤ 5 at h2
      obtain rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 := by omega
      all_goals decide
    · change 0 ≤ k at h1; change k ≤ 2 at h2
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals decide
    · change 6 ≤ k at h1; change k ≤ 8 at h2
      obtain rfl | rfl | rfl : k = 6 ∨ k = 7 ∨ k = 8 := by omega
      all_goals decide
  tick_entry j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  restart_entry j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  released_tick j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  released_other := exec_laws.released_other
  tick_done j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  accept_origin x k o h := by
    cases x
    obtain ⟨j, w, t, hj, hk, ho⟩ := h
    have hk6 : k = 6 := by
      rcases ev_cases hj with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩ <;> cases he
      unfold perm at hk
      split_ifs at hk <;> omega
    subst hk6
    obtain ⟨_, h2, h3, h4, _⟩ := exec_laws.accept_origin () 6 o ⟨j, w, t, hj, hk, ho⟩
    refine ⟨by decide, h2, h3, h4, ?_⟩
    rcases ev_cases hj with ⟨rfl, he⟩ | ⟨rfl, he⟩ | ⟨rfl, he⟩ <;> cases he
    subst ho
    decide
  accept_time x k o h := exec_laws.accept_time x (perm k) o h
  tail_state := exec_laws.tail_state
  own_source x k h := by cases x; exact absurd (obs_own_nil k) h
  own_state x k h := by cases x; exact absurd (obs_own_nil k) h
  own_complete j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide

/-- Probe C attributes a release to the delivery event. Only `released_other` fails. -/
private noncomputable abbrev extraRelease : FGExecutionObs Unit protocol :=
  { obs with released := fun _ j => if j = 2 then [obj] else [] }

private theorem extra_release_fails : ¬ FGExecutionObsLaws env trace extraRelease := by
  intro h
  have := h.released_other 2 () (fun t ht => by cases ht)
  revert this
  decide

private theorem extra_release_isolated
    (released_other : ∀ j x, (∀ t, trace.events[j]? ≠ some (.tick x t)) →
      extraRelease.released x j = []) :
    FGExecutionObsLaws env trace extraRelease where
  init_state := exec_laws.init_state
  start_state := exec_laws.start_state
  done_state := exec_laws.done_state
  cut_order := exec_laws.cut_order
  event_order := exec_laws.event_order
  segment_time := exec_laws.segment_time
  tick_entry := exec_laws.tick_entry
  restart_entry := exec_laws.restart_entry
  released_tick j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  released_other := released_other
  tick_done j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide
  accept_origin := exec_laws.accept_origin
  accept_time := exec_laws.accept_time
  tail_state := exec_laws.tail_state
  own_source := exec_laws.own_source
  own_state := exec_laws.own_state
  own_complete j x t h := by
    cases x
    rcases ev_cases h with ⟨hj0, he⟩ | ⟨hj0, he⟩ | ⟨hj0, he⟩
    all_goals subst hj0
    all_goals cases he
    all_goals decide

/-! ### Strict history on a row-bearing run -/

private def rowR : Row (Fin 1) := ⟨0, .vote 3 ⟨2⟩ false, none⟩

private def rowB : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 [rowR]

private def rowErase : FGBlock (Fin 1) → Block
  | .genesis => .genesis
  | .node p s r x rs => .node (rowErase p) s r (encFGBody x rs)

private theorem rowErase_inj : Function.Injective rowErase := by
  intro A
  induction A with
  | genesis => intro B h; cases B <;> simp_all [rowErase]
  | node p s r x rs ih =>
    intro B h
    cases B with
    | genesis => simp [rowErase] at h
    | node q t u y ts =>
      simp only [rowErase, Block.node.injEq] at h
      obtain ⟨hp, hs, hr, hb⟩ := h
      obtain ⟨hx, hrows⟩ := encFGBody_inj hb
      cases ih hp
      cases hs
      cases hr
      cases hx
      cases hrows
      rfl

-- The state records whether the row-bearing block was admitted (by any delivery).
private abbrev rowsProtocol : V2.ProtocolSpecD Unit where
  State := Bool
  Label := Unit
  Duty := Empty
  signLabel := Empty.elim
  seats := fun _ => 1
  Payload := Unit
  Durable := Bool
  init := false
  clock := fun st _ => st
  actTime := Empty.elim
  duties := fun _ => []
  duties_spec := by intro d; cases d
  duties_nodup := by intro t; exact List.nodup_nil
  act := fun _ d _ => Empty.elim d
  gossip := fun _ _ => []
  process := fun _ _ => true
  selfVisible := fun _ => false
  recordOwn := fun st _ => st
  durable := fun st => st
  restore := fun d _ => d
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => false
  handles := fun _ _ _ => False
  carries := fun _ _ => False

private noncomputable abbrev rowObj : rowsProtocol.Object := ⟨.none, ()⟩

/-- Tick at 1, the late admission by a delivery at 3, then a tick at 4. -/
private noncomputable abbrev rowTrace : V2.D.Run Unit rowsProtocol where
  honest := {()}
  horizon := 5
  events := [.tick () 1, .deliver () rowObj 3, .tick () 4]
  seatOf := fun _ _ => ()
  input := fun _ _ => ()

private noncomputable abbrev rowObs : FGExecutionObs Unit rowsProtocol :=
  ordinaryFGExecutionObs env rowTrace

private noncomputable abbrev rowReads : FGCoreReads rowsProtocol 1 Unit Unit Unit where
  core st := ⟨(), ⟨if st then {.genesis, rowB} else {.genesis}, .genesis, .genesis, 0, 1⟩,
    [], []⟩
  erase := rowErase
  source := fun _ => none
  headVote := fun st _ => if st then rowErase rowB else rowErase .genesis
  finalityHead := fun _ => none
  proposalFG := fun _ _ => none

private theorem row_tf_closed (st : Bool) :
    ∀ B ∈ (rowReads.core st).fg.TF, B.parent ∈ (rowReads.core st).fg.TF := by
  cases st <;> decide

private theorem row_core_laws : FGCoreLaws rowReads where
  clock_fg _ _ := rfl
  clock_proposals _ _ := rfl
  clock_rowPool _ _ := rfl
  process_tf st _ B hB := by
    cases st
    · change B ∈ ({.genesis} : Finset (FGBlock (Fin 1))) at hB
      change B ∈ ({.genesis, rowB} : Finset (FGBlock (Fin 1)))
      rw [Finset.mem_singleton] at hB
      rw [hB]
      exact Finset.mem_insert_self _ _
    · exact hB
  process_proposals _ _ := List.prefix_rfl
  process_rowPool _ _ := List.prefix_rfl
  own_core _ _ := rfl
  source_mem _ _ h := by cases h
  erase_inj := rowErase_inj

private theorem row_head_laws : FGHeadLaws rowReads env rowTrace where
  head_mem i x t s := by
    change ∃ B ∈ (rowReads.core (V2.D.Run.stateBefore env rowTrace i x)).fg.TF,
      rowErase B = rowReads.headVote (V2.D.Run.stateBefore env rowTrace i x) s
    generalize V2.D.Run.stateBefore env rowTrace i x = st
    cases st
    · exact ⟨.genesis, by decide, rfl⟩
    · exact ⟨rowB, by decide, rfl⟩
  parent_closed i x := row_tf_closed _

private theorem row_core_obs : FGObservedCoreLaws rowReads rowTrace rowObs :=
  ordinaryFGExecutionObs_core env rowTrace rowReads row_core_laws row_head_laws ⟨fun _ _ => rfl⟩

private theorem row_ev_cases {j : Nat} {e : V2.Event Unit rowsProtocol.Object}
    (h : rowTrace.events[j]? = some e) :
    (j = 0 ∧ e = .tick () 1) ∨ (j = 1 ∧ e = .deliver () rowObj 3) ∨
      (j = 2 ∧ e = .tick () 4) := by
  rcases j with _ | _ | _ | j
  · simp at h; subst h; exact Or.inl ⟨rfl, rfl⟩
  · simp at h; subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · simp at h; subst h; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · simp at h

private theorem row_prefix5 :
    ∀ i ei, rowTrace.events[i]? = some ei → i ≤ 2 → ei.time < 5 := by
  intro i ei h _
  rcases row_ev_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem row_prefix4 :
    ∀ i ei, rowTrace.events[i]? = some ei → i ≤ 1 → ei.time < 4 := by
  intro i ei h hi
  rcases row_ev_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · decide
  · decide
  · omega

/-- The HEAD bridge (proved for every observation) applied at the second tick: its duty
state holds `rowB`, its whole prefix is before 5. -/
private theorem row_head_bridge : FGChainRowsAtCut rowReads rowTrace rowObs rowB 5 :=
  chainRows_of_head_obs env rowTrace rowReads rowObs row_core_laws
    (ordinaryFGExecutionObs_laws env rowTrace) row_core_obs 2 () 4 0 rowB 5
    (Finset.mem_singleton_self _) rfl (by decide) row_prefix5

/-- Inspected strict witness at deadline 4: receiver `()`, the delivery event 1 at time 3,
its completion cut 5 holds `rowB`. -/
private theorem row_witness_inspected :
    rowB ∈ (rowReads.core (rowObs.cutState () (rowObs.done () 1))).fg.TF ∧
      rowObs.start () 1 ≤ rowObs.done () 1 ∧ rowObs.cutTime () (rowObs.done () 1) = 3 := by
  decide

private theorem row_strict_positive : FGChainRowsAtCut rowReads rowTrace rowObs rowB 4 := by
  intro W hW _ _
  refine ⟨(), Finset.mem_singleton_self _, Or.inr ⟨1, _, 5, rfl, by decide, le_rfl,
    row_prefix4, ?_⟩⟩
  exact KitFG.ancestor_closed_of_parent_closed _ (row_tf_closed _) rowB
    row_witness_inspected.1 W hW

/-- Late admission: `rowB` is admitted at time 3, so no strict witness exists before 2. -/
private theorem row_late_no_cap : ¬ FGChainRowsAtCut rowReads rowTrace rowObs rowB 2 := by
  intro h
  obtain ⟨x, _, hcase⟩ := h rowB (KitFG.preceq_refl _) rowR (List.mem_singleton_self _)
  cases x
  rcases hcase with hinit | ⟨j, e, k, hj, h1, h2, hpre, hk⟩
  · revert hinit; decide
  · have ht := hpre j e hj le_rfl
    rcases row_ev_cases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change 0 ≤ k at h1; change k ≤ 2 at h2
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      all_goals (revert hk; decide)
    · revert ht; decide
    · revert ht; decide

/-- The final cut (outside every event segment) holds `rowB` and reads time 0: the
corrected predicate does not accept it. -/
private theorem row_final_cut :
    rowB ∈ (rowReads.core (rowObs.cutState () 9)).fg.TF ∧ rowObs.cutTime () 9 = 0 := by
  decide

#print axioms exec_laws
#print axioms core_laws
#print axioms head_laws
#print axioms restore_laws
#print axioms core_obs
#print axioms finality_obs
#print axioms inspected_cuts
#print axioms equal_time_order
#print axioms delivery_accepted
#print axioms delivery_origin
#print axioms head_at_duty
#print axioms dropped_fails
#print axioms dropped_isolated
#print axioms reversed_cuts_fail
#print axioms reversed_isolated
#print axioms extra_release_fails
#print axioms extra_release_isolated
#print axioms row_core_laws
#print axioms row_head_laws
#print axioms row_core_obs
#print axioms row_head_bridge
#print axioms row_witness_inspected
#print axioms row_strict_positive
#print axioms row_late_no_cap
#print axioms row_final_cut

end AvailableChain.FGCompose.Tests.X1a
end
