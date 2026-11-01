module
public import AvailableChainFGSAInhabit.WeakContinuationWitness

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.SleepPositive
open WeakContinuationWitness

/-- Every validator sleeps at time two and wakes at time three. -/
def sleepEnv : Generic.Env Validator :=
  { strongEnv with
    t_GST := 3
    t_GST_nonneg := by decide
    awake := fun _ t => decide (t ≠ 2) }

def sleepNodes (t : Time) : List Validator := nodes.filter (sleepEnv.awake · t)

def sleepBatch (t : Time) (w : World) : World × List Event :=
  let wakes := if t = 3 then nodes.map (fun v => V2.Event.restart v t) else []
  let restored := wakes.foldl (V2.D.World.step sleepEnv (runData 9 [])) w
  let ticks := (sleepNodes t).foldl (fun acc v =>
    let result := V2.D.tick sleepEnv (runData 9 []) (acc.1 v) v t
    (Function.update acc.1 v result.1, acc.2 ++ result.2)) (restored, [])
  let deliveries := ticks.2.flatMap (fun o => (sleepNodes t).map (fun v => (v, o)))
  deliveries.foldl (fun acc vo =>
    if (fgsa params unitCodec).processed (acc.1 vo.1) vo.2 then acc else
      (V2.D.World.step sleepEnv (runData 9 []) acc.1 (.deliver vo.1 vo.2 t),
        acc.2 ++ [.deliver vo.1 vo.2 t]))
    (ticks.1, wakes ++ (sleepNodes t).map (fun v => .tick v t))

def sleepBuild : Nat → World × List Event
  | 0 => (V2.D.World.init, [])
  | n + 1 =>
    let before := sleepBuild n
    let next := sleepBatch (n : Time) before.1
    (next.1, before.2 ++ next.2)

/-- This run uses engine ticks, restore, and delivery handlers. -/
def sleepRun : V2.D.Run Validator (fgsa params unitCodec) := runData 9 (sleepBuild 10).2

/-- The first proposal after the wake has an empty previous-label pool. -/
def wakeProposal : Obj params :=
  ⟨.seat (.prop 2) ⟨0, by decide⟩,
    .proposal (.node .genesis 2 ⟨3⟩ (packBody (n := params.n) 0 []) [] [] [])⟩

/-- The four phase-zero restarts precede every event at the wake time. -/
theorem wake_phase_zero :
    (sleepRun.events.filter (fun e => decide (e.time = 3))).take 4 =
      nodes.map (fun v => .restart v 3) := by decide +kernel

/-- Sleeping validators have no tick or delivery event. -/
theorem sleep_has_no_events : ∀ e ∈ sleepRun.events, e.time ≠ 2 := by
  have h : sleepRun.events.all (fun e => decide (e.time ≠ 2)) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

/-- The joined proposer emits the exact named body after the wake. -/
theorem wake_proposal_emitted : V2.D.Run.emits sleepEnv sleepRun 0 wakeProposal 8 := by
  refine ⟨?_, ?_, ?_⟩
  · exact 48
  · decide +kernel
  · have h : V2.D.Run.emitsAt sleepEnv sleepRun 48 = [wakeProposal] := by
      exact @of_decide_eq_true _
        ((inferInstance : DecidableEq (List (Obj params))) _ _) (by decide +kernel)
    rw [h]
    exact List.mem_singleton_self _

/-- The real handler keeps this proposal at validator zero. -/
theorem wake_proposal_stored :
    toWire params wakeProposal ∈ (V2.D.Run.final sleepEnv sleepRun 0).st.proposals := by
  decide +kernel

/-- The emitted body belongs to the P-Fx receipt table. -/
theorem wake_proposal_table :
    (.node .genesis 2 ⟨3⟩ (packBody (n := params.n) 0 []) [] [] []) ∈
      fx_emittedTable sleepEnv sleepRun :=
  fx_emitted_in_table sleepEnv sleepRun 0 wakeProposal 8 _ wake_proposal_emitted rfl

/-- The finite table includes genesis and the emitted post-wake body. -/
def wakeTable : List (NamedProposal params.n) :=
  [.genesis, .node .genesis 2 ⟨3⟩ (packBody (n := params.n) 0 []) [] [] []]

private theorem wake_delivered_table (v : Validator) (o : Obj params) (t : Time)
    (he : V2.Event.deliver v o t ∈ sleepRun.events) (N : NamedProposal params.n)
    (hp : o.payload = .proposal N) : N ∈ wakeTable := by
  have h : sleepRun.events.all (fun e => match e with
      | .deliver _ o _ => match o.payload with
        | .proposal N => decide (N ∈ wakeTable)
        | _ => true
      | _ => true) = true := by decide +kernel
  have hn := List.all_eq_true.mp h _ he
  simpa only [hp, decide_eq_true_eq] using hn

private theorem wake_stored_table (i : Nat) (v : Validator) (N : NamedProposal params.n)
    (hm : N ∈ (V2.D.Run.stateBefore sleepEnv sleepRun i v).st.namedBodies) :
    N ∈ wakeTable := by
  have h : (List.range (sleepRun.events.length + 1)).all (fun j =>
      nodes.all (fun x => (V2.D.Run.stateBefore sleepEnv sleepRun j x).st.namedBodies.all
        (fun N => decide (N ∈ wakeTable)))) = true := by decide +kernel
  have bound (j : Nat) (hj : j ≤ sleepRun.events.length)
      (hn : N ∈ (V2.D.Run.stateBefore sleepEnv sleepRun j v).st.namedBodies) : N ∈ wakeTable := by
    have hv : v ∈ nodes := by fin_cases v <;> simp [nodes]
    exact of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp h j (List.mem_range.mpr (by omega))) v hv) N hn)
  by_cases hi : i ≤ sleepRun.events.length
  · exact bound i hi hm
  · apply bound sleepRun.events.length le_rfl
    change N ∈ ((sleepRun.events.take sleepRun.events.length).foldl
      (V2.D.World.step sleepEnv sleepRun) V2.D.World.init v).st.namedBodies
    change N ∈ ((sleepRun.events.take i).foldl
      (V2.D.World.step sleepEnv sleepRun) V2.D.World.init v).st.namedBodies at hm
    simpa only [List.take_length, List.take_of_length_le (le_of_not_ge hi)] using hm

/-- P23-A: both processed bodies and actual emissions have collision-free receipt roots. -/
theorem wake_receipt_roots : NamedReceiptRootCollisionFree params unitCodec sleepEnv sleepRun := by
  apply fx_receipt_roots_of_table sleepEnv sleepRun wakeTable
  · intro N hN
    obtain ⟨B, hB, hNB⟩ := hN
    have hb : B ∈ wakeTable := by
      rcases hB with ⟨v, o, t, he, hp⟩ | ⟨v, _, i, hm⟩
      · exact wake_delivered_table v o t he B hp
      · exact wake_stored_table i v B hm
    simp only [wakeTable, List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
    rcases hb with rfl | rfl
    · left
      simpa [NamedProposal.Preceq, NamedProposal.preceq] using hNB
    · have hn := hNB
      simp only [NamedProposal.Preceq, NamedProposal.preceq,
        Bool.or_eq_true, decide_eq_true_eq] at hn
      rcases hn with hn | hn
      · exact Or.inr hn
      · exact Or.inl (by simpa [NamedProposal.Preceq, NamedProposal.preceq] using hn)
  · have h : (fx_emittedTable sleepEnv sleepRun).all
        (fun N => decide (N ∈ wakeTable)) = true := by decide +kernel
    exact fun N hN => of_decide_eq_true (List.all_eq_true.mp h N hN)
  · intro N hN A hAN
    simp only [wakeTable, List.mem_cons, List.not_mem_nil, or_false] at hN ⊢
    rcases hN with rfl | rfl
    · left
      simpa [NamedProposal.Preceq, NamedProposal.preceq] using hAN
    · have hn := hAN
      simp only [NamedProposal.Preceq, NamedProposal.preceq,
        Bool.or_eq_true, decide_eq_true_eq] at hn
      rcases hn with hn | hn
      · exact Or.inr hn
      · exact Or.inl (by simpa [NamedProposal.Preceq, NamedProposal.preceq] using hn)
  · intro N hN M hM he
    simp only [wakeTable, List.mem_cons, List.not_mem_nil, or_false] at hN hM
    rcases hN with rfl | rfl <;> rcases hM with rfl | rfl <;>
      simp [NamedProposal.root, genesisRoot] at he ⊢

private theorem sleep_time_bounds : ∀ e ∈ sleepRun.events, 0 ≤ e.time ∧ e.time ≤ 9 := by
  have h : sleepRun.events.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ 9)) = true := by
    decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

/-- The schedule has all awake public ticks and the exact phase ordering. -/
theorem wake_schedule : V2.D.ScheduleWellFormed sleepEnv sleepRun where
  horizon_nonneg := by decide
  sorted := by decide +kernel
  nodup := by decide +kernel
  in_horizon := sleep_time_bounds
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t he
    have ht := (sleep_time_bounds _ he).1
    change 0 ≤ t at ht
    refine ⟨t.toNat, ?_⟩
    change t = (t.toNat : Time) * 1
    rw [Int.toNat_of_nonneg ht, mul_one]
  tick_total := by
    intro v _ t _ ht hh ha
    change t ≤ 9 at hh
    have hn : t ≠ 2 := of_decide_eq_true ha
    interval_cases t <;> fin_cases v <;> first | contradiction | decide +kernel

/-- Every event is at an awake node; each wake has a preceding phase-zero restart. -/
theorem wake_sleep_valid : V2.D.SleepWellFormed sleepEnv sleepRun where
  tick_awake := by
    intro v t he
    exact decide_eq_true (sleep_has_no_events _ he)
  deliver_awake := by
    intro v o t he
    exact decide_eq_true (sleep_has_no_events _ he)
  restart_awake := by
    intro v t he
    exact decide_eq_true (sleep_has_no_events _ he)
  wake_restart := by
    intro v _ t _ _ hw
    have ht : t = 3 := by
      have hf := hw.2
      change decide (t - 1 ≠ 2) = false at hf
      simp only [decide_eq_false_iff_not, not_not] at hf
      dsimp [Time] at *
      omega
    subst t
    fin_cases v <;> decide +kernel

/-- Restart events are exactly the four wakes. -/
theorem wake_restarts : V2.D.RestartsAtWakes sleepEnv sleepRun := by
  have h : sleepRun.events.all (fun e => match e with
      | .restart _ t => decide (t = 3)
      | _ => true) = true := by decide +kernel
  intro v t he
  have ht : t = 3 := of_decide_eq_true (List.all_eq_true.mp h _ he)
  subst t
  refine ⟨by decide, ?_⟩
  change decide ((3 : Time) ≠ 2) = true ∧ decide (3 - 1 ≠ 2) = false
  decide

private theorem wake_delivery_fields (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : sleepRun.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).wellFormed o = true ∧
      (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore sleepEnv sleepRun i v) o = true ∧
      (fgsa params unitCodec).processed (V2.D.Run.stateBefore sleepEnv sleepRun i v) o = false := by
  have h : (List.range sleepRun.events.length).all (fun j => match sleepRun.events[j]? with
      | some (.deliver x a _) =>
        (fgsa params unitCodec).wellFormed a &&
          (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore sleepEnv sleepRun j x) a &&
          !(fgsa params unitCodec).processed (V2.D.Run.stateBefore sleepEnv sleepRun j x) a
      | _ => true) = true := by decide +kernel
  have hx := List.all_eq_true.mp h i (List.mem_range.mpr (List.getElem?_eq_some_iff.mp he).1)
  simpa only [he, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using hx

/-- Each actual handler call has its wire, dependencies, and freshness checks. -/
theorem wake_delivery_valid : V2.D.DeliveryWellFormed sleepEnv sleepRun where
  wire := fun i v o t he => (wake_delivery_fields i v o t he).1
  deps := fun i v o t he => (wake_delivery_fields i v o t he).2.1
  fresh := fun i v o t he => (wake_delivery_fields i v o t he).2.2

private def wake_origin (o : Obj params) (t : Time) (v : Validator) : Bool :=
  (List.range sleepRun.events.length).any (fun j => match sleepRun.events[j]? with
    | some (.tick x u) => decide (x = v ∧ u ≤ t) &&
        (V2.D.Run.emitsAt sleepEnv sleepRun j : List (Obj params)).any
          (fun (a : Obj params) => decide (a = o))
    | _ => false)

private theorem wake_authentic (v : Validator) (o : Obj params) (t : Time)
    (he : V2.Event.deliver v o t ∈ sleepRun.events) (u : Validator)
    (hu : V2.D.Run.holder sleepRun o.auth = some u) :
    ∃ send, send ≤ t ∧ V2.D.Run.emits sleepEnv sleepRun u o send := by
  have h : sleepRun.events.all (fun e => match e with
      | .deliver _ o t => nodes.all (fun u =>
        if V2.D.Run.holder sleepRun o.auth = some u then wake_origin o t u else true)
      | _ => true) = true := by decide +kernel
  have hnode : u ∈ nodes := by fin_cases u <;> simp [nodes]
  have horigin := List.all_eq_true.mp (List.all_eq_true.mp h _ he) u hnode
  rw [ite_eq_left hu] at horigin
  obtain ⟨j, _, hj⟩ := List.any_eq_true.mp horigin
  cases hk : sleepRun.events[j]? with
  | none => simp only [hk] at hj; cases hj
  | some e =>
    cases e with
    | restart x a => simp only [hk] at hj; cases hj
    | deliver x o' a => simp only [hk] at hj; cases hj
    | tick x a =>
      simp only [hk, Bool.and_eq_true, decide_eq_true_eq] at hj
      obtain ⟨⟨rfl, hat⟩, hm⟩ := hj
      obtain ⟨o', ho', heq⟩ := List.any_eq_true.mp hm
      have heq : (o' : Obj params) = o := @of_decide_eq_true _
        ((inferInstance : DecidableEq (Obj params)) _ _) heq
      exact ⟨a, hat, j, hk, heq ▸ ho'⟩

private theorem wake_no_carries (v : Validator) (o : Obj params) (t : Time)
    (he : V2.Event.deliver v o t ∈ sleepRun.events) : ∀ o', ¬ carriesS params o o' := by
  have h : sleepRun.events.all (fun e => match e with
      | .deliver _ o _ => match o.payload with
        | .proposal N => decide (N.raw = [] ∧ N.support = [] ∧ N.rows = [])
        | _ => true
      | _ => true) = true := by decide +kernel
  have hc := List.all_eq_true.mp h _ he
  intro o' ho'
  unfold carriesS at ho'
  cases hp : o.payload <;> simp only [hp] at ho' hc
  rename_i N
  have hn : N.raw = [] ∧ N.support = [] ∧ N.rows = [] := of_decide_eq_true hc
  simp only [hn.1, hn.2.1, hn.2.2, List.map_nil, List.not_mem_nil, or_self] at ho'

/-- All received signatures have an earlier real emission; proposals carry no forged wire. -/
theorem wake_signatures_valid : V2.D.UnforgeableSignatures sleepEnv sleepRun where
  unforgeable := by
    intro v o t hp u _ hu
    obtain ⟨i, hi⟩ := hp
    exact wake_authentic v o t (List.mem_of_getElem? hi) u hu
  carried := by
    intro v o t hp o' hc _ _ _
    obtain ⟨i, hi⟩ := hp
    exact (wake_no_carries v o t (List.mem_of_getElem? hi) o' hc).elim

/-- Positive sleep/wake execution: every engine and signature condition is checked. -/
theorem wake_execution_valid : V2.D.ExecutionValid sleepEnv sleepRun :=
  { wake_schedule, wake_sleep_valid, wake_delivery_valid, wake_signatures_valid with }

/-- The phase-zero restores set both clocks to the exact wake time. -/
theorem wake_restore_clock (v : Validator) :
    (V2.D.Run.stateAfterRestartsAt sleepEnv sleepRun 3 v).st.base.now = 3 ∧
      (V2.D.Run.stateAfterRestartsAt sleepEnv sleepRun 3 v).st.restartTime = some 3 := by
  fin_cases v <;> decide +kernel

/-- The full Base₂ packet is inhabited by this real sleep/wake execution. -/
theorem wake_base : Base₂ params unitCodec sleepEnv sleepRun :=
  ⟨wake_execution_valid, linked 9 _, cstar 9 _, wake_restarts, rfl, wake_receipt_roots⟩

/-- The old W1 source endpoint needs the approved recovery delay. -/
theorem old_w1_endpoint_gap :
    (247 : Time) ≠ recoveryStart params strongEnv + B_HF params 1 4 := by decide +kernel

end AvailableChain.FGSA.Run.Tests.SleepPositive
end
