module
public import AvailableChainFGSAProofs.Proofs.Assembly.Root

@[expose] public section

/-! NV-ADV: an adversarial non-vacuity fixture.

The run has four seats and three honest nodes. Node 3 holds base seat 3; it is faulty and
silent, so it has no events. GST is 7, Δ = ΔF = 1, and every node is awake. Before GST the
schedule delivers only proposals. It holds every HEAD vote and FG row that an honest node
releases before GST, and it delivers them to all honest nodes at GST. The HEAD votes of
slot 0, sent at time 1, therefore arrive at time 7, after their Δ bound (`held_vote_delay`).
From GST on, every release goes to every honest node at its own time.

The run inhabits `ExecutionValid` (`nvExecution`), partial synchrony (`run_sync`),
`NamedRootCollisionFree` (`nvRoots`), `Base₂` (`base`) and `RecoverySleep₂` with G = 4
(`nvRecovery`). It inhabits the premise packages `HealingTimePrem`, `FinalitySet_W`,
`FirstFinalityPrem_W`, `FinalityLivenessGSTPrem_W` and `ProposalFinalGSTPrem_W`. The aggregate
`fgsaClaims` then gives availability with real inclusion of the slot-70 proposal
(`nvAvailableService`), FF5 at time 261 (`nvFF5`), FirstFinality (`nvFirstFinality`) and the
finality of the slot-66 proposal (`nvProposalFinal`).

The generator uses the real duty engine and the real FG-SA handlers, as the W1 generator in
AvailableChainFGSAInhabit/WeakContinuationWitness.lean does. TEST-SCOPE forbids an import of
that Inhabit module, so the generator lemmas are adapted copies (names with `w1_` or `i7_`
are copies with small changes). The proofs follow the generator symbolically; no step
evaluates the encoded trace.
-/

namespace AvailableChain.FGSA.Run.Tests.NonVacuity.Adversarial

open AvailableChain.SimplexFG

/-- The W1 parameters: n = 4, Δ = 1, k = 2, η = 0, R = 2, δt = 4. -/
def params : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 2
  δt := 4
  RLarge := by decide
  digest := fun d => ⟨d.slot + 1⟩

abbrev Validator := Fin 4
abbrev Event := V2.Event Validator (fgsa params unitCodec).Object
abbrev World := V2.D.World Validator (fgsa params unitCodec)

/-- GST is 7. Every node is awake at every time. -/
def env : Generic.Env Validator where
  Δ := 1
  Δ_pos := by decide
  t_GST := 7
  t_GST_nonneg := by decide
  awake _ _ := true

/-- One holder per base seat; node 0 proposes in every slot. Node 3 holds base seat 3. -/
def seatOf : (ℓ : RunLabel) → Fin (RunLabel.seats params ℓ) → Validator
  | .base _, i => i
  | .prop _, _ => 0

/-- The honest nodes. Node 3 is the faulty seat. -/
def honestNodes : Finset Validator := {0, 1, 2}

/-- Static run data for the schedule generator. -/
def runData (horizon : Time) (events : List Event) :
    V2.D.Run Validator (fgsa params unitCodec) where
  honest := honestNodes
  horizon := horizon
  events := events
  seatOf := seatOf
  input _ _ := ()

/-- The nodes that have events: the honest nodes, in index order. -/
def nodes : List Validator := [0, 1, 2]

/-- Run all honest ticks first, and keep the objects that they release. -/
def tickBatch (t : Time) (w : World) : World × List (Obj params) :=
  nodes.foldl (fun acc v =>
    let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
    (Function.update acc.1 v result.1, acc.2 ++ (show List (Obj params) from result.2))) (w, [])

/-- Deliver a fresh object with the real handler. -/
def deliverOne (t : Time) (acc : World × List Event) (vo : Validator × Obj params) :
    World × List Event :=
  if (fgsa params unitCodec).processed (acc.1 vo.1) vo.2 then acc else
    (V2.D.World.step env (runData 0 []) acc.1 (.deliver vo.1 vo.2 t),
      acc.2 ++ [.deliver vo.1 vo.2 t])

/-- The schedule delivers proposals before GST. -/
def isProp (o : Obj params) : Bool :=
  match o.payload with
  | .proposal _ => true
  | _ => false

/-- The objects offered at integer time `n`. Before GST: the released proposals only.
From GST on: the held objects, then the releases. -/
def offers (n : Nat) (held released : List (Obj params)) : List (Obj params) :=
  (if n < 7 then released.filter isProp else held ++ released).dedup

/-- Before GST the adversary holds every released HEAD vote and FG row. -/
def hold (n : Nat) (held released : List (Obj params)) : List (Obj params) :=
  if n < 7 then held ++ released.filter (fun o => !isProp o) else []

/-- Offer each object to every honest node before the next object. -/
def deliverAll (t : Time) (acc : World × List Event) (os : List (Obj params)) :
    World × List Event :=
  (os.flatMap (fun o => nodes.map (fun v => (v, o)))).foldl (deliverOne t) acc

/-- One time block: the honest ticks, then the offered deliveries. -/
def timeBatch (n : Nat) (w : World) (held : List (Obj params)) : World × List Event :=
  deliverAll n ((tickBatch n w).1, nodes.map (fun v => .tick v n))
    (offers n held (tickBatch n w).2)

/-- The generator state: the world, the trace, and the held objects. -/
structure GenState where
  world : World
  events : List Event
  held : List (Obj params)

/-- The first `steps` integer times, starting at zero. -/
def buildPrefix : Nat → GenState
  | 0 => ⟨V2.D.World.init, [], []⟩
  | n + 1 =>
      let prev := buildPrefix n
      ⟨(timeBatch n prev.world prev.held).1,
        prev.events ++ (timeBatch n prev.world prev.held).2,
        hold n prev.held (tickBatch n prev.world).2⟩

/-- The horizon: Jst + B_HF + W_W = 14 + 247 + 33 = 294 ≤ 300. -/
def horizon : Time := 300

/-- The adversarial run: the times 0 to 300. -/
def run : V2.D.Run Validator (fgsa params unitCodec) :=
  runData horizon (buildPrefix 301).events

theorem bp_world (n : Nat) :
    (buildPrefix (n + 1)).world = (timeBatch n (buildPrefix n).world (buildPrefix n).held).1 :=
  rfl

theorem bp_events (n : Nat) :
    (buildPrefix (n + 1)).events = (buildPrefix n).events ++
      (timeBatch n (buildPrefix n).world (buildPrefix n).held).2 := rfl

theorem bp_held (n : Nat) :
    (buildPrefix (n + 1)).held =
      hold n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2 := rfl

theorem run_events : run.events = (buildPrefix 301).events := rfl

theorem run_horizon : run.horizon = 300 := rfl

theorem run_honest : run.honest = honestNodes := rfl

theorem adv_design_numbers :
    params.n = 4 ∧ params.Δ = 1 ∧ params.k = 2 ∧ params.R = 2 ∧
    params.K_W = 2 ∧ params.δt = 4 ∧ params.η = 0 := by decide

theorem adv_delta_ratio : params.δt = 2 * params.R := by decide

theorem env_delta : env.Δ = params.Δ := rfl

theorem env_gst : env.t_GST = 7 := rfl

theorem adv_bounds : B_HF params 1 4 = 247 ∧ W_W params 1 1 = 33 ∧ kappaF params 1 = 2 := by
  decide

theorem nodes_honest (v : Validator) : v ∈ nodes ↔ v ∈ honestNodes := by
  fin_cases v <;> simp [nodes, honestNodes]

theorem faulty_eq : Gen.V2.Duty.faulty run = {3} := by
  rw [Gen.V2.Duty.faulty_def]
  decide

/-- One faulty seat: a = 1. -/
theorem faulty_card : (Gen.V2.Duty.faulty run).card = 1 := by
  rw [faulty_eq]
  rfl

theorem adv_fault_bound : (Gen.V2.Duty.faulty run).card ≤ (params.n - 1) / 3 := by
  rw [faulty_card]
  decide

theorem adv_cstar (h : Time) (es : List Event) :
    V2.D.CStar (fgsaFamilies params unitCodec).fresh (runData h es) := by
  intro label hf
  cases label with
  | prop s => exact hf.elim
  | base label =>
      cases label with
      | fg => exact hf.elim
      | head s => exact Function.bijective_id

theorem adv_linked (h : Time) (es : List Event) :
    V2.D.Linked (fgsaFamilies params unitCodec).linked (runData h es) := by
  refine ⟨4, Equiv.refl _, ?_⟩
  intro label hf
  cases label with
  | prop s => exact hf.elim
  | base label =>
      cases label with
      | head s => exact hf.elim
      | fg => exact ⟨rfl, fun _ => rfl⟩

theorem adv_gap_positive : 4 * params.Δ ≤ (4 : Time) := by decide

/-- Node 0 is honest and proposes every slot, so every window of length 4 has an honest slot. -/
theorem honest_slot (h : Time) (es : List Event) {s : Slot} (hs : 0 < s) :
    Gen.V2.Duty.HonestSlot (runData h es) (fgsaInterface params unitCodec) s :=
  ⟨hs, (by decide : (0 : Validator) ∈ honestNodes)⟩

theorem proposer_gap (h : Time) (es : List Event) (t : Time) (ht : env.t_GST ≤ t) :
    ∃ s, t < V2.D.proposalTime (fgsaInterface params unitCodec) s ∧
      V2.D.proposalTime (fgsaInterface params unitCodec) s ≤ t + 4 ∧
      Gen.V2.Duty.HonestSlot (runData h es) (fgsaInterface params unitCodec) s := by
  refine ⟨(t / 4).toNat + 1, ?_, ?_, honest_slot h es (Nat.zero_lt_succ _)⟩
  · change t < 4 * (((t / 4).toNat + 1 : Nat) : Int)
    have ht0 : (7 : Int) ≤ t := ht
    simp only [Time] at *
    omega
  · change 4 * (((t / 4).toNat + 1 : Nat) : Int) ≤ t + 4
    have ht0 : (7 : Int) ≤ t := ht
    simp only [Time] at *
    omega


/-! ### Single ticks -/

/-- Describe each release without evaluating the state or its codec data. -/
theorem adv_gen_tick_seat (st : Node params) (v : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) st v t).2) :
    ∃ l i m, o = ⟨.seat (RunDuty.signLabel l) i, m⟩ ∧ l ∈ duties params t ∧
      (fgsa params unitCodec).act ((fgsa params unitCodec).clock st t) l () = some m := by
  change o ∈ (if env.awake v t then
    (duties params t).flatMap (fun l =>
      ((runData 0 []).ownSeats (RunDuty.signLabel l) v).filterMap (fun i =>
        ((fgsa params unitCodec).act ((fgsa params unitCodec).clock st t) l ()).map
          (fun m => ⟨.seat (RunDuty.signLabel l) i, m⟩))) ++ [] else []) at ho
  split at ho
  · rw [List.append_nil] at ho
    obtain ⟨l, hl, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp ho
    obtain ⟨m, ha, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨l, i, m, rfl, hl, ha⟩
  · exact (List.not_mem_nil ho).elim

/-- Every emitted object is signed with a seat of its emitter. -/
theorem adv_gen_tick_holder (st : Node params) (v : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) st v t).2) :
    V2.D.Run.holder (runData 0 []) o.auth = some v := by
  change o ∈ (if env.awake v t then
    (duties params t).flatMap (fun l =>
      ((runData 0 []).ownSeats (RunDuty.signLabel l) v).filterMap (fun i =>
        ((fgsa params unitCodec).act ((fgsa params unitCodec).clock st t) l ()).map
          (fun m => ⟨.seat (RunDuty.signLabel l) i, m⟩))) ++ [] else []) at ho
  split at ho
  · rw [List.append_nil] at ho
    obtain ⟨l, _, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨i, hi, hm⟩ := List.mem_filterMap.mp ho
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.mp hm
    have hseat : seatOf (RunDuty.signLabel l) i = v
      := (List.mem_filter.mp hi).2 |> of_decide_eq_true
    exact congrArg some hseat
  · exact (List.not_mem_nil ho).elim

/-- Without gossip, a tick releases at most one object for each duty seat. -/
theorem adv_tick_nodup_without_gossip {In V : Type} [DecidableEq V]
    (P : V2.ProtocolSpecD In) (E : Generic.Env V) (rho : V2.D.Run V P)
    (st : P.State) (v : V) (t : Time) (hg : P.gossip (P.clock st t) t = [])
    (hD : V2.D.DutiesInjectiveAt P t) :
    (V2.D.tick E rho st v t).2.Nodup := by
  change (if E.awake v t then
    (P.duties t).flatMap (fun l =>
      (rho.ownSeats (P.signLabel l) v).filterMap (fun i =>
        (P.act (P.clock st t) l (rho.input v t)).map
          (fun m => (⟨.seat (P.signLabel l) i, m⟩ : P.Object)))) ++
        (P.gossip (P.clock st t) t).map (fun m => ⟨.none, m⟩) else []).Nodup
  rw [hg, List.map_nil]
  split
  · rw [List.append_nil, List.nodup_flatMap]
    constructor
    · intro l _
      apply List.Nodup.filterMap
      · intro i j o hi hj
        obtain ⟨m, _, hm⟩ := Option.map_eq_some_iff.mp hi
        obtain ⟨m', _, hm'⟩ := Option.map_eq_some_iff.mp hj
        have he := congrArg V2.Signed.auth (hm.trans hm'.symm)
        cases he
        rfl
      · exact (List.nodup_finRange _).filter _
    · apply List.Pairwise.imp_of_mem _ (P.duties_nodup t)
      intro l l' hl hl' hne o ho ho'
      obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp ho
      obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp ho'
      obtain ⟨m, _, hm⟩ := Option.map_eq_some_iff.mp hi
      obtain ⟨m', _, hm'⟩ := Option.map_eq_some_iff.mp hj
      have he := congrArg V2.Signed.auth (hm.trans hm'.symm)
      exact hne (hD l l' ((P.duties_spec l t).mp hl)
        ((P.duties_spec l' t).mp hl') (V2.Auth.seat.inj he).1)
  · exact List.nodup_nil

theorem adv_gen_tick_nodup (st : Node params) (v : Validator) (t : Time) :
    (V2.D.tick env (runData 0 []) st v t).2.Nodup :=
  adv_tick_nodup_without_gossip (fgsa params unitCodec) env (runData 0 []) st v t rfl
    (fgsa_dutiesInjectiveAt t)

/-! ### Batch structure -/

/-- The delivery fold adds only deliveries at its own time. -/
theorem adv_delivery_fold_mem (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (e : Event) :
    e ∈ (xs.foldl (deliverOne t) acc).2 ↔
      e ∈ acc.2 ∨ e ∈ (xs.foldl (deliverOne t) acc).2 ∧
        ∃ v o, e = .deliver v o t := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil]; tauto
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true
      · simp only [deliverOne, hp, ↓reduceIte]
        tauto
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ((he | he) | he)
          · exact Or.inl he
          · exact Or.inr ⟨Or.inl (Or.inr he), x.1, x.2, he⟩
          · exact Or.inr ⟨Or.inr he, he.2⟩
        · rintro (he | ⟨he, hd⟩)
          · exact Or.inl (Or.inl he)
          · exact he

/-- Deliveries form a sublist of the offers. This keeps the offer order. -/
theorem adv_delivery_fold_sublist (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) :
    ∃ ds, (xs.foldl (deliverOne t) acc).2 = acc.2 ++ ds ∧
      ds.Sublist (xs.map (fun vo => .deliver vo.1 vo.2 t)) := by
  induction xs generalizing acc with
  | nil => exact ⟨[], (List.append_nil _).symm, .slnil⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      obtain ⟨ds, he, hs⟩ := ih (deliverOne t acc x)
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true
      · simp only [deliverOne, hp, ↓reduceIte] at he ⊢
        exact ⟨ds, he, hs.cons _⟩
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte] at he ⊢
        refine ⟨.deliver x.1 x.2 t :: ds, ?_, hs.cons_cons _⟩
        simpa only [List.append_assoc, List.singleton_append] using he

theorem mem_offers (n : Nat) (held released : List (Obj params)) (o : Obj params) :
    o ∈ offers n held released ↔
      (n < 7 ∧ o ∈ released ∧ isProp o = true) ∨
        (7 ≤ n ∧ (o ∈ held ∨ o ∈ released)) := by
  unfold offers
  rw [List.mem_dedup]
  by_cases hn : n < 7
  · simp only [hn, ↓reduceIte, List.mem_filter, true_and]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h, _⟩)
      · exact h
      · omega
  · simp only [hn, ↓reduceIte, List.mem_append, false_and, false_or]
    exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩

theorem offers_nodup (n : Nat) (held released : List (Obj params)) :
    (offers n held released).Nodup := List.nodup_dedup _

theorem adv_timeBatch_block (n : Nat) (w : World) (held : List (Obj params)) :
    ∃ ds, (timeBatch n w held).2 = nodes.map (fun v => .tick v (n : Time)) ++ ds ∧
      ds.Sublist ((offers n held (tickBatch n w).2).flatMap
        (fun o => nodes.map (fun v => .deliver v o (n : Time)))) := by
  obtain ⟨ds, he, hs⟩ := adv_delivery_fold_sublist (n : Time)
    ((offers n held (tickBatch n w).2).flatMap (fun o => nodes.map (fun v => (v, o))))
    ((tickBatch n w).1, nodes.map (fun v => .tick v (n : Time)))
  refine ⟨ds, he, ?_⟩
  simp only [List.map_flatMap, List.map_map, Function.comp_def] at hs
  exact hs

theorem adv_timeBatch_shape (n : Nat) (w : World) (held : List (Obj params)) (e : Event)
    (he : e ∈ (timeBatch n w held).2) :
    (∃ v ∈ nodes, e = .tick v (n : Time)) ∨
      ∃ v ∈ nodes, ∃ o ∈ offers n held (tickBatch n w).2, e = .deliver v o (n : Time) := by
  obtain ⟨ds, hb, hs⟩ := adv_timeBatch_block n w held
  rw [hb] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact Or.inl ⟨v, hv, rfl⟩
  · obtain ⟨o, ho, hm⟩ := List.mem_flatMap.mp (hs.subset he)
    obtain ⟨v, hv, hve⟩ := List.mem_map.mp hm
    exact Or.inr ⟨v, hv, o, ho, hve.symm⟩

theorem adv_timeBatch_time (n : Nat) (w : World) (held : List (Obj params)) (e : Event)
    (he : e ∈ (timeBatch n w held).2) : e.time = (n : Time) := by
  rcases adv_timeBatch_shape n w held e he with ⟨v, _, rfl⟩ | ⟨v, _, o, _, rfl⟩ <;> rfl

theorem timeBatch_node (n : Nat) (w : World) (held : List (Obj params)) (e : Event)
    (he : e ∈ (timeBatch n w held).2) : e.node ∈ nodes := by
  rcases adv_timeBatch_shape n w held e he with ⟨v, hv, rfl⟩ | ⟨v, hv, o, _, rfl⟩ <;>
    exact hv

theorem adv_timeBatch_no_restart (n : Nat) (w : World) (held : List (Obj params))
    (v : Validator) (s : Time) : V2.Event.restart v s ∉ (timeBatch n w held).2 := by
  intro he
  rcases adv_timeBatch_shape n w held _ he with ⟨u, _, hu⟩ | ⟨u, _, o, _, hu⟩ <;> cases hu

theorem adv_timeBatch_tick (n : Nat) (w : World) (held : List (Obj params)) (v : Validator)
    (hv : v ∈ nodes) : V2.Event.tick v (n : Time) ∈ (timeBatch n w held).2 := by
  obtain ⟨ds, hb, _⟩ := adv_timeBatch_block n w held
  rw [hb]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem adv_prefix_times (steps : Nat) (e : Event) (he : e ∈ (buildPrefix steps).events) :
    0 ≤ e.time ∧ e.time < steps := by
  induction steps with
  | zero => simp [buildPrefix] at he
  | succ steps ih =>
      rw [bp_events] at he
      rcases List.mem_append.mp he with he | he
      · have := ih he
        simp only [Nat.cast_add, Nat.cast_one]
        simp only [Time] at *
        omega
      · rw [adv_timeBatch_time _ _ _ _ he]
        exact ⟨Int.natCast_nonneg _, by simp⟩

theorem prefix_nodes (steps : Nat) (e : Event) (he : e ∈ (buildPrefix steps).events) :
    e.node ∈ nodes := by
  induction steps with
  | zero => simp [buildPrefix] at he
  | succ steps ih =>
      rw [bp_events] at he
      rcases List.mem_append.mp he with he | he
      · exact ih he
      · exact timeBatch_node _ _ _ _ he

theorem adv_prefix_no_restart (steps : Nat) (v : Validator) (t : Time) :
    V2.Event.restart v t ∉ (buildPrefix steps).events := by
  induction steps with
  | zero => simp [buildPrefix]
  | succ steps ih =>
      rw [bp_events]
      simp only [List.mem_append, not_or]
      exact ⟨ih, adv_timeBatch_no_restart _ _ _ v t⟩

theorem adv_prefix_tick (steps t : Nat) (ht : t < steps) (v : Validator) (hv : v ∈ nodes) :
    V2.Event.tick v (t : Time) ∈ (buildPrefix steps).events := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      rw [bp_events]
      by_cases he : t = steps
      · subst t
        exact List.mem_append_right _ (adv_timeBatch_tick _ _ _ v hv)
      · exact List.mem_append_left _ (ih (by omega))

/-- The generator's traces are literal event prefixes of each other. -/
theorem prefix_prefix (m n : Nat) (h : m ≤ n) :
    (buildPrefix m).events.IsPrefix (buildPrefix n).events := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact List.prefix_refl _
  | succ n ih =>
    by_cases he : m = n + 1
    · subst m; exact List.prefix_refl _
    · rw [bp_events]
      exact (ih (by omega)).trans ⟨_, rfl⟩

theorem adv_prefix_blocks (steps : Nat) :
    (buildPrefix steps).events = (List.range steps).flatMap
      (fun (s : Nat) => (timeBatch s (buildPrefix s).world (buildPrefix s).held).2) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [bp_events]
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]

theorem adv_phase_le_two (e : Event) : e.phase ≤ 2 := by cases e <;> simp [V2.Event.phase]

theorem adv_key_le_delivery (e : Event) (v : Validator) (o : Obj params) (t : Time)
    (ht : e.time ≤ t) : e.key ≤ (V2.Event.deliver v o t).key := by
  exact Prod.Lex.toLex_le_toLex'.mpr ⟨ht, fun _ => adv_phase_le_two e⟩

theorem adv_delivery_fold_sorted (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (hs : acc.2.Pairwise (fun e f => e.key ≤ f.key))
    (ht : ∀ e ∈ acc.2, e.time ≤ t) :
    (xs.foldl (deliverOne t) acc).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction xs generalizing acc with
  | nil => exact hs
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hs ht
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte]
        apply ih
        · rw [List.pairwise_append]
          refine ⟨hs, List.pairwise_singleton _ _, ?_⟩
          intro e he f hf
          obtain rfl := List.mem_singleton.mp hf
          exact adv_key_le_delivery e _ _ _ (ht e he)
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact ht e he
          · obtain rfl := List.mem_singleton.mp he
            exact le_rfl

theorem adv_timeBatch_sorted (n : Nat) (w : World) (held : List (Obj params)) :
    (timeBatch n w held).2.Pairwise (fun e f => e.key ≤ f.key) := by
  apply adv_delivery_fold_sorted
  · simp [nodes, V2.Event.key, V2.Event.time, V2.Event.phase]
  · intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact le_rfl

theorem adv_prefix_sorted (steps : Nat) :
    (buildPrefix steps).events.Pairwise (fun e f => e.key ≤ f.key) := by
  induction steps with
  | zero => exact List.Pairwise.nil
  | succ steps ih =>
      rw [bp_events, List.pairwise_append]
      refine ⟨ih, adv_timeBatch_sorted _ _ _, ?_⟩
      intro e he f hf
      have he' := (adv_prefix_times steps e he).2
      have hf' := adv_timeBatch_time _ _ _ f hf
      apply Prod.Lex.toLex_le_toLex'.mpr
      dsimp only
      rw [hf']
      exact ⟨le_of_lt he', fun h => False.elim (ne_of_lt he' h)⟩

/-! ### Replay and freshness -/

/-- The event fold used by the generator. -/
def genFold (w : World) (es : List Event) : World :=
  es.foldl (V2.D.World.step env (runData 0 [])) w

/-- Freshness at each delivery, with the state advanced at every event. -/
def GenFresh : World → List Event → Prop
  | _, [] => True
  | w, e :: es =>
      (match e with
        | .deliver v o _ => (fgsa params unitCodec).processed (w v) o = false
        | _ => True) ∧
      GenFresh (V2.D.World.step env (runData 0 []) w e) es

theorem adv_genFold_append (w : World) (es ds : List Event) :
    genFold w (es ++ ds) = genFold (genFold w es) ds :=
  List.foldl_append

theorem adv_genFresh_append (w : World) (es ds : List Event) :
    GenFresh w (es ++ ds) ↔ GenFresh w es ∧ GenFresh (genFold w es) ds := by
  induction es generalizing w with
  | nil => simp [GenFresh, genFold]
  | cons e es ih =>
      simp only [List.cons_append, GenFresh, ih, genFold, List.foldl_cons]
      tauto

theorem adv_tick_fold_replay (t : Time) (vs : List Validator)
    (w : World) (os : List (Obj params)) :
    (vs.foldl (fun acc v =>
      let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).1 =
      genFold w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w os with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.foldl_cons, List.map_cons, genFold, V2.D.World.step] at *
      exact ih _ _

theorem adv_tickBatch_replay (t : Time) (w : World) :
    (tickBatch t w).1 = genFold w (nodes.map (fun v => .tick v t)) :=
  adv_tick_fold_replay t nodes w []

theorem adv_tick_list_fresh (t : Time) (vs : List Validator) (w : World) :
    GenFresh w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih _⟩

theorem adv_delivery_fold_replay_fresh (t : Time) (xs : List (Validator × Obj params))
    (w : World) (acc : World × List Event)
    (hr : acc.1 = genFold w acc.2) (hf : GenFresh w acc.2) :
    (xs.foldl (deliverOne t) acc).1 = genFold w (xs.foldl (deliverOne t) acc).2 ∧
      GenFresh w (xs.foldl (deliverOne t) acc).2 := by
  induction xs generalizing acc with
  | nil => exact ⟨hr, hf⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hp : (fgsa params unitCodec).processed (acc.1 x.1) x.2 = true
      · simpa only [deliverOne, hp, ↓reduceIte] using ih acc hr hf
      · simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte]
        apply ih
        · rw [adv_genFold_append, ← hr]
          rfl
        · rw [adv_genFresh_append, ← hr]
          exact ⟨hf, Bool.eq_false_iff.mpr hp, trivial⟩

theorem adv_timeBatch_replay_fresh (n : Nat) (w : World) (held : List (Obj params)) :
    (timeBatch n w held).1 = genFold w (timeBatch n w held).2 ∧
      GenFresh w (timeBatch n w held).2 :=
  adv_delivery_fold_replay_fresh n _ w _ (adv_tickBatch_replay n w) (adv_tick_list_fresh n nodes w)

theorem adv_prefix_replay_fresh (steps : Nat) :
    (buildPrefix steps).world = genFold V2.D.World.init (buildPrefix steps).events ∧
      GenFresh V2.D.World.init (buildPrefix steps).events := by
  induction steps with
  | zero => exact ⟨rfl, trivial⟩
  | succ steps ih =>
      have hb := adv_timeBatch_replay_fresh steps (buildPrefix steps).world (buildPrefix steps).held
      constructor
      · rw [bp_world, bp_events, adv_genFold_append, ← ih.1]
        exact hb.1
      · rw [bp_events, adv_genFresh_append, ← ih.1]
        exact ⟨ih.2, hb.2⟩

theorem adv_genFresh_get (w : World) (es : List Event) (hf : GenFresh w es)
    (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : es[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).processed (genFold w (es.take i) v) o = false := by
  induction es generalizing w i with
  | nil => simp at he
  | cons e es ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at he
          subst e
          exact hf.1
      | succ i =>
          exact ih _ hf.2 i (by simpa using he)

/-- Indexed replay for any run made from the generator's static data. -/
theorem adv_runData_stateBefore (h : Time) (es : List Event) (i : Nat) :
    V2.D.Run.stateBefore env (runData h es) i = genFold V2.D.World.init (es.take i) := rfl

attribute [irreducible] GenFresh

theorem run_fresh (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : run.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).processed (V2.D.Run.stateBefore env run i v) o = false :=
  adv_genFresh_get V2.D.World.init _ (adv_prefix_replay_fresh 301).2 i v o t he



/-! ### Emission origin -/

/-- A tick and its release, stated with the event prefix that it reads. -/
def GenEmits (w : World) (es : List Event) (v : Validator) (o : Obj params) (t : Time) : Prop :=
  ∃ pre post, es = pre ++ .tick v t :: post ∧
    o ∈ (V2.D.tick env (runData 0 []) (genFold w pre v) v t).2

/-- Every delivery has an emission no later than the delivery, in the same trace. -/
def GenOrigin (w : World) (es : List Event) : Prop :=
  ∀ v o t, V2.Event.deliver v o t ∈ es → ∃ u s, s ≤ t ∧ GenEmits w es u o s

/-- Every held object is a HEAD vote or FG row with an earlier emission. -/
def HeldOK (steps : Nat) : Prop :=
  ∀ o ∈ (buildPrefix steps).held, isProp o = false ∧
    ∃ u s, s < (steps : Time) ∧ GenEmits V2.D.World.init (buildPrefix steps).events u o s

theorem adv_genEmits_cons (w : World) (e : Event) (es : List Event)
    (v : Validator) (o : Obj params) (t : Time)
    (h : GenEmits (V2.D.World.step env (runData 0 []) w e) es v o t) :
    GenEmits w (e :: es) v o t := by
  obtain ⟨pre, post, he, ho⟩ := h
  exact ⟨e :: pre, post, congrArg (e :: ·) he, ho⟩

theorem adv_genEmits_append_left (w : World) (es ds : List Event)
    (v : Validator) (o : Obj params) (t : Time) (h : GenEmits w es v o t) :
    GenEmits w (es ++ ds) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := h
  exact ⟨pre, post ++ ds, by simp only [List.append_assoc, List.cons_append], ho⟩

theorem adv_genEmits_append_right (w : World) (es ds : List Event)
    (v : Validator) (o : Obj params) (t : Time) (h : GenEmits (genFold w es) ds v o t) :
    GenEmits w (es ++ ds) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := h
  refine ⟨es ++ pre, post, (List.append_assoc ..).symm, ?_⟩
  rwa [adv_genFold_append]

theorem adv_tick_fold_origin (t : Time) (vs : List Validator)
    (w : World) (os : List (Obj params)) (o : Obj params)
    (ho : o ∈ (vs.foldl (fun acc v =>
      let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2) :
    o ∈ os ∨ ∃ v, GenEmits w (vs.map (fun v => .tick v t)) v o t := by
  induction vs generalizing w os with
  | nil => exact Or.inl ho
  | cons v vs ih =>
      rcases ih _ _ ho with hm | ⟨u, hu⟩
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr ⟨v, [], vs.map (fun u => .tick u t), rfl, hm⟩
      · exact Or.inr ⟨u, adv_genEmits_cons w (.tick v t) _ u o t hu⟩

theorem adv_tickBatch_origin (t : Time) (w : World) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) :
    ∃ v, GenEmits w (nodes.map (fun v => .tick v t)) v o t := by
  rcases adv_tick_fold_origin t nodes w [] o ho with h | h
  · exact (List.not_mem_nil h).elim
  · exact h

/-- A release of a batch is an emission at its time in the trace that ends at the batch. -/
theorem batch_release_emits (steps : Nat) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).world).2) :
    ∃ v, GenEmits V2.D.World.init (buildPrefix (steps + 1)).events v o steps := by
  obtain ⟨v, hv⟩ := adv_tickBatch_origin steps (buildPrefix steps).world o ho
  obtain ⟨ds, he, _⟩ :=
    adv_timeBatch_block steps (buildPrefix steps).world (buildPrefix steps).held
  have hb : GenEmits (buildPrefix steps).world
      (timeBatch steps (buildPrefix steps).world (buildPrefix steps).held).2 v o steps := by
    rw [he]
    exact adv_genEmits_append_left _ _ ds v o steps hv
  refine ⟨v, ?_⟩
  rw [bp_events]
  apply adv_genEmits_append_right V2.D.World.init (buildPrefix steps).events _ v o steps
  rwa [← (adv_prefix_replay_fresh steps).1]

theorem isProp_false {o : Obj params} (h : isProp o = false) (b : NamedProposal params.n) :
    o.payload ≠ .proposal b := by
  intro he
  unfold isProp at h
  rw [he] at h
  cases h

theorem carries_nonprop {o o' : Obj params} (h : isProp o = false) :
    ¬ carriesS params o o' := by
  unfold carriesS
  unfold isProp at h
  split
  · rename_i N he
    rw [he] at h
    cases h
  · exact id

theorem timeBatch_delivered (n : Nat) (w : World) (held : List (Obj params)) (v : Validator)
    (o : Obj params) (s : Time) (hm : V2.Event.deliver v o s ∈ (timeBatch n w held).2) :
    s = n ∧ v ∈ nodes ∧ o ∈ offers n held (tickBatch n w).2 := by
  rcases adv_timeBatch_shape n w held _ hm with ⟨u, _, hu⟩ | ⟨u, hu, a, ha, he⟩
  · cases hu
  · cases he
    exact ⟨rfl, hu, ha⟩

/-- I-ORIGIN: deliveries have earlier emissions, and the held objects do as well. -/
theorem adv_prefix_origin (steps : Nat) :
    GenOrigin V2.D.World.init (buildPrefix steps).events ∧ HeldOK steps := by
  induction steps with
  | zero =>
    exact ⟨fun v o t hm => (List.not_mem_nil hm).elim, fun o ho => (List.not_mem_nil ho).elim⟩
  | succ steps ih =>
    obtain ⟨ho, hh⟩ := ih
    have lift (u : Validator) (o : Obj params) (s : Time)
        (h : GenEmits V2.D.World.init (buildPrefix steps).events u o s) :
        GenEmits V2.D.World.init (buildPrefix (steps + 1)).events u o s := by
      rw [bp_events]
      exact adv_genEmits_append_left _ _ _ u o s h
    constructor
    · intro v o t hm
      rw [bp_events] at hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨u, s, hs, he⟩ := ho v o t hm
        exact ⟨u, s, hs, lift u o s he⟩
      · obtain ⟨rfl, _, hoff⟩ := timeBatch_delivered _ _ _ v o t hm
        rcases (mem_offers _ _ _ o).1 hoff with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
        · obtain ⟨u, hu⟩ := batch_release_emits steps o hr
          exact ⟨u, steps, le_rfl, hu⟩
        · obtain ⟨_, u, s, hs, hu⟩ := hh o hr
          exact ⟨u, s, le_of_lt hs, lift u o s hu⟩
        · obtain ⟨u, hu⟩ := batch_release_emits steps o hr
          exact ⟨u, steps, le_rfl, hu⟩
    · intro o hm
      rw [bp_held] at hm
      unfold hold at hm
      split at hm
      · rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨hp, u, s, hs, hu⟩ := hh o hm
          refine ⟨hp, u, s, ?_, lift u o s hu⟩
          push_cast
          simp only [Time] at *
          omega
        · obtain ⟨hr, hp⟩ := List.mem_filter.mp hm
          obtain ⟨u, hu⟩ := batch_release_emits steps o hr
          refine ⟨by simpa using hp, u, steps, ?_, hu⟩
          push_cast
          simp only [Time] at *
          omega
      · exact (List.not_mem_nil hm).elim

theorem held_nonprop (steps : Nat) (o : Obj params) (ho : o ∈ (buildPrefix steps).held) :
    isProp o = false := ((adv_prefix_origin steps).2 o ho).1

/-- Relate the trace witness to the engine's indexed emission predicate. -/
theorem adv_genEmits_runData (h : Time) (es : List Event) (v : Validator) (o : Obj params)
    (t : Time)
    (he : GenEmits V2.D.World.init es v o t) : V2.D.Run.emits env (runData h es) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := he
  have hi : (runData h (pre ++ .tick v t :: post)).events[pre.length]? =
      some (.tick v t) := by simp [runData]
  refine ⟨pre.length, hi, ?_⟩
  rw [V2.D.Run.emitsAt, hi]
  simp only [V2.D.Run.stateBefore, runData, List.take_left']
  exact ho

/-! ### Duplicate freedom and the schedule -/

theorem adv_tick_fold_nodup (t : Time) (vs : List Validator) (hn : vs.Nodup)
    (w : World) (os : List (Obj params)) (ho : os.Nodup)
    (hh : ∀ o ∈ os, ∀ v ∈ vs, V2.D.Run.holder (runData 0 []) o.auth ≠ some v) :
    (vs.foldl (fun acc v =>
      let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2.Nodup := by
  induction vs generalizing w os with
  | nil => exact ho
  | cons v vs ih =>
      rw [List.nodup_cons] at hn
      rw [List.foldl_cons]
      apply ih hn.2
      · apply ho.append (adv_gen_tick_nodup (w v) v t)
        intro o hos hot
        exact hh o hos v (List.mem_cons_self ..) (adv_gen_tick_holder (w v) v t o hot)
      · intro o hom u hum
        rcases List.mem_append.mp hom with hom | hom
        · exact hh o hom u (List.mem_cons_of_mem _ hum)
        · rw [adv_gen_tick_holder (w v) v t o hom]
          intro he
          exact hn.1 (Option.some.inj he ▸ hum)

theorem adv_tickBatch_nodup (t : Time) (w : World) : (tickBatch t w).2.Nodup :=
  adv_tick_fold_nodup t nodes (by decide) w [] List.nodup_nil (by simp)

theorem adv_timeBatch_nodup (n : Nat) (w : World) (held : List (Obj params)) :
    (timeBatch n w held).2.Nodup := by
  obtain ⟨ds, he, hs⟩ := adv_timeBatch_block n w held
  rw [he]
  apply List.Nodup.append
  · exact (show nodes.Nodup from by decide).map (by intro v u h; cases h; rfl)
  · apply List.Nodup.sublist hs
    change ((offers n held (tickBatch n w).2).flatMap (fun (o : Obj params) =>
      nodes.map (fun v => (V2.Event.deliver v o n : V2.Event Validator (Obj params))))).Nodup
    rw [List.nodup_flatMap]
    constructor
    · intro o _
      exact (show nodes.Nodup from by decide).map (by intro v u h; cases h; rfl)
    · apply (offers_nodup n held _).imp
      intro o o' hne e he he'
      obtain ⟨v, _, hv⟩ := List.mem_map.mp he
      obtain ⟨u, _, hu⟩ := List.mem_map.mp he'
      exact hne (V2.Event.deliver.inj (hv.trans hu.symm)).2.1
  · intro e he hd
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    obtain ⟨o, _, ho⟩ := List.mem_flatMap.mp (hs.subset hd)
    obtain ⟨u, _, hu⟩ := List.mem_map.mp ho
    cases hu

theorem adv_prefix_nodup (steps : Nat) : (buildPrefix steps).events.Nodup := by
  induction steps with
  | zero => exact List.nodup_nil
  | succ steps ih =>
      rw [bp_events]
      apply ih.append (adv_timeBatch_nodup _ _ _)
      intro e he hb
      have hlt := (adv_prefix_times steps e he).2
      rw [adv_timeBatch_time _ _ _ _ hb] at hlt
      exact (lt_irrefl _ hlt)

/-- Each finite nonempty generated prefix has the required schedule. -/
theorem prefix_schedule (steps : Nat) :
    V2.D.ScheduleWellFormed env (runData steps (buildPrefix (steps + 1)).events) where
  horizon_nonneg := Int.natCast_nonneg _
  sorted := adv_prefix_sorted _
  nodup := adv_prefix_nodup _
  in_horizon e he := by
    obtain ⟨h0, ht⟩ := adv_prefix_times (steps + 1) e he
    change 0 ≤ e.time ∧ e.time ≤ (steps : Int)
    refine ⟨h0, ?_⟩
    have ht' : e.time < (steps : Int) + 1 := by exact_mod_cast ht
    exact Int.le_of_lt_add_one ht'
  honest_only e he := (nodes_honest _).1 (prefix_nodes _ e he)
  tick_public v t he := ⟨t.toNat, by
    have ht := (adv_prefix_times (steps + 1) (.tick v t) he).1
    change 0 ≤ t at ht
    change t = (t.toNat : Int) * 1
    rw [Int.toNat_of_nonneg ht, mul_one]⟩
  tick_total v hv t _ ht hh _ := by
    change t ≤ (steps : Int) at hh
    change (0 : Int) ≤ t at ht
    have hn : t.toNat < steps + 1 := by
      have hle : t.toNat ≤ steps := Int.toNat_le.mpr hh
      omega
    change V2.Event.tick v t ∈ (buildPrefix (steps + 1)).events
    simpa only [Int.toNat_of_nonneg ht] using
      adv_prefix_tick (steps + 1) t.toNat hn v ((nodes_honest v).2 hv)

theorem run_schedule : V2.D.ScheduleWellFormed env run := prefix_schedule 300

theorem noRestart : V2.D.NoRestart run := by
  intro i v t he
  exact adv_prefix_no_restart 301 v t (List.mem_of_getElem? he)

/-! ### Signatures -/

theorem adv_genOrigin_unforgeable (h : Time) (es : List Event)
    (horigin : GenOrigin V2.D.World.init es)
    (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes (runData h es) v o t) (u : Validator)
    (hu : V2.D.Run.holder (runData h es) o.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits env (runData h es) u o t' := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨x, s, hs, hx⟩ := horigin v o t (List.mem_of_getElem? hi)
  have hemit := adv_genEmits_runData h es x o s hx
  obtain ⟨pre, post, _, ho⟩ := hx
  have hholder := adv_gen_tick_holder (genFold V2.D.World.init pre x) x s o ho
  have hux : u = x := Option.some.inj (hu.symm.trans hholder)
  exact ⟨s, hs, hux.symm ▸ hemit⟩

/-- The delivered object came from an honest emission. -/
theorem run_delivery_origin (v : Validator) (o : Obj params) (t : Time)
    (hd : V2.Event.deliver v o t ∈ run.events) :
    ∃ u s, s ≤ t ∧ u ∈ nodes ∧ V2.D.Run.emits env run u o s := by
  obtain ⟨u, s, hs, hu⟩ := (adv_prefix_origin 301).1 v o t hd
  refine ⟨u, s, hs, ?_, adv_genEmits_runData _ _ u o s hu⟩
  obtain ⟨pre, post, he, _⟩ := hu
  have hm : V2.Event.tick u s ∈ (buildPrefix 301).events := by rw [he]; simp
  exact prefix_nodes 301 _ hm

/-! ### Store invariants (copied from W1) -/

private theorem joined_body {α : Type} {b : Prop} [Decidable b]
    {o : Option α} {m : α} (h : (if b then o else none) = some m) : o = some m := by
  split at h
  · exact h
  · cases h

/-- A row that is already in the pool does not change the store. -/
theorem adv_admitRow_duplicate (st : State params.n) (i : Fin params.n)
    (body : RowPayload)
    (h : (⟨.seat .fg i, body⟩ : RowWire params.n) ∈ st.rowPool) :
    admitRow params st ⟨.seat .fg i, body⟩ = st := by
  simp [admitRow, RowWire.decode?, h]

/-- The clock keeps both lists used by H. -/
theorem adv_clock_fields (st : State params.n) (t : Time) :
    (FGSA.clock params st t).proposals = st.proposals ∧
      (FGSA.clock params st t).rowPool = st.rowPool := by
  have hn (st : State params.n) : (normalizeS st).proposals = st.proposals ∧
      (normalizeS st).rowPool = st.rowPool := by
    unfold normalizeS
    split <;> exact ⟨rfl, rfl⟩
  have hg (st : State params.n) (s : Slot) :
      (gateStep params st s).proposals = st.proposals ∧
        (gateStep params st s).rowPool = st.rowPool := by
    unfold gateStep
    rw [(hn _).1, (hn _).2]
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  have hc : (clockPre params st t).proposals = st.proposals ∧
      (clockPre params st t).rowPool = st.rowPool := by
    unfold clockPre
    dsimp only
    split_ifs <;> exact ⟨rfl, rfl⟩
  unfold FGSA.clock
  dsimp only
  split
  · rw [(hg _ _).1, (hg _ _).2]
    exact hc
  · exact hc

theorem adv_clock_proposals (st : State params.n) (t : Time) :
    (FGSA.clock params st t).proposals = st.proposals := (adv_clock_fields st t).1

theorem adv_clock_rowPool (st : State params.n) (t : Time) :
    (FGSA.clock params st t).rowPool = st.rowPool := (adv_clock_fields st t).2

theorem adv_reconcile_fields (st : State params.n) :
    (reconcile st).proposals = st.proposals ∧ (reconcile st).rowPool = st.rowPool := by
  unfold reconcile normalizeS
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem adv_admitRow_eq (st : State params.n) (a : RowWire params.n) :
    admitRow params st a = st ∨
      admitRow params st a = { st with rowPool := st.rowPool ++ [a] } := by
  unfold admitRow
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

theorem adv_foldl_admitRow_eq (rows : List (RowWire params.n)) (st : State params.n) :
    ∃ pool, rows.foldl (admitRow params) st = { st with rowPool := pool } ∧
      st.rowPool ⊆ pool := by
  induction rows generalizing st with
  | nil => exact ⟨st.rowPool, rfl, List.Subset.refl _⟩
  | cons a rows ih =>
    rw [List.foldl_cons]
    rcases adv_admitRow_eq st a with he | he
    · rw [he]; exact ih st
    · rw [he]
      obtain ⟨pool, hp, hpre⟩ := ih { st with rowPool := st.rowPool ++ [a] }
      exact ⟨pool, hp, fun _ hm => hpre (List.mem_append_left _ hm)⟩

theorem adv_tick_st (st : Node params) (v : Validator) (t : Time) :
    (V2.D.tick env (runData 0 []) st v t).1.st = FGSA.clock params st.st t := by
  have hf (os : List (Obj params)) (nd : Node params) :
      (os.foldl (fgsa params unitCodec).recordOwn nd).st = nd.st := by
    induction os generalizing nd with
    | nil => rfl
    | cons o os ih => exact ih _
  exact hf _ _

/-- A property of every row in every stored proposal. -/
def GenStoredRows (P : RowWire params.n → Prop) (st : State params.n) : Prop :=
  ∀ w ∈ st.proposals, ∀ s b,
    w.decode = some (.block s b) → ∀ a ∈ b.rows, P a

/-- Selection keeps any property shared by pool rows and stored proposal rows. -/
theorem adv_gen_proposalRows_origin (P : RowWire params.n → Prop) (st : State params.n)
    (H : Block) (hp : ∀ a ∈ st.rowPool, P a) (hs : GenStoredRows P st) :
    ∀ a ∈ proposalRows params st H, P a := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin params st (st.slot params) H a ha with
    hm | ⟨o, ho, s, b, hd, hm⟩
  · exact hp a hm
  · exact hs o ho s b hd a hm

/-- The clock keeps the stored proposals. -/
theorem adv_gen_storedRows_clock (P : RowWire params.n → Prop) (st : State params.n)
    (t : Time) (hs : GenStoredRows P st) : GenStoredRows P (FGSA.clock params st t) := by
  simpa only [GenStoredRows, adv_clock_proposals] using hs

/-- A row fold keeps the stored proposals. -/
theorem adv_gen_storedRows_fold (P : RowWire params.n → Prop) (st : State params.n)
    (rows : List (RowWire params.n)) (hs : GenStoredRows P st) :
    GenStoredRows P (rows.foldl (admitRow params) st) := by
  obtain ⟨pool, he, _⟩ := adv_foldl_admitRow_eq rows st
  rw [he]
  exact hs

/-- A delivery adds only its own proposal to the stored proposals. -/
theorem adv_gen_storedRows_process (P : RowWire params.n → Prop) (st : State params.n)
    (o : Obj params) (hs : GenStoredRows P st)
    (ho : ∀ b, o.payload = .proposal b → ∀ a ∈ b.rows, P a) :
    GenStoredRows P (FGSA.process params st (toWire params o)) := by
  unfold FGSA.process
  cases hd : (toWire params o).decode with
  | none => exact hs
  | some m =>
    cases m with
    | vote s i b => exact hs
    | row i body =>
      dsimp only
      rcases adv_admitRow_eq st ⟨(toWire params o).auth, body⟩ with he | he <;>
        rw [he] <;> exact hs
    | block s b =>
      dsimp only
      have he : o.payload = .proposal b := by
        obtain ⟨auth, payload⟩ := o
        cases auth with
        | none => cases payload <;> cases hd
        | seat l i =>
          cases l with
          | base l => cases l <;> cases payload <;> cases hd
          | prop s => cases payload <;> cases hd; rfl
      have hr : ∀ a ∈ b.rows, P a := ho b he
      unfold admitBlock
      split
      · exact hs
      · split
        · exact hs
        · rename_i parent hparent
          split
          · apply adv_gen_storedRows_fold
            have hs' : GenStoredRows P
                { st with
                  base := GridCO.admitProposal params.toParams.engine st.base
                    (baseProposal s b.erase b.raw b.support) b.erase (b.raw.map baseHead)
                  fg := Window.on_block params params.K_W st.fg (fgBlock parent b.erase b.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal b⟩] } := by
              intro w hw s' b' hd' a ha
              rcases List.mem_append.mp hw with hw | hw
              · exact hs w hw s' b' hd' a ha
              · have he := List.mem_singleton.mp hw
                subst w
                cases hd'
                exact hr a ha
            split
            · exact hs'
            · simpa only [GenStoredRows, (adv_reconcile_fields _).1] using hs'
          · exact hs

/-- A delivery only adds to the row pool. -/
theorem adv_gen_process_pool_mono (st : State params.n) (o : Obj params) :
    st.rowPool ⊆ (FGSA.process params st (toWire params o)).rowPool :=
by
  unfold FGSA.process
  split
  · exact List.Subset.refl _
  · rcases adv_admitRow_eq st _ with he | he
    · rw [he]
    · rw [he]; exact fun _ hm => List.mem_append_left _ hm
  · unfold admitBlock
    split
    · exact List.Subset.refl _
    · split
      · exact List.Subset.refl _
      · split
        · obtain ⟨pool, he, hp⟩ := adv_foldl_admitRow_eq _ _
          rw [he]
          dsimp only at hp ⊢
          split at hp
          · exact hp
          · rwa [(adv_reconcile_fields _).2] at hp
        · exact List.Subset.refl _
  · exact List.Subset.refl _

/-- The invariant needed at the only proposer, node zero. -/
def GenPoolWitness (w : World) : Prop :=
  GenStoredRows (fun a => a ∈ (w 0).st.rowPool) (w 0).st

/-- Every generated proposal selects its rows at node zero. -/
theorem adv_gen_tick_proposal_rows (st : Node params) (v : Validator) (t : Time)
    (o : Obj params) (ho : o ∈ (V2.D.tick env (runData 0 []) st v t).2)
    (b : NamedProposal params.n)
    (he : o.payload = .proposal b) :
    v = 0 ∧ ∃ H, b.rows = proposalRows params (FGSA.clock params st.st t) H := by
  have hh := adv_gen_tick_holder st v t o ho
  obtain ⟨l, i, m, rfl, _, ha⟩ := adv_gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have hm : .head (headVote params (FGSA.clock params st.st t) s).root = m := Option.some.inj ha
    subst m
    cases he
  | fgAction r =>
    change (attest params (FGSA.clock params st.st t) st.record
      ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases he
  | propAction s =>
    have ha := joined_body ha
    have hv : v = 0 := (Option.some.inj hh).symm
    change (propose params (FGSA.clock params st.st t) s).map
        (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      cases he
      exact ⟨hv, _, rfl⟩

/-- Each tick keeps both fields used by the invariant. -/
theorem adv_gen_tick_pool_fields (w : World) (v : Validator) (t : Time) (u : Validator) :
    let w' := Function.update w v (V2.D.tick env (runData 0 []) (w v) v t).1
    (w' u).st.rowPool = (w u).st.rowPool ∧
      (w' u).st.proposals = (w u).st.proposals := by
  dsimp only
  by_cases hu : u = v
  · subst u
    rw [Function.update_self]
    have he := adv_tick_st (w v) v t
    exact ⟨(congrArg State.rowPool he).trans (adv_clock_rowPool _ _),
      (congrArg State.proposals he).trans (adv_clock_proposals _ _)⟩
  · rw [Function.update_of_ne hu]
    exact ⟨rfl, rfl⟩

/-- The invariant holds throughout the tick fold, and covers every released proposal. -/
theorem adv_gen_tick_fold_pool (t : Time) (vs : List Validator) (w : World)
    (os : List (Obj params)) (hw : GenPoolWitness w)
    (ho : ∀ o ∈ os, ∀ b, o.payload = .proposal b →
      ∀ a ∈ b.rows, a ∈ (w 0).st.rowPool) :
    let result := vs.foldl (fun acc v =>
      let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)
    GenPoolWitness result.1 ∧
      ∀ o ∈ result.2, ∀ b, o.payload = .proposal b →
        ∀ a ∈ b.rows, a ∈ (result.1 0).st.rowPool := by
  induction vs generalizing w os with
  | nil => exact ⟨hw, ho⟩
  | cons v vs ih =>
    let w' := Function.update w v (V2.D.tick env (runData 0 []) (w v) v t).1
    have hf := adv_gen_tick_pool_fields w v t 0
    have hw' : GenPoolWitness w' := by
      simpa only [GenPoolWitness, GenStoredRows, w', hf.1, hf.2] using hw
    apply ih w' _ hw'
    intro o hm b he a ha
    rw [hf.1]
    rcases List.mem_append.mp hm with hm | hm
    · exact ho o hm b he a ha
    · obtain ⟨hv, H, hrows⟩ := adv_gen_tick_proposal_rows (w v) v t o hm b he
      subst v
      rw [hrows] at ha
      have hs := adv_gen_storedRows_clock _ (w 0).st t hw
      exact adv_gen_proposalRows_origin _ _ H
        (fun a ha => (adv_clock_rowPool (w 0).st t) ▸ ha) hs a ha

/-- A delivery to the proposer preserves its stored-row invariant. -/
theorem adv_gen_deliver_pool (t : Time) (acc : World × List Event) (vo : Validator × Obj params)
    (hw : GenPoolWitness acc.1)
    (ho : ∀ b, vo.2.payload = .proposal b →
      ∀ a ∈ b.rows, a ∈ (acc.1 0).st.rowPool) :
    GenPoolWitness (deliverOne t acc vo).1 ∧
      (acc.1 0).st.rowPool ⊆ ((deliverOne t acc vo).1 0).st.rowPool := by
  unfold deliverOne
  split
  · exact ⟨hw, List.Subset.refl _⟩
  · dsimp only
    by_cases hv : vo.1 = 0
    · have hs := adv_gen_storedRows_process _ (acc.1 0).st vo.2 hw ho
      have hp := adv_gen_process_pool_mono (acc.1 0).st vo.2
      simp only [V2.D.World.step, hv, Function.update_self]
      refine ⟨?_, hp⟩
      intro w hm s b hd a ha
      exact hp (hs w hm s b hd a ha)
    · simpa only [GenPoolWitness, V2.D.World.step, Function.update_of_ne (Ne.symm hv)] using
        (show GenPoolWitness acc.1 ∧ (acc.1 0).st.rowPool ⊆ (acc.1 0).st.rowPool from
          ⟨hw, List.Subset.refl _⟩)

/-- All offers have rows already in the proposer's pool, which only grows. -/
theorem adv_gen_delivery_fold_pool (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (hw : GenPoolWitness acc.1)
    (ho : ∀ vo ∈ xs, ∀ b, vo.2.payload = .proposal b →
      ∀ a ∈ b.rows, a ∈ (acc.1 0).st.rowPool) :
    GenPoolWitness (xs.foldl (deliverOne t) acc).1 := by
  induction xs generalizing acc with
  | nil => exact hw
  | cons vo xs ih =>
    obtain ⟨hw', hp⟩ := adv_gen_deliver_pool t acc vo hw (ho vo (List.mem_cons_self ..))
    apply ih _ hw'
    intro vo' hv b he a ha
    exact hp (ho vo' (List.mem_cons_of_mem _ hv) b he a ha)

/-- Offered proposals are releases of the same batch; held objects are not proposals. -/
theorem offered_prop_released (n : Nat) (held released : List (Obj params))
    (hheld : ∀ o ∈ held, isProp o = false) (o : Obj params)
    (ho : o ∈ offers n held released) (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) : o ∈ released := by
  rcases (mem_offers n held released o).1 ho with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
  · exact hr
  · exact (isProp_false (hheld o hr) b hp).elim
  · exact hr

theorem adv_gen_timeBatch_pool (n : Nat) (w : World) (held : List (Obj params))
    (hw : GenPoolWitness w) (hheld : ∀ o ∈ held, isProp o = false) :
    GenPoolWitness (timeBatch n w held).1 := by
  obtain ⟨ht, ho⟩ := adv_gen_tick_fold_pool n nodes w [] hw (by simp)
  apply adv_gen_delivery_fold_pool (n : Time) _ _ ht
  intro vo hv b he a ha
  obtain ⟨o, hm, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hv
  subst vo
  exact ho o (offered_prop_released n held _ hheld o hm b he) b he a ha

theorem adv_gen_prefix_pool (steps : Nat) : GenPoolWitness (buildPrefix steps).world := by
  induction steps with
  | zero => intro w hw; exact (List.not_mem_nil hw).elim
  | succ steps ih =>
    rw [bp_world]
    exact adv_gen_timeBatch_pool steps _ _ ih (held_nonprop steps)

/-- H at every prefix batch: all selected rows are in the selecting node's pool. -/
theorem adv_prefix_selected_rows (steps : Nat) (t : Time) (H : Block) (a : RowWire params.n)
    (ha : a ∈ proposalRows params (FGSA.clock params ((buildPrefix steps).world 0).st t) H) :
    a ∈ (FGSA.clock params ((buildPrefix steps).world 0).st t).rowPool := by
  apply adv_gen_proposalRows_origin _ _ H (fun _ hm => hm) _ a ha
  rw [adv_clock_rowPool]
  exact adv_gen_storedRows_clock _ _ _ (adv_gen_prefix_pool steps)

/-- The vote pool is also unchanged by the clock. -/
theorem adv_clock_votes (st : State params.n) (t : Time) :
    (FGSA.clock params st t).base.votes = st.base.votes := by
  have hw (st : GridCO.State params.n .root) (b : Block) (g : Nat) (d : Time) :
      (GridCO.writeObligation st b g d).votes = st.votes := by
    rfl
  have hfold (xs : List Block) (levels : Block → List Nat) (d : Time)
      (st : GridCO.State params.n .root) :
      (xs.foldl (fun acc b => (levels b).foldl
        (fun acc g => GridCO.writeObligation acc b g d) acc) st).votes = st.votes := by
    have inner (gs : List Nat) (b : Block) (st : GridCO.State params.n .root) :
        (gs.foldl (fun acc g => GridCO.writeObligation acc b g d) st).votes = st.votes := by
      induction gs generalizing st with
      | nil => rfl
      | cons g gs ih => exact (ih _).trans (hw st b g d)
    induction xs generalizing st with
    | nil => rfl
    | cons b xs ih => exact (ih _).trans (inner _ b st)
  have hg (st : GridCO.State params.n .root) (a : Block) (s : Slot) :
      (SA.Root.gateFrom params.toParams a st s).votes = st.votes := by
    unfold SA.Root.gateFrom GridCO.gateFrom
    split
    · rfl
    · dsimp only
      split
      · rfl
      · exact hfold _ _ _ _
  have hn (st : State params.n) : (normalizeS st).base.votes = st.base.votes := by
    unfold normalizeS
    split <;> rfl
  have hgate (st : State params.n) (s : Slot) :
      (gateStep params st s).base.votes = st.base.votes := by
    unfold gateStep
    rw [hn]
    split
    · rfl
    · split
      · rfl
      · exact hg _ _ _
  have hc : (clockPre params st t).base.votes = st.base.votes := by
    unfold clockPre
    dsimp only
    split_ifs <;> rfl
  unfold FGSA.clock
  dsimp only
  split
  · rw [hgate]; exact hc
  · exact hc

/-- Known signatures in both pools and in stored proposal rows. -/
def GenKnown (P : Obj params → Prop) (st : State params.n) : Prop :=
  (∀ a ∈ st.rowPool, P (ofRow params a)) ∧
    GenStoredRows (fun a => P (ofRow params a)) st ∧
    ∀ h ∈ st.base.votes.filterMap liftHead?, P (ofHead params h)

theorem gen_known_init (P : Obj params → Prop) (v : Validator) :
    GenKnown P ((V2.D.World.init : World) v).st :=
  ⟨by simp [V2.D.World.init, fgsa, initial],
    by intro w hw; simp [V2.D.World.init, fgsa, initial] at hw,
    by simp [V2.D.World.init, fgsa, initial, GridCO.initial]⟩

theorem adv_gen_known_mono (P Q : Obj params → Prop) (st : State params.n)
    (h : GenKnown P st) (hp : ∀ o, P o → Q o) : GenKnown Q st :=
  ⟨fun a ha => hp _ (h.1 a ha),
    fun w hw s b hd a ha => hp _ (h.2.1 w hw s b hd a ha),
    fun a ha => hp _ (h.2.2 a ha)⟩

theorem adv_gen_known_clock (P : Obj params → Prop) (st : State params.n) (t : Time)
    (h : GenKnown P st) : GenKnown P (FGSA.clock params st t) := by
  simpa only [GenKnown, GenStoredRows, adv_clock_proposals, adv_clock_rowPool,
    adv_clock_votes] using h

theorem adv_gen_known_row (P : Obj params → Prop) (st : State params.n)
    (a : RowWire params.n) (h : GenKnown P st) (ha : P (ofRow params a)) :
    GenKnown P (admitRow params st a) := by
  rcases adv_admitRow_eq st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

theorem adv_gen_known_rows (P : Obj params → Prop) (rows : List (RowWire params.n))
    (st : State params.n) (h : GenKnown P st) (hr : ∀ a ∈ rows, P (ofRow params a)) :
    GenKnown P (rows.foldl (admitRow params) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (adv_gen_known_row P st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

theorem adv_gen_known_vote (P : Obj params → Prop) (st : GridCO.State params.n .root)
    (o : GridCO.Wire params.n .root)
    (h : ∀ a ∈ st.votes.filterMap liftHead?, P (ofHead params a))
    (ho : ∀ a, liftHead? o = some a → P (ofHead params a)) :
    ∀ a ∈ (GridCO.admitVote params.toParams.engine st o).votes.filterMap liftHead?,
      P (ofHead params a) := by
  unfold GridCO.admitVote
  split
  · dsimp only
    split
    · exact h
    · intro a ha
      obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
      rcases List.mem_append.mp hw with hw | hw
      · exact h a (List.mem_filterMap.mpr ⟨w, hw, he⟩)
      · exact ho a (List.mem_singleton.mp hw ▸ he)
  · exact h

/-- Lifting an admitted base HEAD recovers its composite wire. -/
theorem adv_lift_baseVote (a h : HeadWire params.n) (he : liftHead? (baseVote a) = some h) :
    a = h := by
  obtain ⟨auth, b⟩ := a
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
    simp [baseVote, baseHead, HeadWire.decode?, GridCO.fromHead, liftHead?,
      GridCO.headLabel?, GridCO.headSeat?, GridCO.headTarget?] at he
  exact he

theorem adv_gen_known_base_proposal (P : Obj params → Prop) (st : GridCO.State params.n .root)
    (s : Slot) (b : Block) (raw sup : List (HeadWire params.n))
    (h : ∀ a ∈ st.votes.filterMap liftHead?, P (ofHead params a))
    (hr : ∀ a ∈ raw, P (ofHead params a)) :
    ∀ a ∈ (GridCO.admitProposal params.toParams.engine st (baseProposal s b raw sup)
      b (raw.map baseHead)).votes.filterMap liftHead?, P (ofHead params a) := by
  have hf (xs : List (HeadWire params.n)) (st : GridCO.State params.n .root)
      (hs : ∀ a ∈ st.votes.filterMap liftHead?, P (ofHead params a))
      (hx : ∀ a ∈ xs, P (ofHead params a)) :
      ∀ a ∈ ((xs.map baseHead).foldl (fun acc row =>
        GridCO.admitVote params.toParams.engine acc (GridCO.fromHead row)) st).votes.filterMap
          liftHead?, P (ofHead params a) := by
    induction xs generalizing st with
    | nil => exact hs
    | cons a xs ih =>
      apply ih _ (adv_gen_known_vote P st (baseVote a) hs ?_)
      · exact fun a ha => hx a (List.mem_cons_of_mem _ ha)
      · intro h he
        exact adv_lift_baseVote a h he ▸ hx a (List.mem_cons_self ..)
  unfold GridCO.admitProposal baseProposal
  dsimp only
  split
  · exact h
  · exact hf raw _ h hr

theorem adv_decode_vote (o : Obj params) (s : Slot) (i : Fin params.n) (b : BlockId)
    (h : (toWire params o).decode = some (.vote s i b)) :
    o = ⟨.seat (.base (.head s)) i, .head b⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | prop r => cases payload <;> cases h
    | base l => cases l <;> cases payload <;> cases h; rfl

theorem adv_decode_row (o : Obj params) (i : Fin params.n) (body : RowPayload)
    (h : (toWire params o).decode = some (.row i body)) :
    o = ⟨.seat (.base .fg) i, .row body⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | prop s => cases payload <;> cases h
    | base l => cases l <;> cases payload <;> cases h; rfl

theorem adv_decode_proposal (o : Obj params) (s : Slot) (b : NamedProposal params.n)
    (h : (toWire params o).decode = some (.block s b)) :
    o.payload = .proposal b := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | base l => cases l <;> cases payload <;> cases h
    | prop r => cases payload <;> cases h; rfl

theorem adv_gen_known_reconcile (P : Obj params → Prop) (st : State params.n)
    (h : GenKnown P st) : GenKnown P (reconcile st) := by
  unfold reconcile normalizeS
  dsimp only
  split <;> exact h

/-- Processing preserves signature origin, including signatures inside a proposal. -/
theorem adv_gen_known_process (P : Obj params → Prop) (st : State params.n) (o : Obj params)
    (h : GenKnown P st) (ho : P o)
    (hc : ∀ o', carriesS params o o' → P o') :
    GenKnown P (FGSA.process params st (toWire params o)) := by
  unfold FGSA.process
  cases hd : (toWire params o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b =>
      dsimp only
      obtain rfl := adv_decode_vote o s i b hd
      refine ⟨h.1, h.2.1, ?_⟩
      apply adv_gen_known_vote P st.base _ h.2.2
      intro a he
      have he' : (⟨.seat (.head s) i, b⟩ : HeadWire params.n) = a := Option.some.inj he
      exact he' ▸ ho
    | row i body =>
      dsimp only
      obtain rfl := adv_decode_row o i body hd
      exact adv_gen_known_row P st _ h ho
    | block s b =>
      dsimp only
      have he := adv_decode_proposal o s b hd
      have hr : ∀ a ∈ b.rows, P (ofRow params a) := by
        intro a ha
        apply hc
        simp only [carriesS, he]
        exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
      have hv : ∀ a ∈ b.raw, P (ofHead params a) := by
        intro a ha
        apply hc
        simp only [carriesS, he]
        exact Or.inl (List.mem_map.mpr ⟨a, ha, rfl⟩)
      unfold admitBlock
      split
      · exact h
      · split
        · exact h
        · rename_i parent hparent
          split
          · apply adv_gen_known_rows _ _ _ _ hr
            have hs : GenKnown P
                { st with
                  base := GridCO.admitProposal params.toParams.engine st.base
                    (baseProposal s b.erase b.raw b.support) b.erase (b.raw.map baseHead)
                  fg := Window.on_block params params.K_W st.fg (fgBlock parent b.erase b.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal b⟩] } := by
              refine ⟨h.1, ?_,
                adv_gen_known_base_proposal P st.base s b.erase b.raw b.support h.2.2 hv⟩
              intro w hw s' b' hd' a ha
              rcases List.mem_append.mp hw with hw | hw
              · exact h.2.1 w hw s' b' hd' a ha
              · have he := List.mem_singleton.mp hw
                subst w
                cases hd'
                exact hr a ha
            split
            · exact hs
            · exact adv_gen_known_reconcile P _ hs
          · exact h

/-- A proposal takes every carried signature from the stored state. -/
theorem adv_gen_tick_children_known (P : Obj params → Prop) (st : Node params)
    (v : Validator) (t : Time) (o : Obj params) (h : GenKnown P st.st)
    (ho : o ∈ (V2.D.tick env (runData 0 []) st v t).2) :
    ∀ o', carriesS params o o' → P o' := by
  have hs := adv_gen_known_clock P st.st t h
  obtain ⟨l, i, m, rfl, _, ha⟩ := adv_gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have hm : .head (headVote params (FGSA.clock params st.st t) s).root = m := Option.some.inj ha
    subst m
    exact fun _ h => h.elim
  | fgAction r =>
    change (attest params (FGSA.clock params st.st t) st.record
      ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact fun _ h => h.elim
  | propAction s =>
    have ha := joined_body ha
    change (propose params (FGSA.clock params st.st t) s).map
        (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      have hv (a : HeadWire params.n)
          (hm : a ∈ (proposerVotes (FGSA.clock params st.st t) s).filterMap liftHead?) :
          P (ofHead params a) := by
        obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp hm
        exact hs.2.2 a (List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩)
      intro o' hc
      rcases hc with hm | hm | hm
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        exact hv a ha
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
        exact hv a (List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        exact adv_gen_proposalRows_origin _ _ _ hs.1 hs.2.1 a ha

/-- Ticks preserve known signatures and select only known children. -/
theorem adv_gen_tick_fold_known (P : Obj params → Prop) (t : Time) (vs : List Validator)
    (w : World) (os : List (Obj params)) (hw : ∀ v, GenKnown P (w v).st)
    (ho : ∀ o ∈ os, ∀ o', carriesS params o o' → P o') :
    let result := vs.foldl (fun acc v =>
      let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)
    (∀ v, GenKnown P (result.1 v).st) ∧
      ∀ o ∈ result.2, ∀ o', carriesS params o o' → P o' := by
  induction vs generalizing w os with
  | nil => exact ⟨hw, ho⟩
  | cons v vs ih =>
    apply ih
    · intro u
      by_cases he : u = v
      · subst u
        rw [Function.update_self]
        exact (adv_tick_st (w v) v t).symm ▸ adv_gen_known_clock P (w v).st t (hw v)
      · rw [Function.update_of_ne he]
        exact hw u
    · intro o hm o' hc
      rcases List.mem_append.mp hm with hm | hm
      · exact ho o hm o' hc
      · exact adv_gen_tick_children_known P (w v) v t o (hw v) hm o' hc

theorem adv_gen_delivery_fold_known (P : Obj params → Prop) (t : Time)
    (xs : List (Validator × Obj params)) (acc : World × List Event)
    (hw : ∀ v, GenKnown P (acc.1 v).st)
    (ho : ∀ vo ∈ xs, P vo.2 ∧ ∀ o', carriesS params vo.2 o' → P o') :
    ∀ v, GenKnown P ((xs.foldl (deliverOne t) acc).1 v).st := by
  induction xs generalizing acc with
  | nil => exact hw
  | cons vo xs ih =>
    apply ih
    · unfold deliverOne
      split
      · exact hw
      · intro v
        dsimp only
        by_cases hv : v = vo.1
        · subst v
          simp only [V2.D.World.step, Function.update_self]
          exact adv_gen_known_process P _ vo.2 (hw vo.1)
            (ho vo (List.mem_cons_self ..)).1 (ho vo (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hv] using hw v
    · exact fun vo hv => ho vo (List.mem_cons_of_mem _ hv)

/-- A batch preserves known signatures when every offer and its children are known. -/
theorem adv_gen_timeBatch_known (P : Obj params → Prop) (n : Nat) (w : World)
    (held : List (Obj params)) (hheld : ∀ o ∈ held, isProp o = false)
    (hw : ∀ v, GenKnown P (w v).st) (ho : ∀ o ∈ offers n held (tickBatch n w).2, P o) :
    ∀ v, GenKnown P ((timeBatch n w held).1 v).st := by
  obtain ⟨ht, hc⟩ := adv_gen_tick_fold_known P n nodes w [] hw (by simp)
  apply adv_gen_delivery_fold_known P n _ _ ht
  intro vo hv
  obtain ⟨o, hm, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hv
  subst vo
  refine ⟨ho o hm, fun o' hcarry => ?_⟩
  rcases (mem_offers n held _ o).1 hm with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
  · exact hc o hr o' hcarry
  · exact (carries_nonprop (hheld o hr) hcarry).elim
  · exact hc o hr o' hcarry

/-- A signature has an emission in the given trace at or before the bound. -/
def GenPast (es : List Event) (t : Time) (o : Obj params) : Prop :=
  ∃ v s, s ≤ t ∧ GenEmits V2.D.World.init es v o s

/-- Every carried signature has an emission no later than its delivery. -/
def GenCarried (es : List Event) : Prop :=
  ∀ v o t, V2.Event.deliver v o t ∈ es →
    ∀ o', carriesS params o o' → GenPast es t o'

theorem adv_gen_past_append (es ds : List Event) (t : Time) (o : Obj params)
    (h : GenPast es t o) : GenPast (es ++ ds) t o := by
  obtain ⟨v, s, ht, he⟩ := h
  exact ⟨v, s, ht, adv_genEmits_append_left _ es ds v o s he⟩

theorem adv_gen_past_bound (es : List Event) (t u : Time) (o : Obj params)
    (h : GenPast es t o) (htu : t ≤ u) : GenPast es u o := by
  obtain ⟨v, s, ht, he⟩ := h
  exact ⟨v, s, ht.trans htu, he⟩

/-- Symbolic signature-origin induction for the entire generator. -/
theorem adv_gen_prefix_carried (steps : Nat) :
    (∀ v, GenKnown (GenPast (buildPrefix steps).events steps)
      ((buildPrefix steps).world v).st) ∧
      GenCarried (buildPrefix steps).events := by
  induction steps with
  | zero =>
    exact ⟨fun v => gen_known_init _ v, fun v o t hm => (List.not_mem_nil hm).elim⟩
  | succ steps ih =>
    obtain ⟨hw, hc⟩ := ih
    let es := (buildPrefix steps).events
    let w := (buildPrefix steps).world
    let held := (buildPrefix steps).held
    have hevents : (buildPrefix (steps + 1)).events = es ++ (timeBatch steps w held).2 := rfl
    have hp (o : Obj params) (ho : GenPast es steps o) :
        GenPast (buildPrefix (steps + 1)).events ((steps + 1 : Nat) : Time) o := by
      rw [hevents]
      apply adv_gen_past_bound _ steps _ o (adv_gen_past_append es _ steps o ho)
      push_cast
      simp only [Time]
      omega
    have hrel (o : Obj params) (ho : o ∈ (tickBatch steps w).2) :
        GenPast (buildPrefix (steps + 1)).events ((steps + 1 : Nat) : Time) o := by
      obtain ⟨u, hu⟩ := batch_release_emits steps o ho
      refine ⟨u, steps, ?_, hu⟩
      push_cast
      simp only [Time]
      omega
    constructor
    · rw [bp_world]
      apply adv_gen_timeBatch_known _ steps w held (held_nonprop steps)
      · exact fun v => adv_gen_known_mono _ _ _ (hw v) hp
      · intro o ho
        rcases (mem_offers steps held _ o).1 ho with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
        · exact hrel o hr
        · obtain ⟨_, u, s, hs, hu⟩ := (adv_prefix_origin steps).2 o hr
          exact hp o ⟨u, s, le_of_lt hs, hu⟩
        · exact hrel o hr
    · intro v o s hm o' hcarry
      rw [hevents] at hm
      rcases List.mem_append.mp hm with hm | hm
      · rw [hevents]
        exact adv_gen_past_append es _ s o' (hc v o s hm o' hcarry)
      · obtain ⟨rfl, _, hoff⟩ := timeBatch_delivered steps w held v o s hm
        have hk := (adv_gen_tick_fold_known (GenPast es steps) steps nodes w [] hw (by simp)).2
        rcases (mem_offers steps held _ o).1 hoff with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
        · rw [hevents]; exact adv_gen_past_append es _ _ o' (hk o hr o' hcarry)
        · exact (carries_nonprop (held_nonprop steps o hr) hcarry).elim
        · rw [hevents]; exact adv_gen_past_append es _ _ o' (hk o hr o' hcarry)

/-- A carried-signature witness identifies the holder of its earlier emission. -/
theorem adv_genCarried_runData (h : Time) (es : List Event) (hc : GenCarried es)
    (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes (runData h es) v o t)
    (o' : Obj params) (hcarry : (fgsa params unitCodec).carries o o') (u : Validator)
    (hh : V2.D.Run.holder (runData h es) o'.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits env (runData h es) u o' t' := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨x, s, ht, he⟩ := hc v o t (List.mem_of_getElem? hi) o' hcarry
  have hem := adv_genEmits_runData h es x o' s he
  obtain ⟨pre, post, _, ho⟩ := he
  have hh' := adv_gen_tick_holder (genFold V2.D.World.init pre x) x s o' ho
  have hu : u = x := Option.some.inj (hh.symm.trans hh')
  exact ⟨s, ht, hu.symm ▸ hem⟩

theorem run_signatures : V2.D.UnforgeableSignatures env run where
  unforgeable v o t hp u _ hh :=
    adv_genOrigin_unforgeable horizon _ (adv_prefix_origin 301).1 v o t hp u hh
  carried v o t hp o' hc u _ hh :=
    adv_genCarried_runData horizon _ (adv_gen_prefix_carried 301).2 v o t hp o' hc u hh



/-! ### Wire checks (copied from W1) -/

section Wire
variable {p : Params}

theorem adv_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, b, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s b hd a hm

theorem adv_proposal_votes (st : State p.n) (s : Slot) :
    (∀ a ∈ (proposerVotes st s).filterMap liftHead?,
      ∃ j b, a.decode? = some (s - 1, j, b)) ∧
    (∀ a ∈ (proposerSupport st s).filterMap liftHead?,
      a ∈ (proposerVotes st s).filterMap liftHead?) := by
  constructor
  · intro a ha
    obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp ha
    have ht : GridCO.headLabel? w = some (s - 1) :=
      beq_iff_eq.mp (List.mem_filter.mp hw).2
    change (GridCO.headLabel? w >>= fun r => GridCO.headSeat? w >>= fun j =>
      GridCO.headTarget? w >>= fun b => some ⟨.seat (.head r) j, b⟩) = some a at hl
    rw [ht] at hl
    obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
    have her := Option.some.inj hr
    subst r
    obtain ⟨j, _, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨b, _, he⟩ := Option.bind_eq_some_iff.mp hl
    cases he
    exact ⟨j, b, rfl⟩
  · intro a ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
    exact List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩

theorem adv_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp p a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  let raw := (proposerVotes st s).filterMap liftHead?
  let sup := (proposerSupport st s).filterMap liftHead?
  unfold propose at hm
  rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
  simp only [Option.map_map] at hm
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm
  have heP : P.erase = H := (namedByErase?_sound st H P hP).2
  change FGSA.wellFormed p ⟨.proposer s, .proposal (namedProposal p P s a raw sup rows)⟩ = true
  simp only [FGSA.wellFormed, Wire.decode]
  rw [namedProposal_erase, heP]
  simp only [namedProposal, NamedProposal.raw, NamedProposal.support, NamedProposal.rows]
  change (true && (s == s) && decide (H.slot < s) &&
    raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    sup.all (fun v => decide (v ∈ raw)) && rows.all RowWire.valid &&
    contentOk p (proposalBlock p H s a raw sup rows) raw sup rows) = true
  obtain ⟨hraw, hsup⟩ := adv_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (adv_proposal_rows st H hv)
  have hvotes : ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) = true := by
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨j, b, hd⟩ := hraw v hv
    rw [hd]
    exact beq_iff_eq.mpr (Nat.sub_add_cancel hs0)
  have hsupport : ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hsup v hv))
  have hc := contentOk_proposalBlock p H s a raw sup rows
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp

end Wire

theorem adv_gen_nonproposal_deps (st : Node params) (o : Obj params)
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa params unitCodec).depsPresent st o = true := by
  obtain ⟨auth, payload⟩ := o
  cases payload with
  | proposal b => exact (hn b rfl).elim
  | head b =>
      rcases auth with ⟨((_ | _) | _), _⟩ | _ <;>
        rfl
  | row a =>
      rcases auth with ⟨((_ | _) | _), _⟩ | _ <;>
        rfl

/-- The active height view starts at a positive height. -/
theorem adv_gen_derive_positive (B : FGBlock (Fin params.n)) :
    1 ≤ (heightView params B).h :=
  (Window.windowHeightLaws params params.K_W params.kWLarge).one_le_h B

/-- Every released row passes the row-body wire check. -/
theorem adv_gen_attest_valid (st : State params.n) (record : RecordOnce)
    (i : Fin params.n) (body : RowPayload)
    (hbody : (attest params st record i).1 = some body) : body.valid = true := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp hbody
  obtain ⟨h, T, timeout, hh, he, _, _, _⟩ :=
    KitFG.createRowOnce_released params.E params.cfg record i
      (fgInputs params st).1 (fgInputs params st).2 ha
  have hf := KitFG.height_pair_vote_fields hh
  obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
  have heh : (heightView params C).h = h := by
    rw [heightView_bridge]
    exact congrArg Prod.fst hc
  have hpos : 1 ≤ h := heh ▸ adv_gen_derive_positive C
  rw [← hp, he]
  change (decide (1 ≤ h) &&
    ((finality_pair record.toRecord (fgInputs params st).2).filter
      (fun fp => decide (fp.height < h)) |>.map (fun fp => decide (fp.height < h))).getD true)
        = true
  cases hfp : finality_pair record.toRecord (fgInputs params st).2 with
  | none => simp [hpos, Option.filter]
  | some fp =>
      by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]

/-- The wire check for non-proposal releases. -/
theorem adv_gen_tick_nonproposal_wire (st : Node params) (v : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) st v t).2)
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨l, i, m, rfl, _, ha⟩ := adv_gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
      have ha := joined_body ha
      have he : .head (headVote params (FGSA.clock params st.st t) s).root = m := Option.some.inj ha
      subst m
      rfl
  | fgAction r =>
      change (attest params (FGSA.clock params st.st t) st.record
        ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      exact adv_gen_attest_valid _ _ _ _ hb
  | propAction s =>
      have ha := joined_body ha
      change (propose params (FGSA.clock params st.st t) s).map
        (withApp params 0) = some m at ha
      unfold propose at ha
      split at ha
      · cases ha
      · simp only [Option.map_map] at ha
        obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.mp ha
        exact (hn _ rfl).elim

/-- A row with a generated emission passes the row wire check. -/
theorem adv_gen_past_row_valid (es : List Event) (t : Time) (a : RowWire params.n)
    (h : GenPast es t (ofRow params a)) : a.valid = true := by
  obtain ⟨v, s, _, pre, post, _, ho⟩ := h
  have hw := adv_gen_tick_nonproposal_wire (genFold V2.D.World.init pre v) v s (ofRow params a) ho
    (by intro b; cases a with | mk auth body => cases auth <;> simp [ofRow,
      ofWire])
  obtain ⟨auth, body⟩ := a
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
    simp [fgsa, FGSA.wellFormed, toWire, toAuth, ofRow, ofWire, ofAuth, Wire.decode,
      RowWire.valid, RowWire.decode?] at hw ⊢
  exact hw

/-- A list fold preserves knowledge when each delivery and its children have it. -/
theorem adv_known_fold (P : Obj params → Prop) (w : World) (es : List Event)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es)
    (hw : ∀ v, GenKnown P (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P o ∧ ∀ o', carriesS params o o' → P o') :
    ∀ v, GenKnown P (genFold w es v).st := by
  induction es generalizing w with
  | nil => exact hw
  | cons e es ih =>
    apply ih (hnr := fun v t h => hnr v t (List.mem_cons_of_mem _ h))
    · intro u
      cases e with
      | restart v t => exact (hnr v t (List.mem_cons_self ..)).elim
      | tick v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact (adv_tick_st (w v) v t).symm ▸ adv_gen_known_clock P _ t (hw v)
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
      | deliver v o t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact adv_gen_known_process P _ o (hw v)
            (he v o t (List.mem_cons_self ..)).1
            (he v o t (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
    · intro v o t hm
      exact he v o t (List.mem_cons_of_mem _ hm)

/-- Row validity at every event prefix, without delivery validity. -/
theorem adv_rows_at_index (h : Time) (es : List Event)
    (ho : GenOrigin V2.D.World.init es) (hc : GenCarried es)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es) (i : Nat) (v : Validator) :
    EmissionRowsValid (V2.D.Run.stateBefore env (runData h es) i v).st := by
  let P := fun o => ∃ t, GenPast es t o
  have hk : GenKnown P (genFold V2.D.World.init (es.take i) v).st := by
    apply adv_known_fold (hnr := fun u t h => hnr u t (List.mem_of_mem_take h))
    · intro u
      exact gen_known_init P u
    · intro u o t hm
      have hm' := List.mem_of_mem_take hm
      obtain ⟨x, s, hs, hx⟩ := ho u o t hm'
      exact ⟨⟨t, x, s, hs, hx⟩, fun o' hcarry => ⟨t, hc u o t hm' o' hcarry⟩⟩
  rw [adv_runData_stateBefore]
  exact ⟨fun a ha => by
      obtain ⟨t, ht⟩ := hk.1 a ha
      exact adv_gen_past_row_valid es t a ht,
    fun w hw s b hd a ha => by
      obtain ⟨t, ht⟩ := hk.2.1 w hw s b hd a ha
      exact adv_gen_past_row_valid es t a ht⟩

/-- Every release passes the wire check, using the symbolic row invariant. -/
theorem adv_emit_wire (h : Time) (es : List Event)
    (hs : V2.D.ScheduleWellFormed env (runData h es))
    (horigin : GenOrigin V2.D.World.init es) (hcarried : GenCarried es)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es)
    (v : Validator) (o : Obj params) (t : Time)
    (hem : V2.D.Run.emits env (runData h es) v o t) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨i, hi, ho⟩ := hem
  rw [(V2.D.Run.step_tick_eq env (runData h es) hi).2] at ho
  obtain ⟨l, j, m, rfl, hl, ha⟩ := adv_gen_tick_seat
    (V2.D.Run.stateBefore env (runData h es) i v) v t o ho
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have he : .head (headVote params
        (FGSA.clock params (V2.D.Run.stateBefore env (runData h es) i v).st t) s).root = m :=
      Option.some.inj ha
    subst m
    rfl
  | fgAction r =>
    change (attest params (FGSA.clock params (V2.D.Run.stateBefore env (runData h es) i v).st t)
      (V2.D.Run.stateBefore env (runData h es) i v).record ⟨0, params.nPos⟩).1.map Msg.row
        = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact adv_gen_attest_valid _ _ _ _ hb
  | propAction s =>
    have ha := joined_body ha
    have ht : SA.proposalTime params.toParams s = t :=
      ((fgsa params unitCodec).duties_spec (.propAction s) t).1 hl
    subst t
    have hm : (propose params
        (FGSA.clock params (V2.D.Run.stateBefore env (runData h es) i v).st
          (SA.proposalTime params.toParams s)) s).map (withApp params 0) = some m := ha
    have hs0 : 0 < s := by
      by_contra hn
      have he : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      change none = some m at hm
      cases hm
    have hv := adv_rows_at_index h es horigin hcarried hnr i v
    have hv' : EmissionRowsValid
        (FGSA.clock params (V2.D.Run.stateBefore env (runData h es) i v).st
          (SA.proposalTime params.toParams s)) := by
      simpa only [EmissionRowsValid, adv_clock_rowPool, adv_clock_proposals] using hv
    exact adv_proposal_wf _ s 0 hv'
      (fgsa_propose_parent_lt env (runData h es) hs hi hs0) hm

/-- Every delivery of the run passes the wire check. -/
theorem run_wire (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : run.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨u, s, _, hu⟩ := (adv_prefix_origin 301).1 v o t (List.mem_of_getElem? hi)
  exact adv_emit_wire 300 _ (prefix_schedule 300) (adv_prefix_origin 301).1
    (adv_gen_prefix_carried 301).2 (adv_prefix_no_restart 301) u o s
    (adv_genEmits_runData 300 _ u o s hu)

/-! ### Dependencies -/

/-- A skipped offer has exactly the store effect of the real handler. -/
theorem adv_process_inert (st : State params.n) (o : Obj params)
    (hp : processedS params st o = true) :
    FGSA.process params st (toWire params o) = st := by
  unfold processedS at hp
  unfold FGSA.process
  cases hd : (toWire params o).decode with
  | none => rw [hd] at hp
  | some m =>
    rw [hd] at hp
    cases m with
    | vote s i b =>
      have hm := of_decide_eq_true hp
      change (⟨.seat s i, .head b⟩ : GridCO.Wire params.n .root) ∈ st.base.votes at hm
      simp [admitHead, GridCO.admitVote, hm]
    | row i body =>
      have hm := of_decide_eq_true hp
      obtain rfl := adv_decode_row o i body hd
      exact adv_admitRow_duplicate st i body hm
    | block s b =>
      have hm := of_decide_eq_true hp
      apply admitBlock_refused
      cases hP : parentFG st b.erase with
      | none => exact Or.inr (Or.inl rfl)
      | some P => exact Or.inr (Or.inr ⟨P, rfl, by simp [blockAccepted, hm]⟩)

/-- The store update does not depend on whether the offer was skipped. -/
theorem adv_deliver_st (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) :
    ((deliverOne t acc vo).1 u).st =
      if u = vo.1 then FGSA.process params (acc.1 u).st (toWire params vo.2)
      else (acc.1 u).st := by
  unfold deliverOne
  split
  · rename_i hp
    by_cases hu : u = vo.1
    · subst u
      rw [ite_eq_left rfl, adv_process_inert _ _ hp]
    · rw [ite_eq_right hu]
  · dsimp only
    by_cases hu : u = vo.1
    · subst u
      simp only [V2.D.World.step, Function.update_self]
      rfl
    · simp only [V2.D.World.step, Function.update_of_ne hu, ite_eq_right hu]

/-- Each node receives one store update for one offered object. -/
theorem adv_offer_st (t : Time) (acc : World × List Event) (o : Obj params)
    (vs : List Validator) (hn : vs.Nodup) (u : Validator) :
    (((vs.map (fun v => (v, o))).foldl (deliverOne t) acc).1 u).st =
      if u ∈ vs then FGSA.process params (acc.1 u).st (toWire params o)
      else (acc.1 u).st := by
  induction vs generalizing acc with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.foldl_cons, ih _ hn.of_cons, adv_deliver_st]
    by_cases huv : u = v
    · subst u
      simp only [List.mem_cons, true_or, ↓reduceIte, hn.notMem]
    · by_cases hu : u ∈ vs <;> simp [huv, hu]

/-- The tick fold clocks each ticking node once. -/
theorem tick_fold_st (t : Time) (vs : List Validator) (hn : vs.Nodup)
    (w : World) (os : List (Obj params)) (u : Validator) :
    ((vs.foldl (fun acc v =>
      let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).1 u).st =
      if u ∈ vs then FGSA.clock params (w u).st t else (w u).st := by
  induction vs generalizing w os with
  | nil => simp
  | cons v vs ih =>
    refine (ih hn.of_cons _ _).trans ?_
    dsimp only
    by_cases huv : u = v
    · subst u
      simp only [List.mem_cons, true_or, ↓reduceIte, hn.notMem, Function.update_self]
      exact adv_tick_st (w v) v t
    · simp only [Function.update_of_ne huv, List.mem_cons, huv, false_or]

/-- The tick fold releases exactly the objects of its independent ticks. -/
theorem tick_fold_emits (t : Time) (vs : List Validator) (hn : vs.Nodup)
    (w : World) (os : List (Obj params)) (o : Obj params) :
    o ∈ (vs.foldl (fun acc v =>
      let result := V2.D.tick env (runData 0 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2 ↔
      o ∈ os ∨ ∃ v ∈ vs, o ∈ (V2.D.tick env (runData 0 []) (w v) v t).2 := by
  induction vs generalizing w os with
  | nil =>
    exact ⟨fun h => Or.inl h, fun h => h.elim id (fun ⟨_, h, _⟩ => by simp at h)⟩
  | cons v vs ih =>
    refine (ih hn.of_cons _ _).trans ?_
    dsimp only
    have hw : ∀ u ∈ vs, Function.update w v (V2.D.tick env (runData 0 []) (w v) v t).1 u
        = w u := by
      intro u hu
      exact Function.update_of_ne (by rintro rfl; exact hn.notMem hu) _ _
    constructor
    · rintro (hm | ⟨u, hu, hm⟩)
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr ⟨v, List.mem_cons_self .., hm⟩
      · rw [hw u hu] at hm
        exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hm⟩
    · rintro (hm | ⟨u, hu, hm⟩)
      · exact Or.inl (List.mem_append_left _ hm)
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact Or.inl (List.mem_append_right _ hm)
        · rw [← hw u hu] at hm
          exact Or.inr ⟨u, hu, hm⟩

theorem tickBatch_st (t : Time) (w : World) (u : Validator) :
    ((tickBatch t w).1 u).st =
      if u ∈ nodes then FGSA.clock params (w u).st t else (w u).st :=
  tick_fold_st t nodes (by decide) w [] u

theorem tickBatch_emits (t : Time) (w : World) (o : Obj params) :
    o ∈ (tickBatch t w).2 ↔
      ∃ v ∈ nodes, o ∈ (V2.D.tick env (runData 0 []) (w v) v t).2 := by
  refine (tick_fold_emits t nodes (by decide) w [] o).trans ?_
  simp

/-- All honest node stores agree; own-signature records can differ. -/
def GenUniformStores (w : World) : Prop := ∀ u ∈ nodes, ∀ v ∈ nodes, (w u).st = (w v).st

/-- One object preserves store agreement after its complete recipient list. -/
theorem adv_offer_uniform (t : Time) (acc : World × List Event) (o : Obj params)
    (hw : GenUniformStores acc.1) :
    GenUniformStores ((nodes.map (fun v => (v, o))).foldl (deliverOne t) acc).1 := by
  intro u hu v hv
  rw [adv_offer_st t acc o nodes (by decide), adv_offer_st t acc o nodes (by decide),
    ite_eq_left hu, ite_eq_left hv, hw u hu v hv]

/-- The object fold preserves store agreement without an acceptance premise. -/
theorem adv_objects_uniform (t : Time) (os : List (Obj params))
    (acc : World × List Event) (hw : GenUniformStores acc.1) :
    GenUniformStores ((os.flatMap (fun o => nodes.map (fun v => (v, o)))).foldl
      (deliverOne t) acc).1 := by
  induction os generalizing acc with
  | nil => exact hw
  | cons o os ih =>
    rw [List.flatMap_cons, List.foldl_append]
    exact ih _ (adv_offer_uniform t acc o hw)

/-- Each generated time block preserves store agreement. -/
theorem adv_batch_uniform (n : Nat) (w : World) (held : List (Obj params))
    (hw : GenUniformStores w) : GenUniformStores (timeBatch n w held).1 := by
  apply adv_objects_uniform
  intro u hu v hv
  rw [tickBatch_st, tickBatch_st, ite_eq_left hu, ite_eq_left hv, hw u hu v hv]

theorem prefix_uniform (steps : Nat) : GenUniformStores (buildPrefix steps).world := by
  induction steps with
  | zero => exact fun _ _ _ _ => rfl
  | succ steps ih => rw [bp_world]; exact adv_batch_uniform _ _ _ ih

/-- Every replayed generator store is reachable. -/
theorem adv_reachable (es : List Event) (u : Validator) :
    Reachable params (genFold V2.D.World.init es u).st := by
  have h := reachable_stateBefore env (runData 0 es) es.length u
  rwa [adv_runData_stateBefore, List.take_length] at h

theorem prefix_reachable (steps : Nat) (u : Validator) :
    Reachable params ((buildPrefix steps).world u).st := by
  rw [(adv_prefix_replay_fresh steps).1]
  exact adv_reachable _ u

/-- An emitted proposal has a parent in the emitting store. -/
theorem adv_tick_deps (st : Node params) (v : Validator) (t : Time)
    (hr : Reachable params st.st) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) st v t).2) :
    depsS params (FGSA.clock params st.st t) o = true := by
  obtain ⟨l, j, m, rfl, _, ha⟩ := adv_gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have he : .head (headVote params (FGSA.clock params st.st t) s).root = m := Option.some.inj ha
    subst m
    rfl
  | fgAction r =>
    change (attest params (FGSA.clock params st.st t)
      st.record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    rfl
  | propAction s =>
    have ha := joined_body ha
    change (propose params (FGSA.clock params st.st t) s).map (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp ha
      let pre := FGSA.clock params st.st t
      have hnamed := namedByErase?_sound pre _ P hP
      have hinv := (storeBundle_of_reachable params _ (Reachable.tick t hr)).cstore
      let H := getHead params pre (proposerVotes pre s) (proposerSupport pre s)
      obtain ⟨Q, hQ, he⟩ := (hinv.baseTree H).mp (getHead_stored params _ hinv _ _)
      have hlookup := (fgBlockOf_spec params pre hinv H Q).mpr ⟨hQ, he⟩
      change (decide (P ∈ pre.namedBodies) && (fgBlockOf pre P.erase).isSome) = true
      rw [hnamed.2, hlookup]
      simp only [Option.isSome_some, Bool.and_true, decide_eq_true_eq]
      exact hnamed.1

/-- Store agreement supplies proposal dependencies at every receiver after the ticks. -/
theorem adv_batch_deps_start (t : Time) (w : World) (hw : GenUniformStores w)
    (hr : ∀ v, Reachable params (w v).st) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) (u : Validator) (hu : u ∈ nodes) :
    depsS params ((tickBatch t w).1 u).st o = true := by
  obtain ⟨v, hv, hm⟩ := (tickBatch_emits t w o).1 ho
  rw [tickBatch_st, ite_eq_left hu, hw u hu v hv]
  exact adv_tick_deps _ v t (hr v) o hm

/-- Dependencies persist when the FG store grows. -/
theorem adv_deps_mono {st st' : State params.n} (hT : st.fg.TF ⊆ st'.fg.TF)
    (hN : st.namedBodies ⊆ st'.namedBodies) (o : Obj params) (h : depsS params st o = true) :
    depsS params st' o = true := by
  unfold depsS at h ⊢
  cases hd : (toWire params o).decode with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => rfl
    | row i body => rfl
    | block s b =>
      rw [hd] at h
      obtain ⟨hn, hp⟩ := Bool.and_eq_true_iff.mp h
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true (hN (of_decide_eq_true hn)), ?_⟩
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hp
      exact Option.isSome_iff_exists.mpr ⟨P,
        (parentFG_spec st' b.erase P).2
          ⟨hT ((parentFG_spec st b.erase P).1 hP).1,
            ((parentFG_spec st b.erase P).1 hP).2⟩⟩

/-- Any offered delivery preserves dependencies of every object. -/
theorem adv_deliver_deps (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) (o : Obj params)
    (h : depsS params (acc.1 u).st o = true) :
    depsS params ((deliverOne t acc vo).1 u).st o = true := by
  rw [adv_deliver_st]
  split
  · exact adv_deps_mono (process_cumulative params _ _).1
      (process_namedBodies_subset _ _) o h
  · exact h

/-- Dependency checks at every delivery in a list. -/
def GenDeps : World → List Event → Prop
  | _, [] => True
  | w, e :: es =>
      (match e with
        | .deliver v o _ => depsS params (w v).st o = true
        | _ => True) ∧
      GenDeps (V2.D.World.step env (runData 0 []) w e) es

theorem adv_deps_append (w : World) (es ds : List Event) :
    GenDeps w (es ++ ds) ↔ GenDeps w es ∧ GenDeps (genFold w es) ds := by
  induction es generalizing w with
  | nil => simp [GenDeps, genFold]
  | cons e es ih =>
    simp only [List.cons_append, GenDeps, ih, genFold, List.foldl_cons]
    tauto

/-- The delivery fold keeps the dependency checks in its accumulated trace. -/
theorem adv_delivery_fold_deps (t : Time) (xs : List (Validator × Obj params))
    (w : World) (acc : World × List Event) (hr : genFold w acc.2 = acc.1)
    (hd : GenDeps w acc.2)
    (hx : ∀ vo ∈ xs, depsS params (acc.1 vo.1).st vo.2 = true) :
    GenDeps w (xs.foldl (deliverOne t) acc).2 := by
  induction xs generalizing acc with
  | nil => exact hd
  | cons vo xs ih =>
    rw [List.foldl_cons]
    apply ih
    · unfold deliverOne
      split
      · exact hr
      · simp only [adv_genFold_append, hr]
        rfl
    · unfold deliverOne
      split
      · exact hd
      · apply (adv_deps_append w acc.2 _).2
        exact ⟨hd, by simpa only [GenDeps, hr, and_true] using hx vo (List.mem_cons_self ..)⟩
    · intro vo' hm
      exact adv_deliver_deps t acc vo vo'.1 vo'.2 (hx vo' (List.mem_cons_of_mem _ hm))

theorem adv_ticks_deps (w : World) (t : Time) (vs : List Validator) :
    GenDeps w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih _⟩

/-- Dependencies hold throughout a complete generated time block. -/
theorem adv_batch_deps (n : Nat) (w : World) (held : List (Obj params))
    (hheld : ∀ o ∈ held, isProp o = false) (hw : GenUniformStores w)
    (hr : ∀ v, Reachable params (w v).st) : GenDeps w (timeBatch n w held).2 := by
  apply adv_delivery_fold_deps
  · exact (adv_tickBatch_replay n w).symm
  · exact adv_ticks_deps w n nodes
  · intro vo hm
    obtain ⟨o, ho, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    rcases (mem_offers n held _ o).1 ho with ⟨_, hr', _⟩ | ⟨_, hr' | hr'⟩
    · exact adv_batch_deps_start n w hw hr o hr' v hv
    · exact adv_gen_nonproposal_deps _ o (isProp_false (hheld o hr'))
    · exact adv_batch_deps_start n w hw hr o hr' v hv

theorem prefix_deps (steps : Nat) : GenDeps V2.D.World.init (buildPrefix steps).events := by
  induction steps with
  | zero => trivial
  | succ steps ih =>
    rw [bp_events]
    apply (adv_deps_append _ _ _).2
    refine ⟨ih, ?_⟩
    rw [← (adv_prefix_replay_fresh steps).1]
    exact adv_batch_deps _ _ _ (held_nonprop steps) (prefix_uniform steps)
      (prefix_reachable steps)

/-- Read a dependency check at an indexed delivery. -/
theorem adv_deps_get (w : World) (es : List Event) (hd : GenDeps w es)
    (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : es[i]? = some (.deliver v o t)) :
    depsS params (genFold w (es.take i) v).st o = true := by
  induction es generalizing w i with
  | nil => simp at he
  | cons e es ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst e
      exact hd.1
    | succ i => exact ih _ hd.2 i (by simpa using he)

attribute [irreducible] GenDeps

theorem run_deps (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : run.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore env run i v) o = true := by
  change depsS params (genFold V2.D.World.init (run.events.take i) v).st o = true
  exact adv_deps_get V2.D.World.init _ (prefix_deps 301) i v o t hi

/-- I-EXEC: every execution-validity field holds for the adversarial run. -/
theorem nvExecution : V2.D.ExecutionValid env run where
  tick_awake := by intros; rfl
  deliver_awake := by intros; rfl
  restart_awake := by intros; rfl
  wake_restart := by intro v hv t ht hh hw; cases hw.2
  toScheduleWellFormed := run_schedule
  wire := run_wire
  deps := run_deps
  fresh := run_fresh
  toUnforgeableSignatures := run_signatures



/-! ### Synchrony: acceptance -/

/-- A single-duty signing key has one object in a trace with unique ticks. -/
def GenSingleDutyUnique (P : Obj params → Prop) : Prop :=
  ∀ l j o o', Gen.V2.Duty.SingleDuty (fgsa params unitCodec) l → P o → P o' → o.auth
    = .seat l j → o'.auth = .seat l j → o = o'

/-- Generated emissions satisfy single-duty key uniqueness by replay. -/
theorem emits_unique (es : List Event) (hn : es.Nodup) :
    GenSingleDutyUnique (fun o => ∃ v t, GenEmits V2.D.World.init es v o t) := by
  rintro l j o o' hD ⟨v, t, he⟩ ⟨v', t', he'⟩ ha ha'
  have holder (x : Validator) (u : Time) (a : Obj params)
      (he : GenEmits V2.D.World.init es x a u) (ha : a.auth = .seat l j) :
      x = seatOf l j := by
    obtain ⟨pre, post, _, hm⟩ := he
    have hh := adv_gen_tick_holder (genFold V2.D.World.init pre x) x u a hm
    rw [ha] at hh
    exact (Option.some.inj hh).symm
  have hv := holder v t o he ha
  have hv' := holder v' t' o' he' ha'
  obtain ⟨i, hi, ho⟩ := adv_genEmits_runData 0 es v o t he
  obtain ⟨i', hi', ho'⟩ := adv_genEmits_runData 0 es v' o' t' he'
  rw [hv] at hi
  rw [hv'] at hi'
  exact (Gen.V2.Duty.emitted_unique_of_singleDuty env (runData 0 es) hn
    l hD j (seatOf l j) i i' t t' o o' hi hi' ho ho' ha ha').2

/-- An honest HEAD for slot `s` is accepted in a store at slot `s` or `s + 1`. -/
theorem head_accept (P : Obj params → Prop) (hu : GenSingleDutyUnique P)
    (st : State params.n) (hk : GenKnown P st) (s : Slot) (i : Fin params.n) (b : BlockId)
    (ho : P (ofHead params ⟨.seat (.head s) i, b⟩))
    (hs1 : s ≤ st.slot params) (hs2 : st.slot params ≤ s + 1) :
    processedS params (FGSA.process params st
      (toWire params (ofHead params ⟨.seat (.head s) i, b⟩)))
      (ofHead params ⟨.seat (.head s) i, b⟩) = true := by
  let a : HeadWire params.n := ⟨.seat (.head s) i, b⟩
  by_cases hm : baseVote a ∈ st.base.votes
  · have hp : processedS params st (ofHead params a) = true := decide_eq_true hm
    rw [adv_process_inert st _ hp]
    exact hp
  · have hempty : GridCO.seatVotes (GridCO.votesAt st.base s) i = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw hseat
      obtain ⟨hw, hlabel⟩ := List.mem_filter.mp hw
      have hl : GridCO.headLabel? w = some s := beq_iff_eq.mp hlabel
      have hi : GridCO.headSeat? w = some i := beq_iff_eq.mp hseat
      obtain ⟨auth, msg⟩ := w
      cases auth with
      | none => cases msg <;> cases hl
      | proposer r => cases msg <;> cases hl
      | seat r j =>
        cases msg with
        | proposal q raw sup => cases hl
        | head b' =>
          cases hl
          cases hi
          have hp : P (ofHead params ⟨.seat (.head s) i, b'⟩) :=
            hk.2.2 _ (List.mem_filterMap.mpr ⟨_, hw, rfl⟩)
          have he := hu (.base (.head s)) i _ _ (fgsa_head_singleDuty s) hp ho rfl rfl
          have hb : b' = b := Msg.head.inj (congrArg V2.Signed.payload he)
          subst b'
          exact hm hw
    have hx : GridCO.equivocates (GridCO.votesAt st.base s) i = false := by
      simp [GridCO.equivocates, hempty]
    have h1 : ¬ s < (st.base.now / (4 * params.toParams.engine.Δ)).toNat - 1 := by
      change ¬ s < st.slot params - 1; simp only [Slot] at *; omega
    have h2 : ¬ (st.base.now / (4 * params.toParams.engine.Δ)).toNat < s := by
      change ¬ st.slot params < s; simp only [Slot] at *; omega
    change decide (baseVote a ∈ (admitHead params st s i b).base.votes) = true
    apply decide_eq_true
    change (⟨.seat s i, .head b⟩ : GridCO.Wire params.n .root) ∈ _
    change (⟨.seat s i, .head b⟩ : GridCO.Wire params.n .root) ∉ st.base.votes at hm
    simp [admitHead, GridCO.admitVote, hm, hx, h1, h2]

/-- A decoded full row is accepted without a round or key-count condition. -/
theorem row_accept (st : State params.n) (i : Fin params.n) (body : RowPayload) :
    processedS params (FGSA.process params st
      (toWire params (ofRow params ⟨.seat .fg i, body⟩)))
      (ofRow params ⟨.seat .fg i, body⟩) = true := by
  change decide ((⟨.seat .fg i, body⟩ : RowWire params.n) ∈
    (admitRow params st ⟨.seat .fg i, body⟩).rowPool) = true
  unfold admitRow
  dsimp only [RowWire.decode?]
  split <;> simp_all

/-- A non-proposal is accepted at its emission time, or at GST when it is held. -/
theorem nonproposal_accept (P : Obj params → Prop) (hu : GenSingleDutyUnique P)
    (nd : Node params) (v : Validator) (t td : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) nd v t).2)
    (hP : P o) (hnot : ∀ b, o.payload ≠ .proposal b) (hwin : t ≤ td ∧ (td = t ∨ td ≤ 7))
    (st : State params.n) (hk : GenKnown P st) (hn : st.base.now = td) :
    processedS params (FGSA.process params st (toWire params o)) o = true := by
  obtain ⟨l, j, m, rfl, hl, ha⟩ := adv_gen_tick_seat nd v t o ho
  have ht := ((fgsa params unitCodec).duties_spec l t).1 hl
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have he : .head (headVote params (FGSA.clock params nd.st t) s).root = m := Option.some.inj ha
    subst m
    change (4 : Int) * s + 1 = t at ht
    have hslot : st.slot params = (td / 4).toNat := by
      change (st.base.now / (4 * params.toParams.engine.Δ)).toNat = _
      rw [hn]
      rfl
    apply head_accept P hu st hk s j _ hP <;> rw [hslot] <;> simp only [Slot, Time] at * <;> omega
  | fgAction r =>
    change (attest params (FGSA.clock params nd.st t) nd.record
        ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact row_accept st j body
  | propAction s =>
    have ha := joined_body ha
    change (propose params (FGSA.clock params nd.st t) s).map (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      exact (hnot _ rfl).elim

/-- Processed objects stay processed when their pools and tree grow. -/
theorem adv_processed_mono {st st' : State params.n}
    (hv : st.base.votes ⊆ st'.base.votes) (hr : st.rowPool ⊆ st'.rowPool)
    (hT : st.fg.TF ⊆ st'.fg.TF) (o : Obj params) :
    processedS params st o = true → processedS params st' o = true := by
  dsimp only [processedS]
  cases (toWire params o).decode with
  | none => exact id
  | some m =>
    cases m with
    | vote s i b => simpa only [decide_eq_true_eq] using (fun h => hv h)
    | row i body => simpa only [decide_eq_true_eq] using (fun h => hr h)
    | block s b =>
      simp only [decide_eq_true_eq]
      rintro ⟨Y, hY, he⟩
      exact ⟨Y, hT hY, he⟩

/-- A handler call preserves every previously processed object. -/
theorem process_processed (st : State params.n) (a o : Obj params)
    (h : processedS params st o = true) :
    processedS params (FGSA.process params st (toWire params a)) o = true := by
  have hc := process_cumulative params st (toWire params a)
  exact adv_processed_mono (process_votes_subset st (toWire params a))
    hc.2.2.2.2.2.subset hc.1 o h

theorem deliver_processed (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) (o : Obj params)
    (h : processedS params (acc.1 u).st o = true) :
    processedS params ((deliverOne t acc vo).1 u).st o = true := by
  rw [adv_deliver_st]
  split
  · exact process_processed _ _ _ h
  · exact h

theorem fold_processed (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (u : Validator) (o : Obj params)
    (h : processedS params (acc.1 u).st o = true) :
    processedS params ((xs.foldl (deliverOne t) acc).1 u).st o = true := by
  induction xs generalizing acc with
  | nil => exact h
  | cons vo xs ih => exact ih _ (deliver_processed t acc vo u o h)

/-- Delivery does not change a receiver's clock. -/
theorem deliver_now (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) :
    ((deliverOne t acc vo).1 u).st.base.now = (acc.1 u).st.base.now := by
  rw [adv_deliver_st]
  split
  · exact process_base_now _ _
  · rfl

/-- Each offered object is processed if its current-time handler accepts it. -/
theorem fold_complete (P : Obj params → Prop) (t : Time)
    (xs : List (Validator × Obj params)) (acc : World × List Event)
    (hk : ∀ u, GenKnown P (acc.1 u).st) (hn : ∀ u ∈ nodes, (acc.1 u).st.base.now = t)
    (hx : ∀ vo ∈ xs, vo.1 ∈ nodes)
    (hc : ∀ vo ∈ xs, P vo.2 ∧ ∀ a, carriesS params vo.2 a → P a)
    (ha : ∀ vo ∈ xs, ∀ st, GenKnown P st → st.base.now = t →
      processedS params (FGSA.process params st (toWire params vo.2)) vo.2 = true) :
    ∀ vo ∈ xs, processedS params ((xs.foldl (deliverOne t) acc).1 vo.1).st vo.2 = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons vo xs ih =>
    have hk' : ∀ u, GenKnown P ((deliverOne t acc vo).1 u).st := by
      intro u
      rw [adv_deliver_st]
      split
      · exact adv_gen_known_process P _ vo.2 (hk u)
          (hc vo (List.mem_cons_self ..)).1 (hc vo (List.mem_cons_self ..)).2
      · exact hk u
    have hn' : ∀ u ∈ nodes, ((deliverOne t acc vo).1 u).st.base.now = t :=
      fun u hu => (deliver_now t acc vo u).trans (hn u hu)
    intro vo' hm
    rcases List.mem_cons.mp hm with he | hm
    · subst vo'
      apply fold_processed t xs (deliverOne t acc vo) vo.1 vo.2
      rw [adv_deliver_st, ite_eq_left rfl]
      exact ha vo (List.mem_cons_self ..) _ (hk vo.1) (hn vo.1 (hx vo (List.mem_cons_self ..)))
    · exact ih _ hk' hn' (fun vo hm => hx vo (List.mem_cons_of_mem _ hm))
        (fun vo hm => hc vo (List.mem_cons_of_mem _ hm))
        (fun vo hm => ha vo (List.mem_cons_of_mem _ hm)) vo' hm

/-- Without a proposal offer, the batch accepts all its offered HEADs and rows. -/
theorem batch_nonproposal_complete (P : Obj params → Prop) (n : Nat) (w : World)
    (held : List (Obj params)) (hheld : ∀ o ∈ held, isProp o = false)
    (hk : ∀ v, GenKnown P (w v).st)
    (hp : ∀ o ∈ offers n held (tickBatch n w).2, P o)
    (hacc : ∀ o ∈ offers n held (tickBatch n w).2, ∀ st, GenKnown P st →
      st.base.now = n → processedS params (FGSA.process params st (toWire params o)) o = true)
    (v : Validator) (hv : v ∈ nodes) (o : Obj params)
    (ho : o ∈ offers n held (tickBatch n w).2) :
    processedS params ((timeBatch n w held).1 v).st o = true := by
  obtain ⟨hk', hc⟩ := adv_gen_tick_fold_known P n nodes w [] hk (by simp)
  apply fold_complete P n _ _ hk'
    (fun u hu => by rw [tickBatch_st, ite_eq_left hu]; exact (clock_vn (w u).st n).2)
    (fun vo hm => ?_) (fun vo hm => ?_) (fun vo hm st hst hn => ?_) (v, o)
    (List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨v, hv, rfl⟩⟩)
  · obtain ⟨a, _, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    exact hu
  · obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hm
    refine ⟨hp a ha, fun a' hca => ?_⟩
    rcases (mem_offers n held _ a).1 ha with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
    · exact hc a hr a' hca
    · exact (carries_nonprop (hheld a hr) hca).elim
    · exact hc a hr a' hca
  · obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hm
    exact hacc a ha st hst hn

/-- A proposal is the only object released at its time. -/
theorem proposal_only (t : Time) (w : World) (v : Validator) (s : Slot)
    (j : Fin 1) (m : Msg params.n)
    (ho : (⟨.seat (.prop s) j, m⟩ : Obj params) ∈
      (V2.D.tick env (runData 0 []) (w v) v t).2)
    (o' : Obj params) (ho' : o' ∈ (tickBatch t w).2) :
    o' = ⟨.seat (.prop s) j, m⟩ := by
  have hv := adv_gen_tick_holder (w v) v t _ ho
  have hv0 : v = 0 := (Option.some.inj hv).symm
  subst v
  have ha := (Gen.V2.Duty.mem_tick_singleDuty_iff env (runData 0 []) (w 0) 0 t
    (.prop s) (fgsa_prop_singleDuty s) (.propAction s) rfl j m).1 ho
  have ht : (4 : Int) * s = t := ha.2.1
  obtain ⟨v', _, hv'⟩ := (tickBatch_emits t w o').1 ho'
  have holder := adv_gen_tick_holder (w v') v' t o' hv'
  obtain ⟨l', j', m', rfl, hl', ha'⟩ := adv_gen_tick_seat (w v') v' t o' hv'
  have ht' := ((fgsa params unitCodec).duties_spec l' t).1 hl'
  cases l' with
  | headAction r =>
    change (4 : Int) * r + 1 = t at ht'
    omega
  | fgAction r =>
    change (4 : Int) * ((r * 2 : Nat) : Int) + 6 = t at ht'
    omega
  | propAction s' =>
    change (4 : Int) * s' = t at ht'
    have he : s' = s := by
      have he : (s' : Int) = s := mul_left_cancel₀ (by decide : (4 : Int) ≠ 0)
        (ht'.trans ht.symm)
      exact_mod_cast he
    subst s'
    have hv0 : v' = 0 := (Option.some.inj holder).symm
    subst v'
    have hj : j' = j := Subsingleton.elim (α := Fin 1) _ _
    subst j'
    have hm : m' = m := Option.some.inj (ha'.symm.trans ha.2.2.2)
    subst m'
    rfl

/-- If a batch contains a proposal, its release list is a singleton. -/
theorem proposal_singleton (t : Time) (w : World) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) (b : NamedProposal params.n) (hp : o.payload = .proposal b) :
    (tickBatch t w).2 = [o] := by
  have hall : ∀ o' ∈ (tickBatch t w).2, o' = o := by
    obtain ⟨v, _, hv⟩ := (tickBatch_emits t w o).1 ho
    obtain ⟨l, j, m, rfl, _, ha⟩ := adv_gen_tick_seat (w v) v t o hv
    cases l with
    | headAction s =>
      have ha := joined_body ha
      have he : .head (headVote params (FGSA.clock params (w v).st t) s).root = m :=
        Option.some.inj ha
      subst m
      cases hp
    | fgAction r =>
      change (attest params (FGSA.clock params (w v).st t) (w v).record
          ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      cases hp
    | propAction s => exact fun o' ho' => proposal_only t w v s j m hv o' ho'
  have hn := adv_tickBatch_nodup t w
  generalize (tickBatch t w).2 = os at ho hall hn ⊢
  cases os with
  | nil => exact (List.not_mem_nil ho).elim
  | cons a os =>
    have he := hall a (List.mem_cons_self ..)
    subst a
    have hz : os = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      have he := hall a (List.mem_cons_of_mem _ ha)
      exact hn.notMem (he ▸ ha)
    rw [hz]

/-- ROOT-DIGEST W3d. A fresh emitted proposal stores its exact body. -/
theorem proposal_admit (nd : Node params) (v : Validator) (t : Time) (o : Obj params)
    (hr : Reachable params nd.st)
    (ho : o ∈ (V2.D.tick env (runData 0 []) nd v t).2)
    (hw : (fgsa params unitCodec).wellFormed o = true) (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) :
    processedS params
      (FGSA.process params (FGSA.clock params nd.st t) (toWire params o)) o = true := by
  obtain ⟨l, j, m, rfl, hl, ha⟩ := adv_gen_tick_seat nd v t o ho
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have he : .head (headVote params (FGSA.clock params nd.st t) s).root = m :=
      Option.some.inj ha
    subst m
    cases hp
  | fgAction r =>
    change (attest params (FGSA.clock params nd.st t) nd.record
        ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases hp
  | propAction s =>
    have ha := joined_body ha
    have ht : SA.proposalTime params.toParams s = t :=
      ((fgsa params unitCodec).duties_spec (.propAction s) t).1 hl
    change (propose params (FGSA.clock params nd.st t) s).map (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨Parent, hParent, rfl⟩ := Option.map_eq_some_iff.mp ha
      cases hp
      let st := FGSA.clock params nd.st t
      let H := getHead params st (proposerVotes st s) (proposerSupport st s)
      let rs := proposalRows params st H
      let N := namedProposal params Parent s 0
        ((proposerVotes st s).filterMap liftHead?)
        ((proposerSupport st s).filterMap liftHead?) rs
      have hnamed := namedByErase?_sound st H Parent hParent
      have hNamed : namedParentHeld st N = true := decide_eq_true hnamed.1
      have hinv := (storeBundle_of_reachable params st (Reachable.tick t hr)).cstore
      change FGSA.wellFormed params ⟨.proposer s, .proposal N⟩ = true at hw
      change processedS params (FGSA.process params st ⟨.proposer s, .proposal N⟩)
          (ofWire params ⟨.proposer s, .proposal N⟩) = true
      by_cases hmem : ∃ Y ∈ st.fg.TF, Y.root = N.root
      · obtain ⟨Y, hY, he⟩ := hmem
        exact decide_eq_true ⟨Y, (process_cumulative params st _).1 hY, he⟩
      · have hslot : N.erase.slot ≤ st.slot params := by
          have hs := fgsa_proposal_slot (c := unitCodec) nd s
          rw [ht] at hs
          exact le_of_eq hs.symm
        have hfresh : ∀ c ∈ st.base.blocks, c.root ≠ N.erase.root := by
          intro c hc he
          obtain ⟨Y, hY, rfl⟩ := (hinv.baseTree c).1 hc
          exact hmem ⟨Y, hY,
            (eraseFG_root Y).symm.trans (he.trans (named_erase_root N))⟩
        have hF : Block.Preceq (eraseFG st.fg.F) N.erase := by
          change (decide (eraseFG st.fg.F = N.erase) ||
            Block.preceq (eraseFG st.fg.F) Parent.erase) = true
          rw [hnamed.2]
          exact Bool.or_eq_true_iff.mpr (Or.inr
            (F_preceq_headInTree params st hinv _ _ _))
        have hvalid : ∀ Q, parentFG st N.erase = some Q →
            rowsValidForParent params Q N.erase.slot rs = true := by
          intro Q hQ
          have hs : st.slot params = s := by
            have hs := fgsa_proposal_slot (c := unitCodec) nd s
            rw [ht] at hs
            exact hs
          change fgBlockOf st Parent.erase = some Q at hQ
          rw [hnamed.2] at hQ
          change rowsValidForParent params Q s (proposalRows params st H) = true
          rw [proposalRows_eq_proposalRowsFor, ← hs]
          exact proposalRowsFor_valid params st (st.slot params) H Q hQ
        have hpar : N.erase.parent ∈ st.base.blocks := by
          change Parent.erase ∈ st.base.blocks
          rw [hnamed.2]
          exact getHead_stored params st hinv _ _
        obtain ⟨_, Q, hQ, hB⟩ := admitBlock_sufficient params st hinv s N hNamed hw
          hpar hslot hfresh hF hvalid
        exact decide_eq_true ⟨_, hB,
          (fgBlock_root Q N.erase N.rows).trans (named_erase_root N)⟩

/-- A proposal batch accepts its output at every receiver. -/
theorem batch_proposal_complete (n : Nat) (w : World) (held : List (Obj params))
    (hu : GenUniformStores w) (hr : ∀ v, Reachable params (w v).st) (o : Obj params)
    (ho : o ∈ (tickBatch n w).2) (hoff : offers n held (tickBatch n w).2 = [o])
    (hw : (fgsa params unitCodec).wellFormed o = true)
    (b : NamedProposal params.n) (hp : o.payload = .proposal b)
    (v : Validator) (hv : v ∈ nodes) :
    processedS params ((timeBatch n w held).1 v).st o = true := by
  obtain ⟨u, hu', he⟩ := (tickBatch_emits n w o).1 ho
  have ha := proposal_admit (w u) u n o (hr u) he hw b hp
  simp only [timeBatch, deliverAll]
  rw [hoff, List.flatMap_singleton, adv_offer_st n _ o nodes (by decide), ite_eq_left hv,
    tickBatch_st, ite_eq_left hv, hu v hv u hu']
  exact ha

/-! ### Synchrony: the held objects -/

theorem isProp_true {o : Obj params} (h : isProp o = true) : ∃ b, o.payload = .proposal b := by
  unfold isProp at h
  split at h
  · rename_i b he
    exact ⟨b, he⟩
  · cases h

theorem isProp_of {o : Obj params} {b : NamedProposal params.n} (h : o.payload = .proposal b) :
    isProp o = true := by
  unfold isProp
  rw [h]

/-- A carried object is a HEAD vote or an FG row. -/
theorem carried_nonprop {a o : Obj params} (hc : carriesS params a o) : isProp o = false := by
  unfold carriesS at hc
  split at hc
  · rcases hc with hm | hm | hm <;>
      (obtain ⟨x, _, rfl⟩ := List.mem_map.mp hm; rfl)
  · exact hc.elim

/-- No duty acts at time 7. -/
theorem release_seven (w : World) : (tickBatch ((7 : Nat) : Time) w).2 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro o ho
  obtain ⟨v, _, hv⟩ := (tickBatch_emits _ w o).1 ho
  obtain ⟨l, j, m, rfl, hl, _⟩ := adv_gen_tick_seat (w v) v _ o hv
  have ht := ((fgsa params unitCodec).duties_spec l _).1 hl
  cases l with
  | headAction r => change (4 : Int) * r + 1 = ((7 : Nat) : Time) at ht; omega
  | fgAction r => change (4 : Int) * ((r * 2 : Nat) : Int) + 6 = ((7 : Nat) : Time) at ht; omega
  | propAction s => change (4 : Int) * s = ((7 : Nat) : Time) at ht; omega

/-- After GST the adversary holds nothing. -/
theorem held_late (n : Nat) (hn : 8 ≤ n) : (buildPrefix n).held = [] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [bp_held]
  unfold hold
  rw [ite_eq_right (by omega)]

/-- Before GST the adversary collects every released HEAD vote and FG row. -/
theorem held_collect (k : Nat) (hk : k ≤ 7) (n : Nat) (hn : n < k) (o : Obj params)
    (ho : o ∈ (tickBatch n (buildPrefix n).world).2) (hp : isProp o = false) :
    o ∈ (buildPrefix k).held := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [bp_held]
    unfold hold
    rw [ite_eq_left (by omega)]
    by_cases he : n = k
    · subst n
      exact List.mem_append_right _ (List.mem_filter.mpr ⟨ho, by simp [hp]⟩)
    · exact List.mem_append_left _ (ih (by omega) (by omega))

/-- Each release is offered at its own time, or at GST if the adversary holds it. -/
theorem released_offered (n : Nat) (o : Obj params)
    (ho : o ∈ (tickBatch n (buildPrefix n).world).2) :
    ((isProp o = true ∨ 7 ≤ n) ∧
        o ∈ offers n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2) ∨
      ((isProp o = false ∧ n < 7) ∧
        o ∈ offers 7 (buildPrefix 7).held
          (tickBatch ((7 : Nat) : Time) (buildPrefix 7).world).2) := by
  by_cases hp : isProp o = true
  · left
    refine ⟨Or.inl hp, (mem_offers _ _ _ o).2 ?_⟩
    by_cases hn : n < 7
    · exact Or.inl ⟨hn, ho, hp⟩
    · exact Or.inr ⟨by omega, Or.inr ho⟩
  · have hp' : isProp o = false := by simpa using hp
    by_cases hn : 7 ≤ n
    · left
      exact ⟨Or.inr hn, (mem_offers _ _ _ o).2 (Or.inr ⟨hn, Or.inr ho⟩)⟩
    · right
      exact ⟨⟨hp', by omega⟩, (mem_offers _ _ _ o).2 (Or.inr ⟨le_rfl, Or.inl
        (held_collect 7 le_rfl n (by omega) o ho hp')⟩)⟩

/-- An offered proposal is the only release and the only offer of its time. -/
theorem offers_prop (n : Nat) (o : Obj params)
    (ho : o ∈ offers n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2)
    (b : NamedProposal params.n) (hp : o.payload = .proposal b) :
    (tickBatch n (buildPrefix n).world).2 = [o] ∧
      offers n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2 = [o] := by
  have hr := offered_prop_released n _ _ (held_nonprop n) o ho b hp
  have hs := proposal_singleton _ _ o hr b hp
  refine ⟨hs, ?_⟩
  have h7 : n ≠ 7 := by
    rintro rfl
    rw [release_seven] at hr
    exact List.not_mem_nil hr
  unfold offers
  rw [hs]
  by_cases hn : n < 7
  · simp [hn, isProp_of hp]
  · rw [held_late n (by omega)]
    simp [hn]

/-- Before GST the stores know proposals only: no HEAD vote and no FG row. -/
theorem early_known (n : Nat) (hn : n ≤ 7) (v : Validator) :
    GenKnown (fun o => isProp o = true) ((buildPrefix n).world v).st := by
  induction n generalizing v with
  | zero => exact gen_known_init _ v
  | succ n ih =>
    rw [bp_world]
    refine adv_gen_timeBatch_known _ n _ _ (held_nonprop n) (fun u => ih (by omega) u) ?_ v
    intro o ho
    rcases (mem_offers n _ _ o).1 ho with ⟨_, _, hp⟩ | ⟨h7, _⟩
    · exact hp
    · omega

/-- I5: every honest node has processed each offer when its time block is complete. -/
theorem prefix_complete (n : Nat) (v : Validator) (hv : v ∈ nodes) (o : Obj params)
    (ho : o ∈ offers n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2) :
    processedS params ((buildPrefix (n + 1)).world v).st o = true := by
  classical
  rw [bp_world]
  let P := fun a => ∃ u t, GenEmits V2.D.World.init (buildPrefix (n + 1)).events u a t
  have lift : ∀ u a s, GenEmits V2.D.World.init (buildPrefix n).events u a s → P a :=
    fun u a s h => ⟨u, s, by rw [bp_events]; exact adv_genEmits_append_left _ _ _ u a s h⟩
  have hk : ∀ u, GenKnown P ((buildPrefix n).world u).st := by
    intro u
    apply adv_gen_known_mono _ P _ ((adv_gen_prefix_carried n).1 u)
    rintro a ⟨x, s, _, he⟩
    exact lift x a s he
  have hrel : ∀ a ∈ (tickBatch n (buildPrefix n).world).2, P a := by
    intro a ha
    obtain ⟨u, hu⟩ := batch_release_emits n a ha
    exact ⟨u, n, hu⟩
  have hunique : GenSingleDutyUnique P := emits_unique _ (adv_prefix_nodup (n + 1))
  by_cases hp : ∃ b, o.payload = .proposal b
  · obtain ⟨b, hp⟩ := hp
    obtain ⟨hr, hoff⟩ := offers_prop n o ho b hp
    have hmem : o ∈ (tickBatch n (buildPrefix n).world).2 := by
      rw [hr]; exact List.mem_singleton_self o
    obtain ⟨u, hu⟩ := batch_release_emits n o hmem
    have hw := adv_emit_wire n _ (prefix_schedule n) (adv_prefix_origin (n + 1)).1
      (adv_gen_prefix_carried (n + 1)).2 (adv_prefix_no_restart (n + 1)) u o n
      (adv_genEmits_runData n _ u o n hu)
    exact batch_proposal_complete n _ _ (prefix_uniform n) (prefix_reachable n) o hmem hoff
      hw b hp v hv
  · have hnp : ∀ a ∈ offers n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2,
        ∀ b, a.payload ≠ .proposal b := by
      intro a ha b he
      obtain ⟨_, hoff⟩ := offers_prop n a ha b he
      rw [hoff] at ho
      exact hp ⟨b, (List.mem_singleton.mp ho) ▸ he⟩
    apply batch_nonproposal_complete P n _ _ (held_nonprop n) hk _ _ v hv o ho
    · intro a ha
      rcases (mem_offers n _ _ a).1 ha with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
      · exact hrel a hr
      · obtain ⟨_, u, s, _, hu⟩ := (adv_prefix_origin n).2 a hr
        exact lift u a s hu
      · exact hrel a hr
    · intro a ha st hst hnow
      rcases (mem_offers n _ _ a).1 ha with ⟨_, hr, _⟩ | ⟨h7, hr | hr⟩
      · obtain ⟨u, _, hu⟩ := (tickBatch_emits n _ a).1 hr
        exact nonproposal_accept P hunique _ u n n a hu (hrel a hr) (hnp a ha)
          ⟨le_rfl, Or.inl rfl⟩ st hst hnow
      · have hn7 : n = 7 := by
          by_contra hne
          rw [held_late n (by omega)] at hr
          exact List.not_mem_nil hr
        obtain ⟨_, u, s, hs, pre, post, hes, hu⟩ := (adv_prefix_origin n).2 a hr
        exact nonproposal_accept P hunique _ u s n a hu (lift u a s ⟨pre, post, hes, hu⟩)
          (hnp a ha) ⟨le_of_lt hs, Or.inr (by subst hn7; decide)⟩ st hst hnow
      · obtain ⟨u, _, hu⟩ := (tickBatch_emits n _ a).1 hr
        exact nonproposal_accept P hunique _ u n n a hu (hrel a hr) (hnp a ha)
          ⟨le_rfl, Or.inl rfl⟩ st hst hnow

/-! ### Synchrony: receipt -/

/-- A single-duty signing label fixes its emission time. -/
theorem emission_time (es : List Event) (v : Validator) (o : Obj params) (t : Time)
    (he : GenEmits V2.D.World.init es v o t) (d : RunDuty)
    (hD : Gen.V2.Duty.SingleDuty (fgsa params unitCodec) d.signLabel)
    (j : Fin (RunLabel.seats params d.signLabel))
    (ha : o.auth = .seat d.signLabel j) : RunDuty.actTime params d = t := by
  obtain ⟨pre, post, _, ho⟩ := he
  obtain ⟨auth, payload⟩ := o
  dsimp only at ha
  subst auth
  exact ((Gen.V2.Duty.mem_tick_singleDuty_iff env (runData 0 [])
    (genFold V2.D.World.init pre v) v t d.signLabel hD d rfl j payload).1 ho).2.1

/-- A release from the actual prefix state has no earlier emission.
For FG rows, the durable sent set supplies this fact. -/
theorem not_past (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) ((buildPrefix steps).world v) v steps).2) :
    ¬ GenPast (buildPrefix steps).events steps o := by
  have hh := adv_gen_tick_holder ((buildPrefix steps).world v) v steps o ho
  obtain ⟨d, j, m, rfl, hd, ha⟩ := adv_gen_tick_seat ((buildPrefix steps).world v) v steps o ho
  have ht := ((fgsa params unitCodec).duties_spec d steps).1 hd
  rintro ⟨u, t, _, he⟩
  have no_single (hD : Gen.V2.Duty.SingleDuty (fgsa params unitCodec) d.signLabel) : False := by
    have heTime := emission_time _ u _ t he d hD j rfl
    obtain ⟨pre, post, hes, _⟩ := he
    have hm : V2.Event.tick u t ∈ (buildPrefix steps).events := by rw [hes]; simp
    have hlt := (adv_prefix_times steps (.tick u t) hm).2
    change t < (steps : Int) at hlt
    exact (lt_irrefl (steps : Int)) ((ht.symm.trans heTime) ▸ hlt)
  cases d with
  | headAction s => exact no_single (fgsa_head_singleDuty s)
  | propAction s => exact no_single (fgsa_prop_singleDuty s)
  | fgAction r =>
    change (attest params (FGSA.clock params ((buildPrefix steps).world v).st steps)
      ((buildPrefix steps).world v).record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    have hu : u = v := by
      obtain ⟨pre, post, _, hem⟩ := he
      have hhu := adv_gen_tick_holder (genFold V2.D.World.init pre u) u t _ hem
      exact Option.some.inj (hhu.symm.trans hh)
    subst u
    obtain ⟨i, hi, hem⟩ := adv_genEmits_runData 0 (buildPrefix steps).events v _ t he
    have hsent := fgsa_row_sent_before env (runData 0 (buildPrefix steps).events)
      v j body (List.getElem?_eq_some_iff.mp hi).1 t hi hem
    change (body.height_pair, body.finality_pair) ∈
      (genFold V2.D.World.init ((buildPrefix steps).events.take
        (buildPrefix steps).events.length) v).record.sent
      at hsent
    rw [List.take_length, ← (adv_prefix_replay_fresh steps).1] at hsent
    exact (attest_some_fresh _ _ _ _ hb) hsent

/-- The clock preserves the processed predicate exactly. -/
theorem clock_processed (st : State params.n) (t : Time) (o : Obj params) :
    processedS params (FGSA.clock params st t) o = processedS params st o := by
  unfold processedS
  rw [adv_clock_votes, adv_clock_rowPool, clock_fg]

/-- Knowledge can be tracked separately for each receiver. -/
theorem known_fold_local (P : Validator → Obj params → Prop) (w : World)
    (es : List Event) (hnr : ∀ v t, V2.Event.restart v t ∉ es) (hk : ∀ v, GenKnown (P v) (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P v o ∧ ∀ a, carriesS params o a → P v a) :
    ∀ v, GenKnown (P v) (genFold w es v).st := by
  induction es generalizing w with
  | nil => exact hk
  | cons e es ih =>
    apply ih (hnr := fun v t h => hnr v t (List.mem_cons_of_mem _ h))
    · intro u
      cases e with
      | restart v t => exact (hnr v t (List.mem_cons_self ..)).elim
      | tick v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact (adv_tick_st (w v) v t).symm ▸ adv_gen_known_clock (P v) _ t (hk v)
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hk u
      | deliver v o t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact adv_gen_known_process (P v) _ o (hk v)
            (he v o t (List.mem_cons_self ..)).1 (he v o t (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hk u
    · intro v o t hm
      exact he v o t (List.mem_cons_of_mem _ hm)

/-- After a batch, each stored non-proposal was known before or delivered in the batch. -/
theorem batch_known_receipt (n : Nat) (K : Obj params → Prop)
    (hK : ∀ u, GenKnown K ((buildPrefix n).world u).st) (v : Validator) :
    GenKnown (fun o => K o ∨ V2.Event.deliver v o n ∈
        (timeBatch n (buildPrefix n).world (buildPrefix n).held).2)
      ((timeBatch n (buildPrefix n).world (buildPrefix n).held).1 v).st := by
  rw [(adv_timeBatch_replay_fresh _ _ _).1]
  apply known_fold_local (fun u o => K o ∨ V2.Event.deliver u o n ∈
    (timeBatch n (buildPrefix n).world (buildPrefix n).held).2)
    (hnr := adv_timeBatch_no_restart n _ _)
  · intro u
    exact adv_gen_known_mono _ _ _ (hK u) (fun _ h => Or.inl h)
  · intro u o t hm
    obtain ⟨rfl, _, ho⟩ := timeBatch_delivered n _ _ u o t hm
    refine ⟨Or.inr hm, fun a hc => Or.inl ?_⟩
    rcases (mem_offers n _ _ o).1 ho with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
    · exact (adv_gen_tick_fold_known K n nodes _ [] hK (by simp)).2 o hr a hc
    · exact (carries_nonprop (held_nonprop n o hr) hc).elim
    · exact (adv_gen_tick_fold_known K n nodes _ [] hK (by simp)).2 o hr a hc

/-- A processed HEAD vote or FG row is in a pool, so the pool knowledge covers it. -/
theorem processed_known (K : Obj params → Prop) (st : State params.n) (hk : GenKnown K st)
    (nd : Node params) (u : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) nd u t).2) (hnot : ∀ b, o.payload ≠ .proposal b)
    (hp : processedS params st o = true) : K o := by
  obtain ⟨l, j, m, rfl, _, ha⟩ := adv_gen_tick_seat nd u t o ho
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have he : .head (headVote params (FGSA.clock params nd.st t) s).root = m :=
      Option.some.inj ha
    subst m
    exact hk.2.2 _ (List.mem_filterMap.mpr ⟨_, of_decide_eq_true hp, rfl⟩)
  | fgAction r =>
    change (attest params (FGSA.clock params nd.st t) nd.record
        ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact hk.1 _ (of_decide_eq_true hp)
  | propAction s =>
    have ha := joined_body ha
    change (propose params (FGSA.clock params nd.st t) s).map (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      exact (hnot _ rfl).elim

/-- Without a local delivery or restart, replay preserves processed objects exactly. -/
theorem fold_no_local (w : World) (es : List Event) (v : Validator) (o : Obj params)
    (hd : ∀ a t, V2.Event.deliver v a t ∉ es)
    (hr : ∀ t, V2.Event.restart v t ∉ es) :
    processedS params (genFold w es v).st o = processedS params (w v).st o := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    rw [show genFold w (e :: es) =
      genFold (V2.D.World.step env (runData 0 []) w e) es from rfl,
      ih _ (fun a t hm => hd a t (List.mem_cons_of_mem _ hm))
        (fun t hm => hr t (List.mem_cons_of_mem _ hm))]
    cases e with
    | restart u t =>
      have hne : v ≠ u := by intro he; subst u; exact hr t (List.mem_cons_self ..)
      simp only [V2.D.World.step, Function.update_of_ne hne]
    | deliver u a t =>
      have hne : v ≠ u := by intro he; subst u; exact hd a t (List.mem_cons_self ..)
      simp only [V2.D.World.step, Function.update_of_ne hne]
    | tick u t =>
      by_cases he : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact (adv_tick_st (w v) v t).symm ▸ clock_processed (w v).st t o
      · simp only [V2.D.World.step, Function.update_of_ne he]

/-- Node zero's proposal tick is the first event of its time block. -/
theorem prefix_tick_zero (steps : Nat) :
    (buildPrefix (steps + 1)).events[(buildPrefix steps).events.length]? =
        some (.tick 0 steps) ∧
      genFold V2.D.World.init
        ((buildPrefix (steps + 1)).events.take (buildPrefix steps).events.length) =
          (buildPrefix steps).world := by
  obtain ⟨ds, he, _⟩ :=
    adv_timeBatch_block steps (buildPrefix steps).world (buildPrefix steps).held
  rw [bp_events]
  constructor
  · rw [he]
    simp [nodes]
  · rw [List.take_append_length]
    exact (adv_prefix_replay_fresh steps).1.symm

/-- ROOT-DIGEST W3d. A stored non-genesis root has the fixture slot digest. -/
theorem stored_digest (st : State params.n) (hr : Reachable params st)
    (Y : SimplexFG.FGBlock (Fin params.n)) (hY : Y ∈ st.fg.TF) :
    Y = .genesis ∨ Y.root = ⟨Y.slot + 1⟩ := by
  by_cases hg : Y = .genesis
  · exact Or.inl hg
  · right
    have hs := storeBundle_of_reachable params st hr
    obtain ⟨s, N, hw, hErase, _⟩ := stored_wire_of_block params st hs.cstore hs.«meta» hY hg
    obtain ⟨s', M, he, hc, _⟩ := hs.«meta».wireTree _ hw
    have hp := Msg.proposal.inj (congrArg (fun w : Wire params.n => w.payload) he)
    cases hp
    unfold namedContentOk at hc
    rw [hErase] at hc
    have hd := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).2
    dsimp only [params, proposalInput] at hd
    exact (eraseFG_root Y).symm.trans
      (hd.trans (congrArg (fun r : Nat => (⟨r + 1⟩ : BlockId)) (eraseFG_slot Y)))

/-- A generated proposal is not already processed before its time block. -/
theorem proposal_fresh_start (steps : Nat) (v : Validator) (hv : v ∈ nodes) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).world).2) (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) :
    processedS params ((buildPrefix steps).world v).st o = false := by
  obtain ⟨u, _, hu⟩ := (tickBatch_emits steps (buildPrefix steps).world o).1 ho
  have hu0 := (adv_gen_tick_proposal_rows ((buildPrefix steps).world u) u steps o hu b hp).1
  subst u
  obtain ⟨l, j, m, rfl, hl, ha⟩ := adv_gen_tick_seat ((buildPrefix steps).world 0) 0 steps o hu
  cases l with
  | headAction s =>
    have ha := joined_body ha
    have he : .head (headVote params
        (FGSA.clock params ((buildPrefix steps).world 0).st steps) s).root = m :=
      Option.some.inj ha
    subst m
    cases hp
  | fgAction r =>
    change (attest params (FGSA.clock params ((buildPrefix steps).world 0).st steps)
        ((buildPrefix steps).world 0).record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases hp
  | propAction s =>
    have ha := joined_body ha
    have ht : SA.proposalTime params.toParams s = steps :=
      ((fgsa params unitCodec).duties_spec (.propAction s) steps).1 hl
    have hs0 : 0 < s := by
      by_contra hn
      have hz : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      cases ha
    have hi := (prefix_tick_zero steps).1
    rw [← ht] at hi
    have hb := (fgsa_stored_block_slots env
      (runData steps (buildPrefix (steps + 1)).events) (prefix_schedule steps) hi hs0).2.2.1
    change ∀ B ∈ (genFold V2.D.World.init
      ((buildPrefix (steps + 1)).events.take (buildPrefix steps).events.length) 0).st.fg.TF,
        B.slot < s at hb
    rw [(prefix_tick_zero steps).2] at hb
    change (propose params (FGSA.clock params ((buildPrefix steps).world 0).st steps) s).map
      (withApp params 0) = some m at ha
    unfold propose at ha
    rw [ite_eq_right (Nat.ne_of_gt hs0)] at ha
    simp only [Option.map_map] at ha
    obtain ⟨Parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
    cases hp
    change decide (∃ Y ∈ ((buildPrefix steps).world v).st.fg.TF,
      Y.root = (⟨s + 1⟩ : BlockId)) = false
    apply decide_eq_false
    rintro ⟨Y, hY, he⟩
    rw [prefix_uniform steps v hv 0 (by decide)] at hY
    have hslot := hb Y hY
    rcases stored_digest _ (prefix_reachable steps 0) Y hY with hg | hd
    · subst Y
      have hz := congrArg BlockId.value he
      change 0 = s + 1 at hz
      exact Nat.noConfusion hz
    · have hs := congrArg BlockId.value (hd.symm.trans he)
      change Y.slot + 1 = s + 1 at hs
      exact (Nat.lt_irrefl s) ((Nat.add_right_cancel hs) ▸ hslot)

/-- Every offered proposal is directly delivered to every honest node at that time. -/
theorem proposal_receipt (n : Nat) (v : Validator) (hv : v ∈ nodes) (o : Obj params)
    (ho : o ∈ offers n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2)
    (b : NamedProposal params.n) (hp : o.payload = .proposal b) :
    V2.Event.deliver v o n ∈ (timeBatch n (buildPrefix n).world (buildPrefix n).held).2 := by
  by_contra hn
  obtain ⟨hrel, hoff⟩ := offers_prop n o ho b hp
  have hd : ∀ a t, V2.Event.deliver v a t ∉
      (timeBatch n (buildPrefix n).world (buildPrefix n).held).2 := by
    intro a t hm
    obtain ⟨rfl, _, ha⟩ := timeBatch_delivered n _ _ v a t hm
    rw [hoff] at ha
    have he : a = o := List.mem_singleton.mp ha
    exact hn (he ▸ hm)
  have he := fold_no_local (buildPrefix n).world
    (timeBatch n (buildPrefix n).world (buildPrefix n).held).2 v o hd
    (adv_timeBatch_no_restart n _ _ v)
  have hmem : o ∈ (tickBatch n (buildPrefix n).world).2 := by
    rw [hrel]; exact List.mem_singleton_self o
  rw [← (adv_timeBatch_replay_fresh _ _ _).1, proposal_fresh_start n v hv o hmem b hp] at he
  have ht := prefix_complete n v hv o ho
  rw [bp_world] at ht
  exact Bool.noConfusion (ht.symm.trans he)

/-- Broadcast: each offer has a direct same-time delivery to every honest node. -/
theorem batch_receipt (n : Nat) (v : Validator) (hv : v ∈ nodes) (o : Obj params)
    (ho : o ∈ offers n (buildPrefix n).held (tickBatch n (buildPrefix n).world).2) :
    V2.Event.deliver v o n ∈ (timeBatch n (buildPrefix n).world (buildPrefix n).held).2 := by
  classical
  by_cases hp : ∃ b, o.payload = .proposal b
  · obtain ⟨b, hp⟩ := hp
    exact proposal_receipt n v hv o ho b hp
  · have hnot : ∀ b, o.payload ≠ .proposal b := fun b he => hp ⟨b, he⟩
    have hc := prefix_complete n v hv o ho
    rw [bp_world] at hc
    rcases (mem_offers n _ _ o).1 ho with ⟨_, _, hpr⟩ | ⟨h7, hr | hr⟩
    · exact (hp (isProp_true hpr)).elim
    · have hn7 : n = 7 := by
        by_contra hne
        rw [held_late n (by omega)] at hr
        exact List.not_mem_nil hr
      subst hn7
      obtain ⟨_, u, s, _, pre, post, _, hm⟩ := (adv_prefix_origin 7).2 o hr
      have hk := batch_known_receipt 7 (fun o => isProp o = true) (early_known 7 le_rfl) v
      refine (processed_known _ _ hk _ u s o hm hnot hc).resolve_left ?_
      rw [held_nonprop 7 o hr]
      decide
    · obtain ⟨u, _, hm⟩ := (tickBatch_emits n _ o).1 hr
      have hk := batch_known_receipt n (GenPast (buildPrefix n).events n)
        (adv_gen_prefix_carried n).1 v
      exact (processed_known _ _ hk _ u n o hm hnot hc).resolve_left (not_past n u o hm)

/-- A tick in a time block reads its own unchanged input node. -/
theorem batch_tick_state (n : Nat) (w : World) (held : List (Obj params)) (i : Nat)
    (v : Validator) (u : Time) (he : (timeBatch n w held).2[i]? = some (.tick v u)) :
    u = n ∧ v ∈ nodes ∧ genFold w ((timeBatch n w held).2.take i) v = w v := by
  have hut : u = n := adv_timeBatch_time n w held (.tick v u) (List.mem_of_getElem? he)
  subst u
  have hvn : v ∈ nodes := timeBatch_node n w held (.tick v n) (List.mem_of_getElem? he)
  have hv3 : v ≠ 3 := by rintro rfl; simp [nodes] at hvn
  obtain ⟨ds, hes, _⟩ := adv_timeBatch_block n w held
  have hv : (timeBatch n w held).2[v.val]? = some (.tick v n) := by
    rw [hes]
    fin_cases v <;> simp [nodes] at hv3 ⊢
  have hi : i = v.val :=
    (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp he).1 (adv_timeBatch_nodup n w held)).1
      (he.trans hv.symm)
  subst i
  refine ⟨rfl, hvn, ?_⟩
  rw [hes]
  fin_cases v <;> simp [nodes, genFold, V2.D.World.step] at hv3 ⊢

/-- Locate every indexed emission in its generated time block. -/
theorem locate_emission (steps : Nat) (i : Nat) (v : Validator) (t : Time)
    (o : Obj params) (hi : (buildPrefix steps).events[i]? = some (.tick v t))
    (ho : o ∈ (V2.D.tick env (runData 0 [])
      (genFold V2.D.World.init ((buildPrefix steps).events.take i) v) v t).2) :
    ∃ n < steps, t = n ∧ o ∈ (tickBatch n (buildPrefix n).world).2 := by
  induction steps generalizing i with
  | zero => simp [buildPrefix] at hi
  | succ steps ih =>
    rw [bp_events] at hi ho
    by_cases hil : i < (buildPrefix steps).events.length
    · rw [List.getElem?_append_left hil] at hi
      rw [List.take_append_of_le_length (Nat.le_of_lt hil)] at ho
      obtain ⟨n, hn, ht, hm⟩ := ih i hi ho
      exact ⟨n, Nat.lt_succ_of_lt hn, ht, hm⟩
    · have hil' := Nat.le_of_not_lt hil
      rw [List.getElem?_append_right hil'] at hi
      rw [List.take_append, List.take_of_length_le hil', adv_genFold_append,
        ← (adv_prefix_replay_fresh steps).1] at ho
      obtain ⟨rfl, hvn, hs⟩ := batch_tick_state steps _ _ _ v t hi
      rw [hs] at ho
      exact ⟨steps, Nat.lt_succ_self _, rfl, (tickBatch_emits _ _ o).2 ⟨v, hvn, ho⟩⟩

/-- Replay without restarts preserves every processed object. -/
theorem adv_fold_stable (w : World) (es : List Event) (v : Validator) (o : Obj params)
    (hr : ∀ u t, V2.Event.restart u t ∉ es)
    (hp : processedS params (w v).st o = true) :
    processedS params (genFold w es v).st o = true := by
  induction es generalizing w with
  | nil => exact hp
  | cons e es ih =>
    apply ih _ (fun u t hm => hr u t (List.mem_cons_of_mem _ hm))
    cases e with
    | restart u t => exact (hr u t (List.mem_cons_self ..)).elim
    | tick u t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        have he : processedS params (FGSA.clock params (w v).st t) o = true := by
          rw [clock_processed]
          exact hp
        exact (adv_tick_st (w v) v t).symm ▸ he
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hp
    | deliver u a t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact process_processed _ _ _ hp
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hp

/-- A processed object remains processed at every later generator boundary. -/
theorem prefix_stable (m n : Nat) (hmn : m ≤ n) (v : Validator) (o : Obj params)
    (hp : processedS params ((buildPrefix m).world v).st o = true) :
    processedS params ((buildPrefix n).world v).st o = true := by
  obtain ⟨ds, he⟩ := prefix_prefix m n hmn
  rw [(adv_prefix_replay_fresh n).1, ← he, adv_genFold_append, ← (adv_prefix_replay_fresh m).1]
  apply adv_fold_stable _ ds v o _ hp
  intro u t hm
  apply adv_prefix_no_restart n u t
  rw [← he]
  exact List.mem_append_right _ hm

/-- From time 8, all honest nodes have processed all earlier emissions. -/
theorem past_complete (steps : Nat) (h8 : 8 ≤ steps) (o : Obj params) (t : Time)
    (he : GenPast (buildPrefix steps).events t o) (v : Validator) (hv : v ∈ nodes) :
    processedS params ((buildPrefix steps).world v).st o = true := by
  obtain ⟨u, s, _, he⟩ := he
  obtain ⟨i, hi, ho⟩ := adv_genEmits_runData 0 _ u o s he
  rw [(V2.D.Run.step_tick_eq env _ hi).2] at ho
  obtain ⟨n, hn, _, hm⟩ := locate_emission steps i u s o hi ho
  rcases released_offered n o hm with ⟨_, hoff⟩ | ⟨⟨_, _⟩, hoff⟩
  · exact prefix_stable (n + 1) steps hn v o (prefix_complete n v hv o hoff)
  · exact prefix_stable 8 steps h8 v o (prefix_complete 7 v hv o hoff)

/-- An event at time at least `m` is after the boundary for times below `m`. -/
theorem index_after (steps m i : Nat) (hm : m ≤ steps) (e : Event)
    (hi : (buildPrefix steps).events[i]? = some e) (ht : (m : Int) ≤ e.time) :
    (buildPrefix m).events.length ≤ i := by
  obtain ⟨ds, he⟩ := prefix_prefix m steps hm
  by_contra hn
  have hl : i < (buildPrefix m).events.length := Nat.lt_of_not_ge hn
  rw [← he, List.getElem?_append_left hl] at hi
  exact (not_lt.mpr ht) (adv_prefix_times m e (List.mem_of_getElem? hi)).2

/-- Boundary completeness persists through any later event prefix. -/
theorem index_stable (steps m i : Nat) (hm : m ≤ steps)
    (hi : (buildPrefix m).events.length ≤ i) (v : Validator) (o : Obj params)
    (hp : processedS params ((buildPrefix m).world v).st o = true) :
    processedS params
      (genFold V2.D.World.init ((buildPrefix steps).events.take i) v).st o = true := by
  obtain ⟨ds, he⟩ := prefix_prefix m steps hm
  rw [← he, List.take_append, List.take_of_length_le hi, adv_genFold_append,
    ← (adv_prefix_replay_fresh m).1]
  apply adv_fold_stable _ _ v o _ hp
  intro u t hmem
  apply adv_prefix_no_restart steps u t
  rw [← he]
  exact List.mem_append_right _ (List.mem_of_mem_take hmem)

/-- A handled object is the envelope or one of its carried objects. -/
theorem adv_handles_carries (st : State params.n) (a o : Obj params)
    (hh : handlesS params st a o) : a = o ∨ carriesS params a o := by
  rcases hh with he | hh
  · exact Or.inl he
  · generalize hd : (toWire params a).decode = d at hh
    cases d with
    | none => exact hh.elim
    | some m =>
      cases m with
      | vote s i b => exact hh.elim
      | row i body => exact hh.elim
      | block s b =>
        have he := adv_decode_proposal a s b hd
        right
        simp only [carriesS, he]
        exact hh.2.elim Or.inl (fun hm => Or.inr (Or.inr hm))

/-- A direct delivery is a handler call. -/
theorem direct_handle (h : Time) (es : List Event)
    (v : Validator) (o : Obj params) (t : Time) (hm : V2.Event.deliver v o t ∈ es) :
    ∃ i, V2.D.Run.handlesAt env (runData h es) i v o t := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨i, o, hi, Or.inl rfl⟩

theorem run_mem_batch (n : Nat) (hn : n < 301) (e : Event)
    (he : e ∈ (timeBatch n (buildPrefix n).world (buildPrefix n).held).2) :
    e ∈ run.events := by
  rw [run_events, adv_prefix_blocks]
  exact List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn, he⟩

/-- Broadcast in the run: at the emission time, or at GST for a held object. -/
theorem run_broadcast (v : Validator) (o : Obj params) (t : Time)
    (he : V2.D.Run.emits env run v o t) (w : Validator) (hw : w ∈ nodes) :
    ∃ t', t ≤ t' ∧ t' < max t 7 + 1 ∧ V2.Event.deliver w o t' ∈ run.events := by
  obtain ⟨i, hi, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq env _ hi).2] at ho
  obtain ⟨n, hn, rfl, hm⟩ := locate_emission 301 i v t o hi ho
  rcases released_offered n o hm with ⟨_, hoff⟩ | ⟨⟨_, hn7⟩, hoff⟩
  · exact ⟨n, le_rfl, Int.lt_add_one_iff.mpr (le_max_left _ _),
      run_mem_batch n hn _ (batch_receipt n w hw o hoff)⟩
  · exact ⟨((7 : Nat) : Time), Int.ofNat_le.mpr (by omega),
      Int.lt_add_one_iff.mpr (by exact_mod_cast le_max_right _ _),
      run_mem_batch 7 (by omega) _ (batch_receipt 7 w hw o hoff)⟩

/-- Relay in the run: an envelope and its carried objects are already handled. -/
theorem run_relay (v : Validator) (i : Nat) (a o : Obj params) (t : Time)
    (hi : (buildPrefix 301).events[i]? = some (.deliver v a t))
    (hh : a = o ∨ carriesS params a o) (w : Validator) (hw : w ∈ nodes)
    (hp : (fgsa params unitCodec).processed
      (genFold V2.D.World.init ((buildPrefix 301).events.take (i + 1)) w) o = false) :
    V2.Event.deliver w o t ∈ run.events := by
  have hm := List.mem_of_getElem? hi
  rw [adv_prefix_blocks] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' := List.mem_range.mp hn
  obtain ⟨rfl, _, ha⟩ := timeBatch_delivered n _ _ v a t hm
  rcases hh with rfl | hc
  · exact run_mem_batch n hn' _ (batch_receipt n w hw a ha)
  · exfalso
    have hr : a ∈ (tickBatch n (buildPrefix n).world).2 := by
      rcases (mem_offers n _ _ a).1 ha with ⟨_, hr, _⟩ | ⟨_, hr | hr⟩
      · exact hr
      · exact (carries_nonprop (held_nonprop n a hr) hc).elim
      · exact hr
    by_cases h8 : 8 ≤ n
    · have hpast := (adv_gen_tick_fold_known (GenPast (buildPrefix n).events n) n nodes _ []
        (adv_gen_prefix_carried n).1 (by simp)).2 a hr o hc
      have hpc := past_complete n h8 o n hpast w hw
      have hidx := index_after 301 n i (by omega) _ hi le_rfl
      have ht := index_stable 301 n (i + 1) (by omega) (by omega) w o hpc
      exact Bool.noConfusion (hp.symm.trans ht)
    · have hk := (adv_gen_tick_fold_known (fun o => isProp o = true) n nodes _ []
        (early_known n (by omega)) (by simp)).2 a hr o hc
      rw [carried_nonprop hc] at hk
      exact Bool.noConfusion hk

/-- A delivered object is processed after its actual generator batch. A later
anchor uses that history; an earlier anchor uses the recorded delivery. -/
theorem service_of_delivery (w : Validator) (hw : w ∈ nodes) (o : Obj params)
    (t a d : Time) (hm : V2.Event.deliver w o t ∈ run.events) (htd : t < d) :
    V2.D.DeliveryService env run w o a d := by
  rw [run_events, adv_prefix_blocks] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < 301 := List.mem_range.mp hn
  obtain ⟨rfl, _, ho⟩ := timeBatch_delivered n _ _ w o t hm
  by_cases hna : (n : Time) < a
  · obtain ⟨ds, he⟩ := prefix_prefix (n + 1) 301 (by omega)
    have hlen : (buildPrefix (n + 1)).events.length ≤ V2.D.Run.actionCut run a := by
      change _ ≤ (run.events.filter
        (fun e => decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))).length
      have hf : (buildPrefix (n + 1)).events.filter
          (fun e => decide (e.time < a ∨ (e.time = a ∧ e.phase = 0))) =
            (buildPrefix (n + 1)).events := by
        apply List.filter_eq_self.mpr
        intro e hem
        have ht := (adv_prefix_times (n + 1) e hem).2
        have hta : e.time < a := by dsimp [Time] at *; omega
        exact decide_eq_true (Or.inl hta)
      rw [run_events, ← he, List.filter_append, List.length_append, hf]
      omega
    left
    refine ⟨(buildPrefix (n + 1)).events.length, hlen, ?_⟩
    rw [show run = runData horizon (buildPrefix 301).events from rfl,
      adv_runData_stateBefore, ← he]
    simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
      List.append_nil]
    rw [← (adv_prefix_replay_fresh (n + 1)).1]
    exact prefix_complete n w hw o ho
  · right
    exact ⟨n, le_of_not_gt hna, htd, direct_handle horizon _ w o n
      (run_mem_batch n hn' _ hm)⟩

/-- The demand is bounded at its actual anchor, including an old stored object. -/
theorem service_of_emission (v : Validator) (o : Obj params) (t : Time)
    (he : V2.D.Run.emits env run v o t) (w : Validator) (hw : w ∈ nodes)
    (a : Time) (hta : t ≤ a) :
    V2.D.DeliveryService env run w o a (max a env.t_GST + env.Δ) := by
  obtain ⟨u, _, hud, hu⟩ := run_broadcast v o t he w hw
  apply service_of_delivery w hw o u a _ hu
  have hm : max t 7 + 1 ≤ max a env.t_GST + env.Δ := by
    change max t 7 + 1 ≤ max a 7 + 1
    dsimp only [Time] at *
    omega
  exact hud.trans_le hm

/-- I-SYNC: finite delivery demands use real receipts or earlier processing. -/
theorem run_sync : V2.D.PartialSynchrony env run where
  broadcast_emitted v _ o t he w hw a hta _ _ _ _ _ _ :=
    service_of_emission v o t he w ((nodes_honest w).2 hw) a hta
  relay_accepted v _ i o t ha w hw a hta _ _ _ _ _ _ := by
    obtain ⟨⟨parent, hi, hh⟩, _, _⟩ := ha
    have hm := List.mem_of_getElem? hi
    have hc := adv_handles_carries _ parent o hh
    obtain ⟨x, u, hut, hem⟩ : GenPast (buildPrefix 301).events t o := by
      rcases hc with rfl | hc
      · exact (adv_prefix_origin 301).1 v parent t hm
      · exact (adv_gen_prefix_carried 301).2 v parent t hm o hc
    exact service_of_emission x o u (adv_genEmits_runData horizon _ x o u hem)
      w ((nodes_honest w).2 hw) a (hut.trans hta)

/-! ### Roots -/

/-- The proposal shape of an honest construction. -/
theorem proposal_shape (st : State params.n) (s : Slot) (app : Nat)
    (N : NamedProposal params.n)
    (ha : (propose params st s).map (withApp params app) = some (.proposal N)) :
    N.erase = proposalBlock params
      (getHead params st (proposerVotes st s) (proposerSupport st s)) s app
      N.raw N.support N.rows := by
  unfold propose at ha
  split at ha
  · cases ha
  · simp only [Option.map_map] at ha
    obtain ⟨P, hP, he⟩ := Option.map_eq_some_iff.mp ha
    have hN := Msg.proposal.inj he
    subst N
    have heP := (namedByErase?_sound st _ P hP).2
    rw [namedProposal_erase, heP]
    rfl

/-- A delivered proposal is node zero's emission at a tick, with its own slot label. -/
theorem delivered_proposal {x : Validator} {o : Obj params} {t : Time}
    {N : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N) :
    ∃ i t', run.events[i]? = some (.tick 0 t') ∧ o ∈ V2.D.Run.emitsAt env run i ∧
      o = ofWire params ⟨.proposer N.slot, .proposal N⟩ := by
  obtain ⟨u, s, _, he⟩ := (adv_prefix_origin 301).1 x o t hd
  obtain ⟨i, hi, hem⟩ := adv_genEmits_runData horizon _ u o s he
  obtain ⟨pre, post, _, ho⟩ := he
  have hh := adv_gen_tick_holder _ u s o ho
  obtain ⟨l, j, m, rfl, _, ha⟩ := adv_gen_tick_seat _ u s _ ho
  cases l with
  | headAction r =>
    have ha := joined_body ha
    have he : .head (headVote params (FGSA.clock params (genFold V2.D.World.init pre u).st s)
      r).root = m := Option.some.inj ha
    subst m
    cases hp
  | fgAction r =>
    change (attest params (FGSA.clock params (genFold V2.D.World.init pre u).st s)
      (genFold V2.D.World.init pre u).record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, _, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases hp
  | propAction s' =>
    have ha := joined_body ha
    change m = .proposal N at hp
    subst m
    change (propose params (FGSA.clock params (genFold V2.D.World.init pre u).st s) s').map
      (withApp params 0) = some (.proposal N) at ha
    have hb := proposal_shape _ s' 0 N ha
    have hslot : N.slot = s' := by rw [← named_erase_slot, hb]; rfl
    subst hslot
    have hu : u = 0 := (Option.some.inj hh).symm
    subst hu
    have hj : j = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp j.isLt)
    subst hj
    exact ⟨i, s, hi, hem, rfl⟩

/-- Each delivered parent was held before its emission. -/
theorem nvParents : ∀ x o t N,
    V2.Event.deliver x o t ∈ run.events → o.payload = .proposal N →
    ∃ i y, N.parent ∈ (V2.D.Run.stateBefore env run i y).st.namedBodies := by
  intro x o t N hd hp
  obtain ⟨i, t', hi, hem, _⟩ := delivered_proposal hd hp
  obtain ⟨j, hj⟩ := emitted_payload_parent_stored env run ⟨i, hi, hem⟩ hp
  exact ⟨j, 0, hj⟩

/-- The slot digest gives every delivered proposal a small root. -/
theorem nv_delivery_root {x : Validator} {o : Obj params} {t : Time}
    {N : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N) :
    N.root = ⟨N.slot + 1⟩ := by
  obtain ⟨i, t', hi, hem, he⟩ := delivered_proposal hd hp
  rw [he] at hem
  exact emitted_proposal_slot_root env run (fun _ => rfl) i 0 t' N.slot N hi hem

/-- The proposal key of a slot signs one object, so equal slots give equal proposals. -/
theorem nv_delivery_unique {x y : Validator} {o o' : Obj params} {t u : Time}
    {N M : NamedProposal params.n}
    (hd : V2.Event.deliver x o t ∈ run.events) (hp : o.payload = .proposal N)
    (hd' : V2.Event.deliver y o' u ∈ run.events) (hp' : o'.payload = .proposal M)
    (hs : N.slot = M.slot) : N = M := by
  obtain ⟨i, t', hi, hem, he⟩ := delivered_proposal hd hp
  obtain ⟨i', u', hi', hem', he'⟩ := delivered_proposal hd' hp'
  have hn : run.events.Nodup := adv_prefix_nodup 301
  have heq := (Gen.V2.Duty.emitted_unique_of_singleDuty env run hn (.prop N.slot)
    (fgsa_prop_singleDuty N.slot) ⟨0, Nat.one_pos⟩ 0 i i' t' u' o o' hi hi' hem hem'
    (by rw [he]; rfl) (by rw [he', ← hs]; rfl)).2
  rw [heq, hp'] at hp
  exact (Msg.proposal.inj hp).symm

/-- I-ROOTS: named origin and slot-key uniqueness give root collision freedom. -/
theorem nvRoots : NamedRootCollisionFree params unitCodec env run where
  root_injective := by
    intro B C hB hC A D hA hD he
    have hAs : NamedProposalInRun params unitCodec env run A := by
      rcases hA with hA | hA
      · exact namedScope_ancestor env run hB hA
      · exact namedScope_ancestor env run hC hA
    have hDs : NamedProposalInRun params unitCodec env run D := by
      rcases hD with hD | hD
      · exact namedScope_ancestor env run hB hD
      · exact namedScope_ancestor env run hC hD
    rcases namedProposalInRun_genesis_or_delivered env run nvParents hAs with rfl | hA
    · rcases namedProposalInRun_genesis_or_delivered env run nvParents hDs with rfl | hD
      · rfl
      · obtain ⟨x, o, t, hd, hp⟩ := hD
        have hr := nv_delivery_root hd hp
        have hh := congrArg BlockId.value (he.trans hr)
        change 0 = D.slot + 1 at hh
        exact (Nat.succ_ne_zero _ hh.symm).elim
    · obtain ⟨x, o, t, hd, hp⟩ := hA
      have hr := nv_delivery_root hd hp
      rcases namedProposalInRun_genesis_or_delivered env run nvParents hDs with rfl | hD
      · have hh := congrArg BlockId.value (hr.symm.trans he)
        change A.slot + 1 = 0 at hh
        exact (Nat.succ_ne_zero _ hh).elim
      · obtain ⟨y, o', u, hd', hp'⟩ := hD
        have hr' := nv_delivery_root hd' hp'
        apply nv_delivery_unique hd hp hd' hp'
        have hh := congrArg BlockId.value (hr.symm.trans (he.trans hr'))
        change A.slot + 1 = D.slot + 1 at hh
        exact Nat.add_right_cancel hh

/-! ### Regimes -/

open Gen.Pure

/-- Every honest emitted proposal is directly received by node zero. -/
theorem nvReceiptRoots : NamedReceiptRootCollisionFree params unitCodec env run := by
  have scope (A : NamedProposal params.n)
      (h : NamedProposalReceiptScope params unitCodec env run A) :
      NamedProposalInRun params unitCodec env run A := by
    rcases h with h | ⟨v, hv, o, t, N, hem, hp, hAN⟩
    · exact h
    · obtain ⟨u, _, _, hd⟩ := run_broadcast v o t hem 0 (by decide)
      exact ⟨N, Or.inl ⟨0, o, u, hd, hp⟩, hAN⟩
  intro A B hA hB he
  exact nvRoots.root_injective A B (scope A hA) (scope B hB)
    A B (Or.inl (named_preceq_refl _)) (Or.inr (named_preceq_refl _)) he

/-- I-BASE: the adversarial run inhabits Base₂. -/
theorem base : Base₂ params unitCodec env run where
  valid := nvExecution
  linked := adv_linked horizon _
  cstar := adv_cstar horizon _
  restartsAtWakes := by
    intro v t hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    exact (noRestart i v t hi).elim
  delta := env_delta
  receiptIdealization := nvReceiptRoots

/-- Rows and other objects have the same delay, Δ = ΔF = 1. -/
theorem delay_const : fgsaDelay (p := params) env.Δ 1 = fun _ => env.Δ := by
  funext o
  unfold fgsaDelay
  split <;> rfl

theorem sync : Gen.V2.Duty.PartialSynchronyBy env run (fgsaDelay env.Δ 1) := by
  rw [delay_const]
  exact (Gen.V2.Duty.partialSynchrony_iff_by_const env run).mp run_sync

/-- I-REC: the adversarial run inhabits Recovery₂ with G = 4 and ΔF = 1. -/
theorem nvRecovery : RecoverySleep₂ params unitCodec env run 4 1 where
  sync := sync
  deltaF := by decide
  gap := by intro t ht _; exact proposer_gap horizon _ t ht
  base := base
  fault := adv_fault_bound
  awake := by intros; rfl
  gapPos := adv_gap_positive
  suffixNoRestart := by intro x hx i t hi; exact (noRestart i x t hi).elim
  joinedGap := by
    intro t ht hh
    obtain ⟨s, hts, hst, hs⟩ := proposer_gap horizon _ t (by
      have hlo : env.t_GST ≤ recoveryStart params env := by decide
      exact hlo.trans ht)
    refine ⟨s, hts, hst, hs, rfl, ?_, ?_⟩
    · intro u _ _ hw; cases hw.2
    · intro u _ _ hu
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hu
      exact (noRestart i _ u hi).elim

theorem livenessBound : LivenessBoundW params 1 := ⟨by decide⟩

theorem healingPrem : HealingPrem params unitCodec 4 1 env run () :=
  ⟨nvRecovery, livenessBound⟩

/-- I-HEAL: Jst + B_HF = 14 + 247 = 261 ≤ 300. -/
theorem healingTimePrem : HealingTimePrem params unitCodec 4 1 env run () :=
  ⟨healingPrem, by rw [run_horizon]; decide⟩

/-- Every positive slot has the honest proposer node 0. -/
theorem nvGood (r : Nat) (hr : 1 ≤ r) :
    FGoodE_W (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec))
      params.R (kappaF params 1) r := by
  rw [FGoodE_W_def]
  have hk : kappaF params 1 = 2 := by decide
  rw [hk]
  refine ⟨honest_slot horizon _ (by change 0 < r * 2; omega),
    honest_slot horizon _ (by change 0 < (r + 1) * 2; omega),
    ⟨(r + 1) * 2 + 2, le_rfl, ?_, honest_slot horizon _ (by change 0 < (r + 1) * 2 + 2; omega)⟩,
    honest_slot horizon _ (by change 0 < (r + 2) * 2 + 2; omega)⟩
  change (r + 1) * 2 + 2 ≤ (r + 2) * 2
  omega

theorem nvRecFE : FE_W params 1
    (Gen.V2.Duty.HonestSlot run (fgsaInterface params unitCodec))
      (recoveryStart params env) run.horizon 1 := by
  rw [FE_W_def, RecFE_W_def]
  refine ⟨le_rfl, ?_⟩
  intro q hq _ _
  exact ⟨q, (by rw [InWindow_def]; exact ⟨le_rfl, Nat.lt_succ_self q⟩), nvGood q hq⟩

theorem nvFinalitySet : FinalitySet_W params unitCodec env run 4 1 .recFE 1 :=
  ⟨nvRecovery, livenessBound, by rw [FinFormW.holdsW_def]; exact nvRecFE⟩

/-- I-FIN: FF5 at the GST bound, t = 261, with 261 + W_W = 294 ≤ 300. -/
theorem nvGSTPrem : FinalityLivenessGSTPrem_W params unitCodec 4 1 .recFE 1 env run ⟨261⟩ :=
  ⟨nvFinalitySet, by decide, by rw [run_horizon]; decide⟩

theorem nvFirstFinalityPrem : FirstFinalityPrem_W params unitCodec 4 1 .recFE 1 env run () :=
  ⟨nvFinalitySet, by rw [run_horizon]; decide⟩

/-! ### Claim applications -/

/-- Node zero's tick is the first event of its time block. -/
theorem tick_zero_emits (n : Nat) (hn : n < 301) (o : Obj params)
    (ho : o ∈ (V2.D.tick env (runData 0 []) ((buildPrefix n).world 0) 0 n).2) :
    V2.D.Run.emits env run 0 o n := by
  obtain ⟨ds, hds⟩ := prefix_prefix (n + 1) 301 (by omega)
  obtain ⟨ds', hb, _⟩ := adv_timeBatch_block n (buildPrefix n).world (buildPrefix n).held
  apply adv_genEmits_runData horizon _ 0 o n
  refine ⟨(buildPrefix n).events,
    (([1, 2] : List Validator).map (fun v => V2.Event.tick v (n : Time)) ++ ds') ++ ds, ?_, ?_⟩
  · rw [← hds, bp_events n, hb]
    simp [nodes]
  · rw [← (adv_prefix_replay_fresh n).1]
    exact ho

/-- Node 0 proposes at every positive slot of the run. -/
theorem adv_honest_proposal_exists (s : Slot) (hs : 0 < s) (hn : 4 * s < 301) :
    ∃ B, HonestProposal env run (fgsaInterface params unitCodec) s B := by
  have hr : Reachable params
      (FGSA.clock params ((buildPrefix (4 * s)).world 0).st ((4 * s : Nat) : Time)) :=
    Reachable.tick _ (prefix_reachable (4 * s) 0)
  obtain ⟨P, hP, _, _⟩ := propose_parent_lookup params hr s
  have ht : SA.proposalTime params.toParams s = ((4 * s : Nat) : Time) := by
    change (4 : Int) * s = ((4 * s : Nat) : Int)
    push_cast
    rfl
  have hg := fgsa_joinedNow_of_joinedEnv env
    (runData ((4 * s : Nat) : Time) (buildPrefix (4 * s + 1)).events)
    (prefix_schedule (4 * s)) (prefix_tick_zero (4 * s)).1 (by
      intro u _ _ hm
      exact (adv_prefix_no_restart (4 * s + 1) 0 u hm).elim)
  rw [adv_runData_stateBefore, (prefix_tick_zero (4 * s)).2] at hg
  have ho := (fgsa_emits_proposal env (runData 0 []) ((buildPrefix (4 * s)).world 0) 0
    ((4 * s : Nat) : Time) s _).mpr ⟨rfl, ht, rfl, hg, by
      delta propose
      simp only [Nat.ne_of_gt hs, ↓reduceIte, hP, Option.map_some]
      rfl⟩
  have hem := tick_zero_emits (4 * s) hn _ ho
  rw [← ht] at hem
  exact ⟨_, honest_slot horizon _ hs, _, hem, rfl⟩

/-- C-AVAIL: the aggregate availableGST claim on the adversarial run. -/
theorem nvAvailableGST : ∃ w, HealingInput params unitCodec env run w 1 ∧
    tstar params w < recoveryStart params env + B_HF params 1 4 ∧
    AvailableFromConcl params unitCodec env run (recoveryStart params env + B_HF params 1 4) :=
  (fgsaClaims params).availableGST 4 1 adv_delta_ratio unitCodec env run healingTimePrem

/-- C-AVAIL: the slot-70 proposal (time 280, gate 286) is served to every honest reader. -/
theorem nvAvailableService : ∃ B, HonestProposal env run (fgsaInterface params unitCodec) 70 B ∧
    InclusionAt params unitCodec env run ⟨70, B⟩ := by
  obtain ⟨B, hB⟩ := adv_honest_proposal_exists 70 (by decide) (by decide)
  obtain ⟨_, _, _, h⟩ := nvAvailableGST
  refine ⟨B, hB, h.2 ⟨70, B⟩ ?_ hB ?_⟩
  · change (14 : Time) + B_HF params 1 4 ≤ V2.D.proposalTime (fgsaInterface params unitCodec) 70
    decide
  · change SA.gateTime params.toParams 70 ≤ run.horizon
    rw [run_horizon]
    decide

/-- C-FIN: FF5 from the aggregate GST claim, with deadline 294. -/
theorem nvFF5 : FinalityLivenessConcl_W params unitCodec env run 261 294 := by
  obtain ⟨_, _, _, h, _⟩ := (fgsaClaims params).finalityLivenessGSTRecFE 4 1 1
    adv_delta_ratio unitCodec env run ⟨261⟩ nvGSTPrem
  exact h

/-- C-FIN: FirstFinality from the aggregate claim, with deadline 14 + 247 + 33 = 294. -/
theorem nvFirstFinality : FirstFinalityConcl_W params unitCodec env run 1 4 294 :=
  (fgsaClaims params).firstFinalityRecFE 4 1 1 adv_delta_ratio unitCodec env run ()
    nvFirstFinalityPrem

theorem nvProposalGSTPrem (B : Block)
    (hB : HonestProposal env run (fgsaInterface params unitCodec) 66 B) :
    ProposalFinalGSTPrem_W params unitCodec 4 1 .recFE 1 env run ⟨66, B⟩ := by
  refine ⟨nvFinalitySet, hB, ?_, ?_⟩
  · change (14 : Time) + B_HF params 1 4 ≤ V2.D.proposalTime (fgsaInterface params unitCodec) 66
    decide
  · change V2.D.proposalTime (fgsaInterface params unitCodec) 66 + W_W params 1 1 ≤ run.horizon
    rw [run_horizon]
    decide

/-- C-FIN: the slot-66 proposal (time 264) is final at every honest node by time 297. -/
theorem nvProposalFinal : ∃ B, HonestProposal env run (fgsaInterface params unitCodec) 66 B ∧
    ProposalFinalConcl_W params unitCodec env run B 297 := by
  obtain ⟨B, hB⟩ := adv_honest_proposal_exists 66 (by decide) (by decide)
  obtain ⟨_, _, _, h⟩ := (fgsaClaims params).proposalFinalGSTRecFE 4 1 1 adv_delta_ratio
    unitCodec env run ⟨66, B⟩ (nvProposalGSTPrem B hB)
  exact ⟨B, hB, h⟩

/-! ### The asynchrony witness -/

/-- Node 0's slot-0 HEAD vote is released at time 1 and held until GST: every honest node
receives it at time 7 and no node receives it earlier. With Δ = 1, 7 > 1 + Δ. -/
theorem held_vote_delay : ∃ o : Obj params,
    V2.D.Run.emits env run 0 o ((1 : Nat) : Time) ∧ (∃ b, o.payload = Msg.head b) ∧
      (∀ w ∈ nodes, V2.Event.deliver w o ((7 : Nat) : Time) ∈ run.events) ∧
      ∀ w t, V2.Event.deliver w o t ∈ run.events → ((7 : Nat) : Time) ≤ t := by
  have ho := (Gen.V2.Duty.mem_tick_singleDuty_iff env (runData 0 []) ((buildPrefix 1).world 0) 0
    ((1 : Nat) : Time) (.base (.head 0)) (fgsa_head_singleDuty 0) (.headAction 0) rfl
    ⟨0, by decide⟩ _).2
    ⟨rfl, by decide, rfl, rfl⟩
  refine ⟨_, tick_zero_emits 1 (by decide) _ ho, ⟨_, rfl⟩, ?_, ?_⟩
  · intro w hw
    have hr := (tickBatch_emits ((1 : Nat) : Time) (buildPrefix 1).world _).2 ⟨0, by decide, ho⟩
    rcases released_offered 1 _ hr with ⟨hp, _⟩ | ⟨_, hoff⟩
    · rcases hp with hp | hp
      · cases hp
      · omega
    · exact run_mem_batch 7 (by decide) _ (batch_receipt 7 w hw _ hoff)
  · intro w t hm
    rw [run_events, adv_prefix_blocks] at hm
    obtain ⟨m, _, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨rfl, _, hoff⟩ := timeBatch_delivered m _ _ w _ t hm
    rcases (mem_offers m _ _ _).1 hoff with ⟨_, _, hp⟩ | ⟨h7, _⟩
    · cases hp
    · exact Int.ofNat_le.mpr h7

/-- Run parameters: four seats, one faulty seat, GST 7, Δ = ΔF = 1, horizon 300. -/
theorem nvParameters : params.n = 4 ∧ (Gen.V2.Duty.faulty run).card = 1 ∧ env.t_GST = 7 ∧
    env.Δ = 1 ∧ run.horizon = 300 :=
  ⟨rfl, faulty_card, rfl, rfl, rfl⟩

#print axioms nvExecution
#print axioms run_sync
#print axioms nvRoots
#print axioms base
#print axioms nvRecovery
#print axioms healingTimePrem
#print axioms nvFinalitySet
#print axioms nvGSTPrem
#print axioms nvFirstFinalityPrem
#print axioms adv_honest_proposal_exists
#print axioms nvAvailableGST
#print axioms nvAvailableService
#print axioms nvFF5
#print axioms nvFirstFinality
#print axioms nvProposalFinal
#print axioms held_vote_delay
#print axioms nvParameters

end AvailableChain.FGSA.Run.Tests.NonVacuity.Adversarial
end
