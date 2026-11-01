module
public import AvailableChainFGSAClaims.Statements.WeakContinuation
public import AvailableChainFGSARun.Proofs.EmissionWellFormed -- shake: keep (INHABIT)

@[expose] public section

/-! W1: concrete source and continuation on the window model.

The generator uses the current duty engine and the real FG-SA handlers.
It ticks awake nodes before it delivers each released object to awake receivers.
After time 253, only node zero is awake. The source ends at 253, and the
continuation ends at 269. Proofs follow the generator without evaluating the
complete encoded trace.
-/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

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

def strongEnv : Generic.Env Validator where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake _ _ := true

def weakEnv : Generic.Env Validator :=
  { strongEnv with awake := fun v t => decide (t ≤ 253 ∨ v = 0) }

/-- One holder per base seat; node zero proposes in every slot. -/
def seatOf : (ℓ : RunLabel) → Fin (RunLabel.seats params ℓ) → Validator
  | .base _, i => i
  | .prop _, _ => 0

/-- Static run data for the schedule generator. -/
def runData (horizon : Time) (events : List Event) :
    V2.D.Run Validator (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := horizon
  events := events
  seatOf := seatOf
  input _ _ := ()

def nodes : List Validator := [0, 1, 2, 3]

/-- Only awake nodes take state steps or receive event records. -/
def awakeNodes (t : Time) : List Validator := nodes.filter (weakEnv.awake · t)

theorem awakeNodes_mem (v : Validator) (t : Time) :
    v ∈ awakeNodes t ↔ weakEnv.awake v t = true := by
  have hn : v ∈ nodes := by fin_cases v <;> simp [nodes]
  simp [awakeNodes, hn]

theorem awakeNodes_nodup (t : Time) : (awakeNodes t).Nodup :=
  (show nodes.Nodup from by decide).filter _

/-- Run all ticks first, and keep the actual objects that they release. -/
def tickBatch (t : Time) (w : World) : World × List (Obj params) :=
  (awakeNodes t).foldl (fun acc v =>
    let result := V2.D.tick weakEnv (runData 269 []) (acc.1 v) v t
    (Function.update acc.1 v result.1, acc.2 ++ (show List (Obj params) from result.2))) (w, [])

/-- Deliver a fresh object with the real handler, for the awake receiver. -/
def deliverOne (t : Time) (acc : World × List Event) (vo : Validator × Obj params) :
    World × List Event :=
  if (fgsa params unitCodec).processed (acc.1 vo.1) vo.2 then acc else
    (V2.D.World.step weakEnv (runData 269 []) acc.1 (.deliver vo.1 vo.2 t),
      acc.2 ++ [.deliver vo.1 vo.2 t])

/-- Every object is offered to every receiver before the next object. -/
def timeBatch (t : Time) (w : World) : World × List Event :=
  let ticks := tickBatch t w
  let deliveries := ticks.2.flatMap (fun o => (awakeNodes t).map (fun v => (v, o)))
  deliveries.foldl (deliverOne t) (ticks.1, (awakeNodes t).map (fun v => .tick v t))

/-- The first `steps` integer times, starting at zero. -/
def buildPrefix : Nat → World × List Event
  | 0 => (V2.D.World.init, [])
  | steps + 1 =>
      let previous := buildPrefix steps
      let batch := timeBatch (steps : Time) previous.1
      (batch.1, previous.2 ++ batch.2)

attribute [local irreducible] buildPrefix

def source : V2.D.Run Validator (fgsa params unitCodec) :=
  runData 253 (buildPrefix 254).2

/-- Append only the times strictly after the source endpoint. -/
def buildSuffixFrom (first : Nat) (start : World) : Nat → World × List Event
  | 0 => (start, [])
  | steps + 1 =>
      let previous := buildSuffixFrom first start steps
      let batch := timeBatch ((first + steps : Nat) : Time) previous.1
      (batch.1, previous.2 ++ batch.2)

def buildSuffix (steps : Nat) : World × List Event :=
  buildSuffixFrom 254 (buildPrefix 254).1 steps

def continuation : V2.D.Run Validator (fgsa params unitCodec) :=
  runData 269 (source.events ++ (buildSuffix 16).2)

theorem design_numbers :
    params.n = 4 ∧ params.Δ = 1 ∧ params.k = 2 ∧ params.R = 2 ∧
    params.K_W = 2 ∧ params.δt = 4 ∧ params.η = 0 := by decide

theorem delta_ratio : params.δt = 2 * params.R := by decide

theorem bounds : L params = 7 ∧ P params = 8 ∧ Γ params 4 = 4 ∧
    ρΓ params 4 = 26 ∧ ρ₁ params 4 = 21 ∧
    B_H2 params 4 = 277 ∧ B_H1 params 4 = 247 ∧ B_H params 4 = 247 := by decide

/-- The current W bound has the same search endpoint at row delay one. -/
theorem witness_window_bounds : kappaF params 1 = 2 ∧ betaF params 1 = 8 ∧
    B_H2F params 1 4 = 277 ∧ B_H1F params 1 4 = 247 ∧ B_HF params 1 4 = 247 := by
  decide

theorem horizons : source.horizon = 253 ∧ continuation.horizon = 269 := ⟨rfl, rfl⟩

theorem endpoint : source.horizon = recoveryStart params strongEnv + B_HF params 1 4 := by decide

theorem witness_covered : source.horizon < continuation.horizon := by decide

theorem environments : strongEnv.Δ = params.Δ ∧ weakEnv.Δ = params.Δ ∧
    strongEnv.t_GST = 0 ∧ weakEnv.t_GST = 0 := by decide

theorem honest_sets : source.honest = Finset.univ ∧
    continuation.honest = Finset.univ := ⟨rfl, rfl⟩

theorem faulty_sets : Gen.V2.Duty.faulty source = ∅ ∧ Gen.V2.Duty.faulty continuation = ∅ := by
  simp [Gen.V2.Duty.faulty, source, continuation, runData]

theorem fault_bound : (Gen.V2.Duty.faulty source).card = 0 ∧
    (Gen.V2.Duty.faulty source).card ≤ (params.n - 1) / 3 := by
  rw [faulty_sets.1]
  decide

theorem strong_awake (v : Validator) (t : Time) : strongEnv.awake v t = true := rfl

theorem weak_awake_iff (v : Validator) (t : Time) :
    weakEnv.awake v t = true ↔ t ≤ 253 ∨ v = 0 := by simp [weakEnv]

theorem awake_agreement (v : Validator) (t : Time) (ht : t ≤ source.horizon) :
    weakEnv.awake v t = strongEnv.awake v t := by
  have ht' : t ≤ 253 := ht
  simp [weakEnv, strongEnv, ht']

theorem strong_awake_set (t : Time) :
    Gen.V2.Duty.awakeHonest strongEnv source t = Finset.univ := by
  simp [Gen.V2.Duty.awakeHonest, source, runData, strongEnv]

theorem weak_awake_set_before (t : Time) (ht : t ≤ 253) :
    Gen.V2.Duty.awakeHonest weakEnv continuation t = Finset.univ := by
  simp [Gen.V2.Duty.awakeHonest, continuation, runData, weakEnv, ht]

theorem weak_awake_set_after (t : Time) (ht : 253 < t) :
    Gen.V2.Duty.awakeHonest weakEnv continuation t = {0} := by
  ext v
  simp [Gen.V2.Duty.awakeHonest, continuation, runData, weakEnv, not_le.mpr ht]

theorem awake_counts (t : Time) :
    (Gen.V2.Duty.awakeHonest strongEnv source t).card = 4 ∧
    (Gen.V2.Duty.awakeHonest weakEnv continuation t).card = if t ≤ 253 then 4 else 1 := by
  rw [strong_awake_set]
  constructor
  · decide
  · split_ifs with ht
    · rw [weak_awake_set_before t ht]; decide
    · rw [weak_awake_set_after t (lt_of_not_ge ht)]; rfl

theorem witness_participation (t : Time) (ht : source.horizon < t) :
    (Gen.V2.Duty.faulty continuation).card <
      (Gen.V2.Duty.awakeHonest weakEnv continuation t).card := by
  rw [faulty_sets.2, weak_awake_set_after t ht]
  decide

theorem strict_drop :
    (Gen.V2.Duty.awakeHonest weakEnv continuation 254).card <
      (Gen.V2.Duty.awakeHonest strongEnv source 253).card := by
  rw [weak_awake_set_after 254 (by decide), strong_awake_set]
  decide

theorem later_sleep : weakEnv.awake 1 254 = false ∧ weakEnv.awake 2 254 = false ∧
    weakEnv.awake 3 254 = false := by decide

theorem cstar (h : Time) (es : List Event) :
    V2.D.CStar (fgsaFamilies params unitCodec).fresh (runData h es) := by
  intro label hf
  cases label with
  | prop s => exact hf.elim
  | base label =>
      cases label with
      | fg => exact hf.elim
      | head s => exact Function.bijective_id

theorem linked (h : Time) (es : List Event) :
    V2.D.Linked (fgsaFamilies params unitCodec).linked (runData h es) := by
  refine ⟨4, Equiv.refl _, ?_⟩
  intro label hf
  cases label with
  | prop s => exact hf.elim
  | base label =>
      cases label with
      | head s => exact hf.elim
      | fg => exact ⟨rfl, fun _ => rfl⟩

theorem gap_positive : 4 * params.Δ ≤ (4 : Time) := by decide

theorem gap_aligned : 4 * params.Δ ∣ (4 : Time) := by decide

theorem source_gap (t : Time) (ht : strongEnv.t_GST ≤ t) (_hh : t + 4 ≤ source.horizon) :
    ∃ s, t < V2.D.proposalTime (fgsaInterface params unitCodec) s ∧
      V2.D.proposalTime (fgsaInterface params unitCodec) s ≤ t + 4 ∧
      Gen.V2.Duty.HonestSlot source (fgsaInterface params unitCodec) s := by
  refine ⟨(t / 4).toNat + 1, ?_, ?_, ?_⟩
  · change t < 4 * (((t / 4).toNat + 1 : Nat) : Int)
    have ht0 : (0 : Int) ≤ t := ht
    simp only [Time] at *
    omega
  · change 4 * (((t / 4).toNat + 1 : Nat) : Int) ≤ t + 4
    have ht0 : (0 : Int) ≤ t := ht
    simp only [Time] at *
    omega
  · exact ⟨Nat.zero_lt_succ _, Finset.mem_univ _⟩

theorem boundary_duties : SA.proposalTime params.toParams 61 = 244 ∧
    SA.gateTime params.toParams 61 = 250 ∧ SA.voteTime params.toParams 62 = 249 ∧
    SA.gateTime params.toParams 62 = 254 := by decide

/-- The delivery fold adds only deliveries at its own time. -/
theorem delivery_fold_mem (t : Time) (xs : List (Validator × Obj params))
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

theorem timeBatch_shape (t : Time) (w : World) (e : Event)
    (he : e ∈ (timeBatch t w).2) :
    e.time = t ∧ (∃ v, e = .tick v t) ∨ e.time = t ∧ ∃ v o, e = .deliver v o t := by
  rw [timeBatch, delivery_fold_mem] at he
  rcases he with ht | ⟨_, v, o, rfl⟩
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    exact Or.inl ⟨rfl, v, rfl⟩
  · exact Or.inr ⟨rfl, v, o, rfl⟩

theorem timeBatch_time (t : Time) (w : World) (e : Event)
    (he : e ∈ (timeBatch t w).2) : e.time = t :=
  (timeBatch_shape t w e he).elim And.left And.left

theorem timeBatch_no_restart (t : Time) (w : World) (v : Validator) (s : Time) :
    V2.Event.restart v s ∉ (timeBatch t w).2 := by
  intro he
  rcases timeBatch_shape t w _ he with ⟨_, u, hu⟩ | ⟨_, u, o, hu⟩ <;> cases hu

theorem nodes_complete (v : Validator) : v ∈ nodes := by
  fin_cases v <;> simp [nodes]

theorem timeBatch_tick (t : Time) (w : World) (v : Validator)
    (ha : weakEnv.awake v t = true) :
    V2.Event.tick v t ∈ (timeBatch t w).2 := by
  rw [timeBatch, delivery_fold_mem]
  exact Or.inl (List.mem_map.mpr ⟨v, (awakeNodes_mem v t).mpr ha, rfl⟩)

theorem witness_prefix_times (steps : Nat) (e : Event) (he : e ∈ (buildPrefix steps).2) :
    0 ≤ e.time ∧ e.time < steps := by
  induction steps with
  | zero => simp [buildPrefix] at he
  | succ steps ih =>
      simp only [buildPrefix] at he
      rcases List.mem_append.mp he with he | he
      · have := ih he
        simp only [Nat.cast_add, Nat.cast_one]
        simp only [Time] at *
        omega
      · rw [timeBatch_time _ _ _ he]
        exact ⟨Int.natCast_nonneg _, by simp⟩

theorem suffix_times (steps : Nat) (e : Event) (he : e ∈ (buildSuffix steps).2) :
    254 ≤ e.time ∧ e.time < 254 + steps := by
  induction steps with
  | zero => simp [buildSuffix, buildSuffixFrom] at he
  | succ steps ih =>
      change e ∈ (buildSuffix steps).2 ++
        (timeBatch (254 + steps : Nat) (buildSuffix steps).1).2 at he
      rcases List.mem_append.mp he with he | he
      · have := ih he
        simp only [Nat.cast_add, Nat.cast_one]
        simp only [Time] at *
        omega
      · rw [timeBatch_time _ _ _ he]
        simp only [Nat.cast_add, Nat.cast_one]
        simp only [Time] at *
        omega

theorem prefix_no_restart (steps : Nat) (v : Validator) (t : Time) :
    V2.Event.restart v t ∉ (buildPrefix steps).2 := by
  induction steps with
  | zero => simp [buildPrefix]
  | succ steps ih =>
      simp only [buildPrefix]
      simp only [List.mem_append, not_or]
      exact ⟨ih, timeBatch_no_restart _ _ v t⟩

theorem suffix_no_restart (steps : Nat) (v : Validator) (t : Time) :
    V2.Event.restart v t ∉ (buildSuffix steps).2 := by
  induction steps with
  | zero => simp [buildSuffix, buildSuffixFrom]
  | succ steps ih =>
      change V2.Event.restart v t ∉ (buildSuffix steps).2 ++
        (timeBatch (254 + steps : Nat) (buildSuffix steps).1).2
      simp only [List.mem_append, not_or]
      exact ⟨ih, timeBatch_no_restart _ _ v t⟩

theorem no_restart : V2.D.NoRestart source ∧ V2.D.NoRestart continuation := by
  constructor
  · intro i v t he
    exact prefix_no_restart 254 v t (List.mem_of_getElem? he)
  · intro i v t he
    have hm := List.mem_of_getElem? he
    change V2.Event.restart v t ∈ source.events ++ (buildSuffix 16).2 at hm
    exact (List.mem_append.mp hm).elim (prefix_no_restart 254 v t) (suffix_no_restart 16 v t)

theorem event_prefix : continuation.events.take source.events.length = source.events :=
  List.take_left

theorem suffix_after_endpoint (e : Event)
    (he : e ∈ continuation.events.drop source.events.length) : source.horizon < e.time := by
  change e ∈ (source.events ++ (buildSuffix 16).2).drop source.events.length at he
  rw [List.drop_left] at he
  have := (suffix_times 16 e he).1
  change 253 < e.time
  simp only [Time] at *
  omega

/-- Prove agreement without expanding the concrete event lists. -/
theorem agreement_of_suffix (es ds : List Event)
    (hds : ∀ e ∈ ds, (253 : Time) < e.time) :
    AgreesThrough₂ params unitCodec strongEnv (runData 253 es)
      weakEnv (runData 269 (es ++ ds)) 1 where
  honest := rfl
  gst := rfl
  delta := rfl
  seats := rfl
  inputs := fun _ _ _ => rfl
  awake := by
    intro v t ht
    have ht' : t ≤ 253 := ht
    simp [weakEnv, strongEnv, ht']
  events := List.take_left
  suffixTime := by
    intro e he
    change e ∈ (es ++ ds).drop es.length at he
    rw [List.drop_left] at he
    exact hds e he

theorem agreement : AgreesThrough₂ params unitCodec strongEnv source weakEnv continuation 1 := by
  apply agreement_of_suffix
  intro e he
  have htime := (suffix_times 16 e he).1
  simp only [Time] at *
  omega

theorem witness_committees :
    V2.D.CStar (fgsaFamilies params unitCodec).fresh source ∧
    V2.D.CStar (fgsaFamilies params unitCodec).fresh continuation ∧
    V2.D.Linked (fgsaFamilies params unitCodec).linked source ∧
    V2.D.Linked (fgsaFamilies params unitCodec).linked continuation :=
  ⟨cstar _ _, cstar _ _, linked _ _, linked _ _⟩

theorem recovery_awake : ∀ v ∈ source.honest, ∀ t,
    strongEnv.t_GST ≤ t → t ≤ source.horizon → strongEnv.awake v t = true :=
  fun _ _ _ _ _ => rfl

theorem prefix_tick (steps t : Nat) (ht : t < steps) (v : Validator)
    (ha : weakEnv.awake v (t : Time) = true) :
    V2.Event.tick v (t : Time) ∈ (buildPrefix steps).2 := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      simp only [buildPrefix]
      by_cases he : t = steps
      · subst t
        exact List.mem_append_right _ (timeBatch_tick _ _ v ha)
      · exact List.mem_append_left _ (ih (by omega))

theorem suffix_tick (steps t : Nat) (ht : t < steps) (v : Validator)
    (ha : weakEnv.awake v ((254 + t : Nat) : Time) = true) :
    V2.Event.tick v ((254 + t : Nat) : Time) ∈ (buildSuffix steps).2 := by
  induction steps with
  | zero => omega
  | succ steps ih =>
      change V2.Event.tick v ((254 + t : Nat) : Time) ∈ (buildSuffix steps).2 ++
        (timeBatch (254 + steps : Nat) (buildSuffix steps).1).2
      by_cases he : t = steps
      · subst t
        exact List.mem_append_right _ (timeBatch_tick _ _ v ha)
      · exact List.mem_append_left _ (ih (by omega))

theorem source_horizon_nonneg : 0 ≤ source.horizon := by decide

theorem continuation_horizon_nonneg : 0 ≤ continuation.horizon := by decide

theorem source_in_horizon (e : Event) (he : e ∈ source.events) :
    0 ≤ e.time ∧ e.time ≤ source.horizon := by
  have ht := witness_prefix_times 254 e he
  change 0 ≤ e.time ∧ e.time ≤ 253
  simp only [Time] at *
  omega

theorem continuation_in_horizon (e : Event) (he : e ∈ continuation.events) :
    0 ≤ e.time ∧ e.time ≤ continuation.horizon := by
  change e ∈ source.events ++ (buildSuffix 16).2 at he
  change 0 ≤ e.time ∧ e.time ≤ 269
  rcases List.mem_append.mp he with he | he
  · have ht := source_in_horizon e he
    change 0 ≤ e.time ∧ e.time ≤ 253 at ht
    simp only [Time] at *
    omega
  · have ht := suffix_times 16 e he
    simp only [Time] at *
    omega

theorem source_honest_only (e : Event) (_he : e ∈ source.events) :
    e.node ∈ source.honest := Finset.mem_univ _

theorem continuation_honest_only (e : Event) (_he : e ∈ continuation.events) :
    e.node ∈ continuation.honest := Finset.mem_univ _

theorem source_tick_public (v : Validator) (t : Time)
    (ht : V2.Event.tick v t ∈ source.events) : V2.PublicTime strongEnv t := by
  have hn : 0 ≤ t := (source_in_horizon _ ht).1
  exact ⟨t.toNat, by simpa [strongEnv] using (Int.toNat_of_nonneg hn).symm⟩

theorem continuation_tick_public (v : Validator) (t : Time)
    (ht : V2.Event.tick v t ∈ continuation.events) : V2.PublicTime weakEnv t := by
  have hn : 0 ≤ t := (continuation_in_horizon _ ht).1
  exact ⟨t.toNat, by simpa [weakEnv, strongEnv] using (Int.toNat_of_nonneg hn).symm⟩

theorem witness_source_tick_total (v : Validator) (_hv : v ∈ source.honest) (t : Time)
    (_hp : V2.PublicTime strongEnv t) (ht : 0 ≤ t) (hh : t ≤ source.horizon) :
    V2.Event.tick v t ∈ source.events := by
  have he : (t.toNat : Int) = t := Int.toNat_of_nonneg ht
  rw [← he]
  apply prefix_tick
  · change t ≤ 253 at hh
    simp only [Time] at *
    omega
  · rw [he]
    exact (weak_awake_iff v t).mpr (Or.inl hh)

theorem continuation_tick_total (v : Validator) (_hv : v ∈ continuation.honest) (t : Time)
    (_hp : V2.PublicTime weakEnv t) (ht : 0 ≤ t) (hh : t ≤ continuation.horizon)
    (ha : weakEnv.awake v t = true) :
    V2.Event.tick v t ∈ continuation.events := by
  change V2.Event.tick v t ∈ source.events ++ (buildSuffix 16).2
  by_cases he : t ≤ 253
  · apply List.mem_append_left
    exact witness_source_tick_total v (Finset.mem_univ _) t
      ⟨t.toNat, by simpa [strongEnv] using (Int.toNat_of_nonneg ht).symm⟩ ht he
  · apply List.mem_append_right
    have hcast : (((254 + (t - 254).toNat : Nat)) : Time) = t := by
      simp only [Time] at *
      omega
    rw [← hcast]
    apply suffix_tick
    · change t ≤ 269 at hh
      simp only [Time] at *
      omega
    · rwa [hcast]

theorem suffix_has_ticks : V2.Event.tick 0 254 ∈ continuation.events ∧
    V2.Event.tick 0 269 ∈ continuation.events := by
  constructor
  · exact continuation_tick_total 0 (Finset.mem_univ _) 254 ⟨254, rfl⟩
      (by decide) (by decide) (by decide)
  · exact continuation_tick_total 0 (Finset.mem_univ _) 269 ⟨269, rfl⟩
      (by decide) (by decide) (by decide)

theorem phase_le_two (e : Event) : e.phase ≤ 2 := by cases e <;> simp [V2.Event.phase]

theorem key_le_delivery (e : Event) (v : Validator) (o : Obj params) (t : Time)
    (ht : e.time ≤ t) : e.key ≤ (V2.Event.deliver v o t).key := by
  exact Prod.Lex.toLex_le_toLex'.mpr ⟨ht, fun _ => phase_le_two e⟩

theorem delivery_fold_sorted (t : Time) (xs : List (Validator × Obj params))
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
          exact key_le_delivery e _ _ _ (ht e he)
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact ht e he
          · obtain rfl := List.mem_singleton.mp he
            exact le_rfl

theorem timeBatch_sorted (t : Time) (w : World) :
    (timeBatch t w).2.Pairwise (fun e f => e.key ≤ f.key) := by
  apply delivery_fold_sorted
  · rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun _ _ _ => le_rfl)
      (awakeNodes_nodup t)
  · intro e he
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    exact le_rfl

theorem prefix_sorted (steps : Nat) :
    (buildPrefix steps).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction steps with
  | zero => simpa only [buildPrefix] using (List.Pairwise.nil
      (R := fun e f : Event => e.key ≤ f.key))
  | succ steps ih =>
      simp only [buildPrefix]
      rw [List.pairwise_append]
      refine ⟨ih, timeBatch_sorted _ _, ?_⟩
      intro e he f hf
      have he' := (witness_prefix_times steps e he).2
      have hf' := timeBatch_time _ _ f hf
      apply Prod.Lex.toLex_le_toLex'.mpr
      dsimp only
      rw [hf']
      exact ⟨le_of_lt he', fun h => False.elim (ne_of_lt he' h)⟩

theorem suffix_sorted (steps : Nat) :
    (buildSuffix steps).2.Pairwise (fun e f => e.key ≤ f.key) := by
  induction steps with
  | zero => exact List.Pairwise.nil
  | succ steps ih =>
      change ((buildSuffix steps).2 ++
        (timeBatch (254 + steps : Nat) (buildSuffix steps).1).2).Pairwise _
      rw [List.pairwise_append]
      refine ⟨ih, timeBatch_sorted _ _, ?_⟩
      intro e he f hf
      have he' := (suffix_times steps e he).2
      have hf' := timeBatch_time _ _ f hf
      apply Prod.Lex.toLex_le_toLex'.mpr
      dsimp only
      rw [hf']
      simp only [Nat.cast_add, Nat.cast_ofNat]
      exact ⟨le_of_lt he', fun h => False.elim (ne_of_lt he' h)⟩

theorem source_sorted : source.events.Pairwise (fun e f => e.key ≤ f.key) := prefix_sorted 254

theorem continuation_sorted : continuation.events.Pairwise (fun e f => e.key ≤ f.key) := by
  change (source.events ++ (buildSuffix 16).2).Pairwise _
  rw [List.pairwise_append]
  refine ⟨source_sorted, suffix_sorted 16, ?_⟩
  intro e he f hf
  have he' := (witness_prefix_times 254 e he).2
  have hf' := (suffix_times 16 f hf).1
  exact Prod.Lex.toLex_le_toLex'.mpr
    ⟨le_trans (le_of_lt he') hf', fun h => False.elim (ne_of_lt (lt_of_lt_of_le he' hf') h)⟩

/-- The source can be replayed with the continuation environment. -/
theorem replay_of_agreement {E E' : Generic.Env Validator}
    {s r : V2.D.Run Validator (fgsa params unitCodec)}
    (ha : AgreesThrough₂ params unitCodec E s E' r 1)
    (hh : ∀ e ∈ s.events, e.time ≤ s.horizon) {i : Nat} (hi : i ≤ s.events.length) :
    V2.D.Run.stateBefore E' r i = V2.D.Run.stateBefore E s i := by
  unfold V2.D.Run.stateBefore
  have htake : r.events.take i = s.events.take i := by
    rw [← ha.events, List.take_take, Nat.min_eq_left hi]
  rw [htake]
  apply List.foldl_ext
  intro w e he
  have ht := hh e (List.mem_of_mem_take he)
  cases e with
  | restart v t => rfl
  | deliver v o t => rfl
  | tick v t =>
      have ht' : t ≤ s.horizon := ht
      simp only [V2.D.World.step, V2.D.tick, V2.D.Run.ownSeats, ha.seats,
        ha.inputs v t ht', ha.awake v t ht']

theorem source_replay {i : Nat} (hi : i ≤ source.events.length) :
    V2.D.Run.stateBefore weakEnv continuation i = V2.D.Run.stateBefore strongEnv source i :=
  replay_of_agreement agreement (fun e he => (source_in_horizon e he).2) hi


end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- The event fold used by the generator. -/
def genFold (w : World) (es : List Event) : World :=
  es.foldl (V2.D.World.step weakEnv (runData 269 [])) w

/-- Freshness at each delivery, with the state advanced at every event. -/
def GenFresh : World → List Event → Prop
  | _, [] => True
  | w, e :: es =>
      (match e with
        | .deliver v o _ => (fgsa params unitCodec).processed (w v) o = false
        | _ => True) ∧
      GenFresh (V2.D.World.step weakEnv (runData 269 []) w e) es

theorem genFold_append (w : World) (es ds : List Event) :
    genFold w (es ++ ds) = genFold (genFold w es) ds :=
  List.foldl_append

theorem genFresh_append (w : World) (es ds : List Event) :
    GenFresh w (es ++ ds) ↔ GenFresh w es ∧ GenFresh (genFold w es) ds := by
  induction es generalizing w with
  | nil => simp [GenFresh, genFold]
  | cons e es ih =>
      simp only [List.cons_append, GenFresh, ih, genFold, List.foldl_cons]
      tauto

theorem tick_fold_replay (t : Time) (vs : List Validator)
    (w : World) (os : List (Obj params)) :
    (vs.foldl (fun acc v =>
      let result := V2.D.tick weakEnv (runData 269 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).1 =
      genFold w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w os with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.foldl_cons, List.map_cons, genFold, V2.D.World.step] at *
      exact ih _ _

theorem tickBatch_replay (t : Time) (w : World) :
    (tickBatch t w).1 = genFold w ((awakeNodes t).map (fun v => .tick v t)) :=
  tick_fold_replay t (awakeNodes t) w []

theorem tick_list_fresh (t : Time) (vs : List Validator) (w : World) :
    GenFresh w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih _⟩

theorem delivery_fold_replay_fresh (t : Time) (xs : List (Validator × Obj params))
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
        · rw [genFold_append, ← hr]
          rfl
        · rw [genFresh_append, ← hr]
          exact ⟨hf, Bool.eq_false_iff.mpr hp, trivial⟩

theorem timeBatch_replay_fresh (t : Time) (w : World) :
    (timeBatch t w).1 = genFold w (timeBatch t w).2 ∧
      GenFresh w (timeBatch t w).2 :=
  delivery_fold_replay_fresh t _ w _ (tickBatch_replay t w) (tick_list_fresh t (awakeNodes t) w)

theorem prefix_replay_fresh (steps : Nat) :
    (buildPrefix steps).1 = genFold V2.D.World.init (buildPrefix steps).2 ∧
      GenFresh V2.D.World.init (buildPrefix steps).2 := by
  induction steps with
  | zero => simp only [buildPrefix, genFold, GenFresh, List.foldl_nil, and_self]
  | succ steps ih =>
      simp only [buildPrefix]
      have hb := timeBatch_replay_fresh (steps : Time) (buildPrefix steps).1
      constructor
      · rw [genFold_append, ← ih.1]
        exact hb.1
      · rw [genFresh_append, ← ih.1]
        exact ⟨ih.2, hb.2⟩

section
private theorem suffixFrom_replay_fresh (start : World) (steps : Nat) :
    (buildSuffixFrom 254 start steps).1 = genFold start (buildSuffixFrom 254 start steps).2 ∧
      GenFresh start (buildSuffixFrom 254 start steps).2 := by
  induction steps with
  | zero => exact ⟨rfl, trivial⟩
  | succ steps ih =>
    have hb := timeBatch_replay_fresh ((254 + steps : Nat) : Time)
      (buildSuffixFrom 254 start steps).1
    constructor
    · change (timeBatch (254 + steps : Nat) (buildSuffixFrom 254 start steps).1).1 =
        genFold start ((buildSuffixFrom 254 start steps).2 ++
          (timeBatch (254 + steps : Nat) (buildSuffixFrom 254 start steps).1).2)
      rw [genFold_append, ← ih.1]
      exact hb.1
    · change GenFresh start ((buildSuffixFrom 254 start steps).2 ++
        (timeBatch (254 + steps : Nat) (buildSuffixFrom 254 start steps).1).2)
      rw [genFresh_append, ← ih.1]
      exact ⟨ih.2, hb.2⟩

theorem suffix_replay_fresh (steps : Nat) :
    (buildSuffix steps).1 = genFold (buildPrefix 254).1 (buildSuffix steps).2 ∧
      GenFresh (buildPrefix 254).1 (buildSuffix steps).2 :=
  suffixFrom_replay_fresh (buildPrefix 254).1 steps

end

theorem genFresh_get (w : World) (es : List Event) (hf : GenFresh w es)
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

theorem genFold_runData (w : World) (h : Time) (schedule es : List Event) :
    genFold w es = es.foldl (V2.D.World.step weakEnv (runData h schedule)) w := rfl

theorem genFresh_join (w w' : World) (es ds : List Event)
    (hr : w' = genFold w es) (he : GenFresh w es) (hd : GenFresh w' ds) :
    GenFresh w (es ++ ds) := by
  rw [genFresh_append, ← hr]
  exact ⟨he, hd⟩

theorem runData_fresh (h : Time) (es : List Event)
    (hf : GenFresh V2.D.World.init es)
    (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : es[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).processed
      (V2.D.Run.stateBefore weakEnv (runData h es) i v) o = false := by
  exact genFresh_get V2.D.World.init es hf i v o t he

theorem continuation_events_eq :
    continuation.events = (buildPrefix 254).2 ++ (buildSuffix 16).2 := rfl

attribute [irreducible] GenFresh

theorem continuation_genFresh : GenFresh V2.D.World.init continuation.events :=
  Eq.mpr (congrArg (GenFresh V2.D.World.init) continuation_events_eq)
    (genFresh_join V2.D.World.init (buildPrefix 254).1 (buildPrefix 254).2 (buildSuffix 16).2
      (prefix_replay_fresh 254).1 (prefix_replay_fresh 254).2 (suffix_replay_fresh 16).2)

set_option maxRecDepth 4096 in
theorem continuation_fresh (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : continuation.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).processed (V2.D.Run.stateBefore weakEnv continuation i v) o = false :=
  runData_fresh 269 _ continuation_genFresh i v o t he

theorem source_fresh (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : source.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).processed (V2.D.Run.stateBefore strongEnv source i v) o = false := by
  have hi : i ≤ source.events.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
  rw [← source_replay hi]
  apply continuation_fresh
  change (source.events ++ (buildSuffix 16).2)[i]? = some (.deliver v o t)
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1]
  exact he

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- A tick and its release, stated with the event prefix that it reads. -/
def GenEmits (w : World) (es : List Event) (v : Validator) (o : Obj params) (t : Time) : Prop :=
  ∃ pre post, es = pre ++ .tick v t :: post ∧
    o ∈ (V2.D.tick weakEnv (runData 269 []) (genFold w pre v) v t).2

/-- Every direct delivery has a same-time emission in the same trace. -/
def GenOrigin (w : World) (es : List Event) : Prop :=
  ∀ v o t, V2.Event.deliver v o t ∈ es → ∃ u, GenEmits w es u o t

theorem genEmits_cons (w : World) (e : Event) (es : List Event)
    (v : Validator) (o : Obj params) (t : Time)
    (h : GenEmits (V2.D.World.step weakEnv (runData 269 []) w e) es v o t) :
    GenEmits w (e :: es) v o t := by
  obtain ⟨pre, post, he, ho⟩ := h
  exact ⟨e :: pre, post, congrArg (e :: ·) he, ho⟩

theorem genEmits_append_left (w : World) (es ds : List Event)
    (v : Validator) (o : Obj params) (t : Time) (h : GenEmits w es v o t) :
    GenEmits w (es ++ ds) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := h
  exact ⟨pre, post ++ ds, by simp only [List.append_assoc, List.cons_append], ho⟩

theorem genEmits_append_right (w : World) (es ds : List Event)
    (v : Validator) (o : Obj params) (t : Time) (h : GenEmits (genFold w es) ds v o t) :
    GenEmits w (es ++ ds) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := h
  refine ⟨es ++ pre, post, (List.append_assoc ..).symm, ?_⟩
  rwa [genFold_append]

theorem genOrigin_append (w w' : World) (es ds : List Event)
    (hr : w' = genFold w es) (he : GenOrigin w es) (hd : GenOrigin w' ds) :
    GenOrigin w (es ++ ds) := by
  intro v o t hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨u, hu⟩ := he v o t hm
    exact ⟨u, genEmits_append_left w es ds u o t hu⟩
  · obtain ⟨u, hu⟩ := hd v o t hm
    rw [hr] at hu
    exact ⟨u, genEmits_append_right w es ds u o t hu⟩

theorem tick_fold_origin (t : Time) (vs : List Validator)
    (w : World) (os : List (Obj params)) (o : Obj params)
    (ho : o ∈ (vs.foldl (fun acc v =>
      let result := V2.D.tick weakEnv (runData 269 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2) :
    o ∈ os ∨ ∃ v, GenEmits w (vs.map (fun v => .tick v t)) v o t := by
  induction vs generalizing w os with
  | nil => exact Or.inl ho
  | cons v vs ih =>
      rcases ih _ _ ho with hm | ⟨u, hu⟩
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr ⟨v, [], vs.map (fun u => .tick u t), rfl, hm⟩
      · exact Or.inr ⟨u, genEmits_cons w (.tick v t) _ u o t hu⟩

theorem tickBatch_origin (t : Time) (w : World) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) :
    ∃ v, GenEmits w ((awakeNodes t).map (fun v => .tick v t)) v o t := by
  rcases tick_fold_origin t (awakeNodes t) w [] o ho with h | h
  · exact (List.not_mem_nil h).elim
  · exact h

/-- Deliveries form a sublist of the offers. This keeps the release order. -/
theorem delivery_fold_sublist (t : Time) (xs : List (Validator × Obj params))
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

theorem timeBatch_block (t : Time) (w : World) :
    ∃ ds, (timeBatch t w).2 = (awakeNodes t).map (fun v => .tick v t) ++ ds ∧
      ds.Sublist ((tickBatch t w).2.flatMap
        (fun o => (awakeNodes t).map (fun v => .deliver v o t))) := by
  obtain ⟨ds, he, hs⟩ := delivery_fold_sublist t
    ((tickBatch t w).2.flatMap (fun o => (awakeNodes t).map (fun v => (v, o))))
    ((tickBatch t w).1, (awakeNodes t).map (fun v => .tick v t))
  refine ⟨ds, he, ?_⟩
  simp only [List.map_flatMap, List.map_map, Function.comp_def] at hs
  exact hs

theorem prefix_blocks (steps : Nat) :
    (buildPrefix steps).2 = (List.range steps).flatMap
      (fun (s : Nat) => (timeBatch (s : Time) (buildPrefix s).1).2) := by
  induction steps with
  | zero => simp [buildPrefix]
  | succ steps ih =>
      rw [buildPrefix]
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]

theorem suffix_blocks (steps : Nat) :
    (buildSuffix steps).2 = (List.range steps).flatMap
      (fun s => (timeBatch ((254 + s : Nat) : Time) (buildSuffix s).1).2) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      change (buildSuffix steps).2 ++
        (timeBatch (254 + steps : Nat) (buildSuffix steps).1).2 = _
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih]

theorem timeBatch_origin (t : Time) (w : World) : GenOrigin w (timeBatch t w).2 := by
  obtain ⟨ds, he, hs⟩ := timeBatch_block t w
  intro v o s hm
  rw [he] at hm ⊢
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
    cases hu
  · obtain ⟨o', ho', hv⟩ := List.mem_flatMap.mp (hs.subset hm)
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
    cases hu
    obtain ⟨u, hu⟩ := tickBatch_origin t w o ho'
    exact ⟨u, genEmits_append_left w _ ds u o t hu⟩

theorem prefix_origin (steps : Nat) : GenOrigin V2.D.World.init (buildPrefix steps).2 := by
  induction steps with
  | zero => simp [buildPrefix, GenOrigin]
  | succ steps ih =>
      rw [buildPrefix]
      exact genOrigin_append _ _ _ _ (prefix_replay_fresh steps).1 ih (timeBatch_origin _ _)

theorem suffix_origin (steps : Nat) : GenOrigin (buildPrefix 254).1 (buildSuffix steps).2 := by
  induction steps with
  | zero => intro v o t hm; exact (List.not_mem_nil hm).elim
  | succ steps ih =>
      exact genOrigin_append _ _ _ _ (suffix_replay_fresh steps).1 ih (timeBatch_origin _ _)

/-- Relate the trace witness to the engine's indexed emission predicate. -/
theorem genEmits_runData (h : Time) (es : List Event) (v : Validator) (o : Obj params) (t : Time)
    (he : GenEmits V2.D.World.init es v o t) : V2.D.Run.emits weakEnv (runData h es) v o t := by
  obtain ⟨pre, post, rfl, ho⟩ := he
  have hi : (runData h (pre ++ .tick v t :: post)).events[pre.length]? =
      some (.tick v t) := by simp [runData]
  refine ⟨pre.length, hi, ?_⟩
  rw [V2.D.Run.emitsAt, hi]
  simp only [V2.D.Run.stateBefore, runData, List.take_left']
  exact ho

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- Every emitted object is signed with a seat of its emitter. -/
theorem gen_tick_holder (st : Node params) (v : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick weakEnv (runData 269 []) st v t).2) :
    V2.D.Run.holder (runData 269 []) o.auth = some v := by
  change o ∈ (if weakEnv.awake v t then
    (duties params t).flatMap (fun l =>
      ((runData 269 []).ownSeats (RunDuty.signLabel l) v).filterMap (fun i =>
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

theorem genOrigin_unforgeable (h : Time) (es : List Event) (horigin : GenOrigin V2.D.World.init es)
    (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes (runData h es) v o t) (u : Validator)
    (hu : V2.D.Run.holder (runData h es) o.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits weakEnv (runData h es) u o t' := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨x, hx⟩ := horigin v o t (List.mem_of_getElem? hi)
  have hemit := genEmits_runData h es x o t hx
  obtain ⟨pre, post, _, ho⟩ := hx
  have hholder := gen_tick_holder (genFold V2.D.World.init pre x) x t o ho
  have hux : u = x := Option.some.inj (hu.symm.trans hholder)
  exact ⟨t, le_rfl, hux.symm ▸ hemit⟩

theorem continuation_genOrigin : GenOrigin V2.D.World.init continuation.events :=
  Eq.mpr (congrArg (GenOrigin V2.D.World.init) continuation_events_eq)
    (genOrigin_append V2.D.World.init (buildPrefix 254).1 (buildPrefix 254).2 (buildSuffix 16).2
      (prefix_replay_fresh 254).1 (prefix_origin 254) (suffix_origin 16))

theorem continuation_unforgeable (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes continuation v o t) (u : Validator) (_hu : u ∈ continuation.honest)
    (hh : V2.D.Run.holder continuation o.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits weakEnv continuation u o t' :=
  genOrigin_unforgeable 269 _ continuation_genOrigin v o t hp u hh

/-- On the source, a tick and its releases agree in both environments. -/
theorem source_emits_weak_to_strong (v : Validator) (o : Obj params) (t : Time)
    (he : V2.D.Run.emits weakEnv source v o t) : V2.D.Run.emits strongEnv source v o t := by
  obtain ⟨i, hi, ho⟩ := he
  have ht := (source_in_horizon _ (List.mem_of_getElem? hi)).2
  have hstate : V2.D.Run.stateBefore weakEnv source i
    = V2.D.Run.stateBefore strongEnv source i := by
    have hsa : AgreesThrough₂ params unitCodec strongEnv source weakEnv source 1 :=
      { honest := rfl, gst := rfl, delta := rfl, seats := rfl, inputs := fun _ _ _ => rfl,
        awake := fun v t ht => awake_agreement v t ht, events := by simp,
        suffixTime := by simp }
    exact replay_of_agreement hsa (fun e he => (source_in_horizon e he).2)
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hi).1)
  refine ⟨i, hi, ?_⟩
  simp only [V2.D.Run.emitsAt, hi] at ho ⊢
  rw [hstate] at ho
  have hawake := awake_agreement v t ht
  simpa only [V2.D.tick, hawake] using ho

theorem source_unforgeable (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes source v o t) (u : Validator) (_hu : u ∈ source.honest)
    (hh : V2.D.Run.holder source o.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits strongEnv source u o t' := by
  obtain ⟨t', ht', he⟩ := genOrigin_unforgeable 253 (buildPrefix 254).2
    (prefix_origin 254) v o t hp u hh
  exact ⟨t', ht', source_emits_weak_to_strong u o t' he⟩

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- Without gossip, a tick releases at most one object for each duty seat. -/
theorem tick_nodup_without_gossip {In V : Type} [DecidableEq V]
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

theorem gen_tick_nodup (st : Node params) (v : Validator) (t : Time) :
    (V2.D.tick weakEnv (runData 269 []) st v t).2.Nodup :=
  tick_nodup_without_gossip (fgsa params unitCodec) weakEnv (runData 269 []) st v t rfl
    (fgsa_dutiesInjectiveAt t)

theorem tick_fold_nodup (t : Time) (vs : List Validator) (hn : vs.Nodup)
    (w : World) (os : List (Obj params)) (ho : os.Nodup)
    (hh : ∀ o ∈ os, ∀ v ∈ vs, V2.D.Run.holder (runData 269 []) o.auth ≠ some v) :
    (vs.foldl (fun acc v =>
      let result := V2.D.tick weakEnv (runData 269 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)).2.Nodup := by
  induction vs generalizing w os with
  | nil => exact ho
  | cons v vs ih =>
      rw [List.nodup_cons] at hn
      rw [List.foldl_cons]
      apply ih hn.2
      · apply ho.append (gen_tick_nodup (w v) v t)
        intro o hos hot
        exact hh o hos v (List.mem_cons_self ..) (gen_tick_holder (w v) v t o hot)
      · intro o hom u hum
        rcases List.mem_append.mp hom with hom | hom
        · exact hh o hom u (List.mem_cons_of_mem _ hum)
        · rw [gen_tick_holder (w v) v t o hom]
          intro he
          exact hn.1 (Option.some.inj he ▸ hum)

theorem tickBatch_nodup (t : Time) (w : World) : (tickBatch t w).2.Nodup :=
  tick_fold_nodup t (awakeNodes t) (awakeNodes_nodup t) w [] List.nodup_nil (by simp)

theorem timeBatch_nodup (t : Time) (w : World) : (timeBatch t w).2.Nodup := by
  obtain ⟨ds, he, hs⟩ := timeBatch_block t w
  rw [he]
  apply List.Nodup.append
  · exact (awakeNodes_nodup t).map (by intro v u h; cases h; rfl)
  · apply List.Nodup.sublist hs
    change ((tickBatch t w).2.flatMap (fun (o : Obj params) =>
      (awakeNodes t).map (fun v =>
        (V2.Event.deliver v o t : V2.Event Validator (Obj params))))).Nodup
    rw [List.nodup_flatMap]
    constructor
    · intro o _
      exact (awakeNodes_nodup t).map (by intro v u h; cases h; rfl)
    · apply (tickBatch_nodup t w).imp
      intro o o' hne e he he'
      obtain ⟨v, _, hv⟩ := List.mem_map.mp he
      obtain ⟨u, _, hu⟩ := List.mem_map.mp he'
      exact hne (V2.Event.deliver.inj (hv.trans hu.symm)).2.1
  · intro e he hd
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    obtain ⟨o, _, ho⟩ := List.mem_flatMap.mp (hs.subset hd)
    obtain ⟨u, _, hu⟩ := List.mem_map.mp ho
    cases hu

theorem prefix_nodup (steps : Nat) : (buildPrefix steps).2.Nodup := by
  induction steps with
  | zero => simp [buildPrefix]
  | succ steps ih =>
      rw [buildPrefix]
      apply ih.append (timeBatch_nodup _ _)
      intro e he hb
      have hlt := (witness_prefix_times steps e he).2
      rw [timeBatch_time _ _ _ hb] at hlt
      exact (lt_irrefl _ hlt)

theorem suffix_nodup (steps : Nat) : (buildSuffix steps).2.Nodup := by
  induction steps with
  | zero => exact List.nodup_nil
  | succ steps ih =>
      apply ih.append (timeBatch_nodup _ _)
      intro e he hb
      have hlt := (suffix_times steps e he).2
      rw [timeBatch_time _ _ _ hb] at hlt
      simp only [Nat.cast_add, Nat.cast_ofNat] at hlt
      exact (lt_irrefl _ hlt)

theorem source_nodup : source.events.Nodup := prefix_nodup 254

theorem continuation_nodup : continuation.events.Nodup := by
  apply source_nodup.append (suffix_nodup 16)
  intro e he hd
  have hlt := (witness_prefix_times 254 e he).2
  have hge := (suffix_times 16 e hd).1
  exact (not_lt_of_ge hge hlt)

theorem witness_source_schedule : V2.D.ScheduleWellFormed strongEnv source where
  horizon_nonneg := source_horizon_nonneg
  sorted := source_sorted
  nodup := source_nodup
  in_horizon := source_in_horizon
  honest_only := source_honest_only
  tick_public := source_tick_public
  tick_total := fun v hv t hp ht hh _ => witness_source_tick_total v hv t hp ht hh

theorem continuation_schedule : V2.D.ScheduleWellFormed weakEnv continuation where
  horizon_nonneg := continuation_horizon_nonneg
  sorted := continuation_sorted
  nodup := continuation_nodup
  in_horizon := continuation_in_horizon
  honest_only := continuation_honest_only
  tick_public := continuation_tick_public
  tick_total := continuation_tick_total

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

open AvailableChain.SimplexFG

/-- Indexed replay for any run made from the generator's static data. -/
theorem runData_stateBefore (h : Time) (es : List Event) (i : Nat) :
    V2.D.Run.stateBefore weakEnv (runData h es) i = genFold V2.D.World.init (es.take i) := rfl

theorem genOrigin_runData (h : Time) (es : List Event) (ho : GenOrigin V2.D.World.init es)
    (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes (runData h es) v o t) :
    ∃ u, u ∈ (runData h es).honest ∧ V2.D.Run.emits weakEnv (runData h es) u o t := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨u, hu⟩ := ho v o t (List.mem_of_getElem? hi)
  exact ⟨u, Finset.mem_univ _, genEmits_runData h es u o t hu⟩

theorem source_delivery_origin (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes source v o t) :
    ∃ u, u ∈ source.honest ∧ V2.D.Run.emits strongEnv source u o t := by
  obtain ⟨u, hu, he⟩ := genOrigin_runData 253 (buildPrefix 254).2 (prefix_origin 254) v o t hp
  exact ⟨u, hu, source_emits_weak_to_strong u o t he⟩

theorem continuation_delivery_origin (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes continuation v o t) :
    ∃ u, u ∈ continuation.honest ∧ V2.D.Run.emits weakEnv continuation u o t :=
  genOrigin_runData 269 _ continuation_genOrigin v o t hp

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

open AvailableChain.SimplexFG

theorem gen_nonproposal_deps (st : Node params) (o : Obj params)
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
theorem gen_derive_positive (B : FGBlock (Fin params.n)) :
    1 ≤ (heightView params B).h :=
  (Window.windowHeightLaws params params.K_W params.kWLarge).one_le_h B

/-- Every released row passes the row-body wire check. -/
theorem gen_attest_valid (st : State params.n) (record : RecordOnce)
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
  have hpos : 1 ≤ h := heh ▸ gen_derive_positive C
  rw [← hp, he]
  change (decide (1 ≤ h) &&
    ((finality_pair record.toRecord (fgInputs params st).2).filter
      (fun fp => decide (fp.height < h)) |>.map (fun fp => decide (fp.height < h))).getD true)
        = true
  cases hfp : finality_pair record.toRecord (fgInputs params st).2 with
  | none => simp [hpos, Option.filter]
  | some fp =>
      by_cases hlt : fp.height < h <;> simp [hpos, Option.filter, hlt]

/-- Describe each release without evaluating the state or its codec data. -/
theorem gen_tick_seat (st : Node params) (v : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick weakEnv (runData 269 []) st v t).2) :
    ∃ l i m, o = ⟨.seat (RunDuty.signLabel l) i, m⟩ ∧ l ∈ duties params t ∧
      (fgsa params unitCodec).act ((fgsa params unitCodec).clock st t) l () = some m := by
  change o ∈ (if weakEnv.awake v t then
    (duties params t).flatMap (fun l =>
      ((runData 269 []).ownSeats (RunDuty.signLabel l) v).filterMap (fun i =>
        ((fgsa params unitCodec).act ((fgsa params unitCodec).clock st t) l ()).map
          (fun m => ⟨.seat (RunDuty.signLabel l) i, m⟩))) ++ [] else []) at ho
  split at ho
  · rw [List.append_nil] at ho
    obtain ⟨l, hl, ho⟩ := List.mem_flatMap.mp ho
    obtain ⟨i, _, hm⟩ := List.mem_filterMap.mp ho
    obtain ⟨m, ha, rfl⟩ := Option.map_eq_some_iff.mp hm
    exact ⟨l, i, m, rfl, hl, ha⟩
  · exact (List.not_mem_nil ho).elim

/-- The wire check for non-proposal releases. WeakContinuationW1 proves proposal wire. -/
theorem gen_tick_nonproposal_wire (st : Node params) (v : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick weakEnv (runData 269 []) st v t).2)
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨l, i, m, rfl, _, ha⟩ := gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
      change (if joinedNow params (FGSA.clock params st.st t) then
        some (Msg.head (headVote params (FGSA.clock params st.st t) s).root)
        else none) = some m at ha
      split at ha <;> try contradiction
      have he : .head (headVote params (FGSA.clock params st.st t) s).root = m := Option.some.inj ha
      subst m
      rfl
  | fgAction r =>
      change (attest params (FGSA.clock params st.st t) st.record
        ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      exact gen_attest_valid _ _ _ _ hb
  | propAction s =>
      change (if joinedNow params (FGSA.clock params st.st t) then
        (propose params (FGSA.clock params st.st t) s).map (withApp params 0)
        else none) = some m at ha
      split at ha <;> try contradiction
      unfold propose at ha
      split at ha
      · cases ha
      · simp only [Option.map_map] at ha
        obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.mp ha
        exact (hn _ rfl).elim

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- Each offer either creates a delivery or finds the object processed at
an event prefix. This lemma does not assert acceptance of a delivery. -/
theorem delivery_fold_offered (t : Time) (xs : List (Validator × Obj params))
    (w : World) (acc : World × List Event)
    (hr : acc.1 = genFold w acc.2) (hf : GenFresh w acc.2)
    (v : Validator) (o : Obj params) (hm : (v, o) ∈ xs) :
    V2.Event.deliver v o t ∈ (xs.foldl (deliverOne t) acc).2 ∨
      ∃ pre post, (xs.foldl (deliverOne t) acc).2 = pre ++ post ∧
        (fgsa params unitCodec).processed (genFold w pre v) o = true := by
  induction xs generalizing acc with
  | nil => exact (List.not_mem_nil hm).elim
  | cons x xs ih =>
      have hnext : (deliverOne t acc x).1 = genFold w (deliverOne t acc x).2 ∧
          GenFresh w (deliverOne t acc x).2 :=
        delivery_fold_replay_fresh t [x] w acc hr hf
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hm with he | hm
      · subst x
        by_cases hp : (fgsa params unitCodec).processed (acc.1 v) o = true
        · obtain ⟨ds, he, _⟩ := delivery_fold_sublist t xs (deliverOne t acc (v, o))
          right
          refine ⟨acc.2, ds, ?_, ?_⟩
          · simpa only [deliverOne, hp, ↓reduceIte] using he
          · rwa [← hr]
        · left
          apply (delivery_fold_mem t xs (deliverOne t acc (v, o)) (.deliver v o t)).2
          left
          simp only [deliverOne, hp, Bool.false_eq_true, ↓reduceIte]
          exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact ih _ hnext.1 hnext.2 hm

theorem timeBatch_offered (t : Time) (w : World) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) (ha : weakEnv.awake v t = true) :
    V2.Event.deliver v o t ∈ (timeBatch t w).2 ∨
      ∃ pre post, (timeBatch t w).2 = pre ++ post ∧
        (fgsa params unitCodec).processed (genFold w pre v) o = true := by
  apply delivery_fold_offered t _ w _ (tickBatch_replay t w) (tick_list_fresh t (awakeNodes t) w)
  exact List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨v, (awakeNodes_mem v t).mpr ha, rfl⟩⟩

/-- Wire validity for the HEAD and row part of a trace with emission origin. -/
theorem genOrigin_nonproposal_wire (w : World) (es : List Event) (horigin : GenOrigin w es)
    (v : Validator) (o : Obj params) (t : Time) (hm : V2.Event.deliver v o t ∈ es)
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨u, pre, post, _, ho⟩ := horigin v o t hm
  exact gen_tick_nonproposal_wire (genFold w pre u) u t o ho hn

theorem source_nonproposal_wire (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : source.events[i]? = some (.deliver v o t))
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa params unitCodec).wellFormed o = true :=
  genOrigin_nonproposal_wire V2.D.World.init _ (prefix_origin 254) v o t
    (List.mem_of_getElem? he) hn

theorem continuation_nonproposal_wire (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : continuation.events[i]? = some (.deliver v o t))
    (hn : ∀ b, o.payload ≠ .proposal b) :
    (fgsa params unitCodec).wellFormed o = true :=
  genOrigin_nonproposal_wire V2.D.World.init _ continuation_genOrigin v o t
    (List.mem_of_getElem? he) hn

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- A row that is already in the pool does not change the store. -/
theorem i7_admitRow_duplicate (st : State params.n) (i : Fin params.n)
    (body : RowPayload)
    (h : (⟨.seat .fg i, body⟩ : RowWire params.n) ∈ st.rowPool) :
    admitRow params st ⟨.seat .fg i, body⟩ = st := by
  simp [admitRow, RowWire.decode?, h]

/-- The clock keeps both lists used by H. -/
theorem i7_clock_fields (st : State params.n) (t : Time) :
    (FGSA.clock params st t).proposals = st.proposals ∧
      (FGSA.clock params st t).rowPool = st.rowPool := by
  have hn (st : State params.n) : (normalizeS st).proposals = st.proposals ∧
      (normalizeS st).rowPool = st.rowPool := by
    unfold normalizeS
    split <;> exact ⟨rfl, rfl⟩
  have hg (st : State params.n) (s : Slot) :
      (gateStep params st s).proposals = st.proposals ∧
        (gateStep params st s).rowPool = st.rowPool := by
    exact ⟨gateStep_proposals params st s, gateStep_rowPool params st s⟩
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

theorem i7_clock_proposals (st : State params.n) (t : Time) :
    (FGSA.clock params st t).proposals = st.proposals := (i7_clock_fields st t).1

theorem i7_clock_rowPool (st : State params.n) (t : Time) :
    (FGSA.clock params st t).rowPool = st.rowPool := (i7_clock_fields st t).2

theorem i7_reconcile_fields (st : State params.n) :
    (reconcile st).proposals = st.proposals ∧ (reconcile st).rowPool = st.rowPool := by
  unfold reconcile normalizeS
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

theorem i7_admitRow_eq (st : State params.n) (a : RowWire params.n) :
    admitRow params st a = st ∨
      admitRow params st a = { st with rowPool := st.rowPool ++ [a] } := by
  unfold admitRow
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inl rfl

theorem i7_foldl_admitRow_eq (rows : List (RowWire params.n)) (st : State params.n) :
    ∃ pool, rows.foldl (admitRow params) st = { st with rowPool := pool } ∧
      st.rowPool ⊆ pool := by
  induction rows generalizing st with
  | nil => exact ⟨st.rowPool, rfl, List.Subset.refl _⟩
  | cons a rows ih =>
    rw [List.foldl_cons]
    rcases i7_admitRow_eq st a with he | he
    · rw [he]; exact ih st
    · rw [he]
      obtain ⟨pool, hp, hpre⟩ := ih { st with rowPool := st.rowPool ++ [a] }
      exact ⟨pool, hp, fun _ hm => hpre (List.mem_append_left _ hm)⟩

theorem i7_tick_st (st : Node params) (v : Validator) (t : Time) :
    (V2.D.tick weakEnv (runData 269 []) st v t).1.st = FGSA.clock params st.st t := by
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
theorem gen_proposalRows_origin (P : RowWire params.n → Prop) (st : State params.n)
    (H : Block) (hp : ∀ a ∈ st.rowPool, P a) (hs : GenStoredRows P st) :
    ∀ a ∈ proposalRows params st H, P a := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin params st (st.slot params) H a ha with
    hm | ⟨o, ho, s, b, hd, hm⟩
  · exact hp a hm
  · exact hs o ho s b hd a hm

/-- The clock keeps the stored proposals. -/
theorem gen_storedRows_clock (P : RowWire params.n → Prop) (st : State params.n)
    (t : Time) (hs : GenStoredRows P st) : GenStoredRows P (FGSA.clock params st t) := by
  simpa only [GenStoredRows, i7_clock_proposals] using hs

/-- A row fold keeps the stored proposals. -/
theorem gen_storedRows_fold (P : RowWire params.n → Prop) (st : State params.n)
    (rows : List (RowWire params.n)) (hs : GenStoredRows P st) :
    GenStoredRows P (rows.foldl (admitRow params) st) := by
  obtain ⟨pool, he, _⟩ := i7_foldl_admitRow_eq rows st
  rw [he]
  exact hs

/-- A delivery adds only its own proposal to the stored proposals. -/
theorem gen_storedRows_process (P : RowWire params.n → Prop) (st : State params.n)
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
      rcases i7_admitRow_eq st ⟨(toWire params o).auth, body⟩ with he | he <;>
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
          · apply gen_storedRows_fold
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
            · simpa only [GenStoredRows, (i7_reconcile_fields _).1] using hs'
          · exact hs

/-- A delivery only adds to the row pool. -/
theorem gen_process_pool_mono (st : State params.n) (o : Obj params) :
    st.rowPool ⊆ (FGSA.process params st (toWire params o)).rowPool :=
by
  unfold FGSA.process
  split
  · exact List.Subset.refl _
  · rcases i7_admitRow_eq st _ with he | he
    · rw [he]
    · rw [he]; exact fun _ hm => List.mem_append_left _ hm
  · unfold admitBlock
    split
    · exact List.Subset.refl _
    · split
      · exact List.Subset.refl _
      · split
        · obtain ⟨pool, he, hp⟩ := i7_foldl_admitRow_eq _ _
          rw [he]
          dsimp only at hp ⊢
          split at hp
          · exact hp
          · rwa [(i7_reconcile_fields _).2] at hp
        · exact List.Subset.refl _
  · exact List.Subset.refl _

/-- The invariant needed at the only proposer, node zero. -/
def GenPoolWitness (w : World) : Prop :=
  GenStoredRows (fun a => a ∈ (w 0).st.rowPool) (w 0).st

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- Every generated proposal selects its rows at node zero. -/
theorem gen_tick_proposal_rows (st : Node params) (v : Validator) (t : Time)
    (o : Obj params) (ho : o ∈ (V2.D.tick weakEnv (runData 269 []) st v t).2)
    (b : NamedProposal params.n)
    (he : o.payload = .proposal b) :
    v = 0 ∧ ∃ H, b.rows = proposalRows params (FGSA.clock params st.st t) H := by
  have hh := gen_tick_holder st v t o ho
  obtain ⟨l, i, m, rfl, _, ha⟩ := gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
    change (if joinedNow params (FGSA.clock params st.st t) then
      some (Msg.head (headVote params (FGSA.clock params st.st t) s).root)
      else none) = some m at ha
    split at ha <;> try contradiction
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
    have hv : v = 0 := (Option.some.inj hh).symm
    change (if joinedNow params (FGSA.clock params st.st t) then
      (propose params (FGSA.clock params st.st t) s).map (withApp params 0)
      else none) = some m at ha
    split at ha <;> try contradiction
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      cases he
      exact ⟨hv, _, rfl⟩

/-- Each tick keeps both fields used by the invariant. -/
theorem gen_tick_pool_fields (w : World) (v : Validator) (t : Time) (u : Validator) :
    let w' := Function.update w v (V2.D.tick weakEnv (runData 269 []) (w v) v t).1
    (w' u).st.rowPool = (w u).st.rowPool ∧
      (w' u).st.proposals = (w u).st.proposals := by
  dsimp only
  by_cases hu : u = v
  · subst u
    rw [Function.update_self]
    have he := i7_tick_st (w v) v t
    exact ⟨(congrArg State.rowPool he).trans (i7_clock_rowPool _ _),
      (congrArg State.proposals he).trans (i7_clock_proposals _ _)⟩
  · rw [Function.update_of_ne hu]
    exact ⟨rfl, rfl⟩

/-- The invariant holds throughout the tick fold, and covers every released proposal. -/
theorem gen_tick_fold_pool (t : Time) (vs : List Validator) (w : World)
    (os : List (Obj params)) (hw : GenPoolWitness w)
    (ho : ∀ o ∈ os, ∀ b, o.payload = .proposal b →
      ∀ a ∈ b.rows, a ∈ (w 0).st.rowPool) :
    let result := vs.foldl (fun acc v =>
      let result := V2.D.tick weakEnv (runData 269 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)
    GenPoolWitness result.1 ∧
      ∀ o ∈ result.2, ∀ b, o.payload = .proposal b →
        ∀ a ∈ b.rows, a ∈ (result.1 0).st.rowPool := by
  induction vs generalizing w os with
  | nil => exact ⟨hw, ho⟩
  | cons v vs ih =>
    let w' := Function.update w v (V2.D.tick weakEnv (runData 269 []) (w v) v t).1
    have hf := gen_tick_pool_fields w v t 0
    have hw' : GenPoolWitness w' := by
      simpa only [GenPoolWitness, GenStoredRows, w', hf.1, hf.2] using hw
    apply ih w' _ hw'
    intro o hm b he a ha
    rw [hf.1]
    rcases List.mem_append.mp hm with hm | hm
    · exact ho o hm b he a ha
    · obtain ⟨hv, H, hrows⟩ := gen_tick_proposal_rows (w v) v t o hm b he
      subst v
      rw [hrows] at ha
      have hs := gen_storedRows_clock _ (w 0).st t hw
      exact gen_proposalRows_origin _ _ H
        (fun a ha => (i7_clock_rowPool (w 0).st t) ▸ ha) hs a ha

/-- A delivery to the proposer preserves its stored-row invariant. -/
theorem gen_deliver_pool (t : Time) (acc : World × List Event) (vo : Validator × Obj params)
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
    · have hs := gen_storedRows_process _ (acc.1 0).st vo.2 hw ho
      have hp := gen_process_pool_mono (acc.1 0).st vo.2
      simp only [V2.D.World.step, hv, Function.update_self]
      refine ⟨?_, hp⟩
      intro w hm s b hd a ha
      exact hp (hs w hm s b hd a ha)
    · simpa only [GenPoolWitness, V2.D.World.step, Function.update_of_ne (Ne.symm hv)] using
        (show GenPoolWitness acc.1 ∧ (acc.1 0).st.rowPool ⊆ (acc.1 0).st.rowPool from
          ⟨hw, List.Subset.refl _⟩)

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- All offers have rows already in the proposer's pool, which only grows. -/
theorem gen_delivery_fold_pool (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (hw : GenPoolWitness acc.1)
    (ho : ∀ vo ∈ xs, ∀ b, vo.2.payload = .proposal b →
      ∀ a ∈ b.rows, a ∈ (acc.1 0).st.rowPool) :
    GenPoolWitness (xs.foldl (deliverOne t) acc).1 := by
  induction xs generalizing acc with
  | nil => exact hw
  | cons vo xs ih =>
    obtain ⟨hw', hp⟩ := gen_deliver_pool t acc vo hw (ho vo (List.mem_cons_self ..))
    apply ih _ hw'
    intro vo' hv b he a ha
    exact hp (ho vo' (List.mem_cons_of_mem _ hv) b he a ha)

theorem gen_timeBatch_pool (t : Time) (w : World) (hw : GenPoolWitness w) :
    GenPoolWitness (timeBatch t w).1 := by
  obtain ⟨ht, ho⟩ := gen_tick_fold_pool t (awakeNodes t) w [] hw (by simp)
  apply gen_delivery_fold_pool t _ _ ht
  intro vo hv b he a ha
  obtain ⟨o, hm, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hv
  subst vo
  exact ho o hm b he a ha

theorem gen_prefix_pool (steps : Nat) : GenPoolWitness (buildPrefix steps).1 := by
  induction steps with
  | zero =>
    rw [buildPrefix]
    intro w hw
    exact (List.not_mem_nil hw).elim
  | succ steps ih =>
    rw [buildPrefix]
    exact gen_timeBatch_pool steps _ ih

section
private theorem suffixFrom_pool (start : World) (hw : GenPoolWitness start) (steps : Nat) :
    GenPoolWitness (buildSuffixFrom 254 start steps).1 := by
  induction steps with
  | zero => exact hw
  | succ steps ih => exact gen_timeBatch_pool (254 + steps : Nat) _ ih

theorem gen_suffix_pool (steps : Nat) : GenPoolWitness (buildSuffix steps).1 :=
  suffixFrom_pool (buildPrefix 254).1 (gen_prefix_pool 254) steps

end

/-- H at every prefix batch: all selected rows are in the selecting node's pool. -/
theorem i7_prefix_selected_rows (steps : Nat) (H : Block) (a : RowWire params.n)
    (ha : a ∈ proposalRows params (FGSA.clock params ((buildPrefix steps).1 0).st steps) H) :
    a ∈ (FGSA.clock params ((buildPrefix steps).1 0).st steps).rowPool := by
  apply gen_proposalRows_origin _ _ H (fun _ hm => hm) _ a ha
  rw [i7_clock_rowPool]
  exact gen_storedRows_clock _ _ _ (gen_prefix_pool steps)

/-- H at every suffix batch, including the continuation through time 269. -/
theorem i7_suffix_selected_rows (steps : Nat) (H : Block) (a : RowWire params.n)
    (ha : a ∈ proposalRows params
      (FGSA.clock params ((buildSuffix steps).1 0).st (254 + steps : Nat)) H) :
    a ∈ (FGSA.clock params ((buildSuffix steps).1 0).st (254 + steps : Nat)).rowPool := by
  apply gen_proposalRows_origin _ _ H (fun _ hm => hm) _ a ha
  rw [i7_clock_rowPool]
  exact gen_storedRows_clock _ _ _ (gen_suffix_pool steps)

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- The vote pool is also unchanged by the clock. -/
theorem i7_clock_votes (st : State params.n) (t : Time) :
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

theorem gen_known_mono (P Q : Obj params → Prop) (st : State params.n)
    (h : GenKnown P st) (hp : ∀ o, P o → Q o) : GenKnown Q st :=
  ⟨fun a ha => hp _ (h.1 a ha),
    fun w hw s b hd a ha => hp _ (h.2.1 w hw s b hd a ha),
    fun a ha => hp _ (h.2.2 a ha)⟩

theorem gen_known_clock (P : Obj params → Prop) (st : State params.n) (t : Time)
    (h : GenKnown P st) : GenKnown P (FGSA.clock params st t) := by
  simpa only [GenKnown, GenStoredRows, i7_clock_proposals, i7_clock_rowPool,
    i7_clock_votes] using h

theorem gen_known_row (P : Obj params → Prop) (st : State params.n)
    (a : RowWire params.n) (h : GenKnown P st) (ha : P (ofRow params a)) :
    GenKnown P (admitRow params st a) := by
  rcases i7_admitRow_eq st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

theorem gen_known_rows (P : Obj params → Prop) (rows : List (RowWire params.n))
    (st : State params.n) (h : GenKnown P st) (hr : ∀ a ∈ rows, P (ofRow params a)) :
    GenKnown P (rows.foldl (admitRow params) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (gen_known_row P st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

theorem gen_known_vote (P : Obj params → Prop) (st : GridCO.State params.n .root)
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
theorem i7_lift_baseVote (a h : HeadWire params.n) (he : liftHead? (baseVote a) = some h) :
    a = h := by
  obtain ⟨auth, b⟩ := a
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
    simp [baseVote, baseHead, HeadWire.decode?, GridCO.fromHead, liftHead?,
      GridCO.headLabel?, GridCO.headSeat?, GridCO.headTarget?] at he
  exact he

theorem gen_known_base_proposal (P : Obj params → Prop) (st : GridCO.State params.n .root)
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
      apply ih _ (gen_known_vote P st (baseVote a) hs ?_)
      · exact fun a ha => hx a (List.mem_cons_of_mem _ ha)
      · intro h he
        exact i7_lift_baseVote a h he ▸ hx a (List.mem_cons_self ..)
  unfold GridCO.admitProposal baseProposal
  dsimp only
  split
  · exact h
  · exact hf raw _ h hr

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

theorem i7_decode_vote (o : Obj params) (s : Slot) (i : Fin params.n) (b : BlockId)
    (h : (toWire params o).decode = some (.vote s i b)) :
    o = ⟨.seat (.base (.head s)) i, .head b⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | prop r => cases payload <;> cases h
    | base l => cases l <;> cases payload <;> cases h; rfl

theorem i7_decode_row (o : Obj params) (i : Fin params.n) (body : RowPayload)
    (h : (toWire params o).decode = some (.row i body)) :
    o = ⟨.seat (.base .fg) i, .row body⟩ := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | prop s => cases payload <;> cases h
    | base l => cases l <;> cases payload <;> cases h; rfl

theorem i7_decode_proposal (o : Obj params) (s : Slot) (b : NamedProposal params.n)
    (h : (toWire params o).decode = some (.block s b)) :
    o.payload = .proposal b := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | none => cases payload <;> cases h
  | seat l j =>
    cases l with
    | base l => cases l <;> cases payload <;> cases h
    | prop r => cases payload <;> cases h; rfl

theorem gen_known_reconcile (P : Obj params → Prop) (st : State params.n)
    (h : GenKnown P st) : GenKnown P (reconcile st) := by
  unfold reconcile normalizeS
  dsimp only
  split <;> exact h

/-- Processing preserves signature origin, including signatures inside a proposal. -/
theorem gen_known_process (P : Obj params → Prop) (st : State params.n) (o : Obj params)
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
      obtain rfl := i7_decode_vote o s i b hd
      refine ⟨h.1, h.2.1, ?_⟩
      apply gen_known_vote P st.base _ h.2.2
      intro a he
      have he' : (⟨.seat (.head s) i, b⟩ : HeadWire params.n) = a := Option.some.inj he
      exact he' ▸ ho
    | row i body =>
      dsimp only
      obtain rfl := i7_decode_row o i body hd
      exact gen_known_row P st _ h ho
    | block s b =>
      dsimp only
      have he := i7_decode_proposal o s b hd
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
          · apply gen_known_rows _ _ _ _ hr
            have hs : GenKnown P
                { st with
                  base := GridCO.admitProposal params.toParams.engine st.base
                    (baseProposal s b.erase b.raw b.support) b.erase (b.raw.map baseHead)
                  fg := Window.on_block params params.K_W st.fg (fgBlock parent b.erase b.rows)
                  proposals := st.proposals ++ [⟨.proposer s, .proposal b⟩] } := by
              refine ⟨h.1, ?_, gen_known_base_proposal P st.base s b.erase b.raw b.support h.2.2 hv⟩
              intro w hw s' b' hd' a ha
              rcases List.mem_append.mp hw with hw | hw
              · exact h.2.1 w hw s' b' hd' a ha
              · have he := List.mem_singleton.mp hw
                subst w
                cases hd'
                exact hr a ha
            split
            · exact hs
            · exact gen_known_reconcile P _ hs
          · exact h
/-- A proposal takes every carried signature from the stored state. -/
theorem gen_tick_children_known (P : Obj params → Prop) (st : Node params)
    (v : Validator) (t : Time) (o : Obj params) (h : GenKnown P st.st)
    (ho : o ∈ (V2.D.tick weakEnv (runData 269 []) st v t).2) :
    ∀ o', carriesS params o o' → P o' := by
  have hs := gen_known_clock P st.st t h
  obtain ⟨l, i, m, rfl, _, ha⟩ := gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
    change (if joinedNow params (FGSA.clock params st.st t) then
      some (Msg.head (headVote params (FGSA.clock params st.st t) s).root)
      else none) = some m at ha
    split at ha <;> try contradiction
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
    change (if joinedNow params (FGSA.clock params st.st t) then
      (propose params (FGSA.clock params st.st t) s).map (withApp params 0)
      else none) = some m at ha
    split at ha <;> try contradiction
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
        exact gen_proposalRows_origin _ _ _ hs.1 hs.2.1 a ha

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- Ticks preserve known signatures and select only known children. -/
theorem gen_tick_fold_known (P : Obj params → Prop) (t : Time) (vs : List Validator)
    (w : World) (os : List (Obj params)) (hw : ∀ v, GenKnown P (w v).st)
    (ho : ∀ o ∈ os, ∀ o', carriesS params o o' → P o') :
    let result := vs.foldl (fun acc v =>
      let result := V2.D.tick weakEnv (runData 269 []) (acc.1 v) v t
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
        exact (i7_tick_st (w v) v t).symm ▸ gen_known_clock P (w v).st t (hw v)
      · rw [Function.update_of_ne he]
        exact hw u
    · intro o hm o' hc
      rcases List.mem_append.mp hm with hm | hm
      · exact ho o hm o' hc
      · exact gen_tick_children_known P (w v) v t o (hw v) hm o' hc

theorem gen_delivery_fold_known (P : Obj params → Prop) (t : Time)
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
          exact gen_known_process P _ vo.2 (hw vo.1)
            (ho vo (List.mem_cons_self ..)).1 (ho vo (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hv] using hw v
    · exact fun vo hv => ho vo (List.mem_cons_of_mem _ hv)

theorem gen_timeBatch_known (P : Obj params → Prop) (t : Time) (w : World)
    (hw : ∀ v, GenKnown P (w v).st) (ho : ∀ o ∈ (tickBatch t w).2, P o) :
    ∀ v, GenKnown P ((timeBatch t w).1 v).st := by
  obtain ⟨ht, hc⟩ := gen_tick_fold_known P t (awakeNodes t) w [] hw (by simp)
  apply gen_delivery_fold_known P t _ _ ht
  intro vo hv
  obtain ⟨o, hm, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨v, _, hv⟩ := List.mem_map.mp hv
  subst vo
  exact ⟨ho o hm, hc o hm⟩

theorem gen_timeBatch_delivered (t : Time) (w : World) (v : Validator)
    (o : Obj params) (s : Time) (hm : V2.Event.deliver v o s ∈ (timeBatch t w).2) :
    s = t ∧ o ∈ (tickBatch t w).2 := by
  obtain ⟨ds, he, hs⟩ := timeBatch_block t w
  rw [he] at hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨u, _, hu⟩ := List.mem_map.mp hm
    cases hu
  · obtain ⟨o', ho, hv⟩ := List.mem_flatMap.mp (hs.subset hm)
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
    cases hu
    exact ⟨rfl, ho⟩

/-- A signature has an emission in the given trace at or before the bound. -/
def GenPast (es : List Event) (t : Time) (o : Obj params) : Prop :=
  ∃ v s, s ≤ t ∧ GenEmits V2.D.World.init es v o s

/-- Every carried signature has an emission no later than its delivery. -/
def GenCarried (es : List Event) : Prop :=
  ∀ v o t, V2.Event.deliver v o t ∈ es →
    ∀ o', carriesS params o o' → GenPast es t o'

theorem gen_past_append (es ds : List Event) (t : Time) (o : Obj params)
    (h : GenPast es t o) : GenPast (es ++ ds) t o := by
  obtain ⟨v, s, ht, he⟩ := h
  exact ⟨v, s, ht, genEmits_append_left _ es ds v o s he⟩

theorem gen_past_bound (es : List Event) (t u : Time) (o : Obj params)
    (h : GenPast es t o) (htu : t ≤ u) : GenPast es u o := by
  obtain ⟨v, s, ht, he⟩ := h
  exact ⟨v, s, ht.trans htu, he⟩

-- This proof unfolds nested world and event folds to transport emission witnesses.
/-- One real batch preserves signature origin and adds valid carried-signature witnesses. -/
theorem gen_batch_carried (es : List Event) (t : Time) (w : World)
    (he : w = genFold V2.D.World.init es)
    (hw : ∀ v, GenKnown (GenPast es t) (w v).st) (hc : GenCarried es) :
    (∀ v, GenKnown (GenPast (es ++ (timeBatch t w).2) (t + 1))
      ((timeBatch t w).1 v).st) ∧ GenCarried (es ++ (timeBatch t w).2) := by
  have hp (o : Obj params) (ho : GenPast es t o) :
      GenPast (es ++ (timeBatch t w).2) (t + 1) o :=
    gen_past_bound _ t (t + 1) o (gen_past_append es _ t o ho) (le_add_of_nonneg_right (by decide))
  constructor
  · apply gen_timeBatch_known (GenPast (es ++ (timeBatch t w).2) (t + 1)) t w
    · exact fun v => gen_known_mono _ _ _ (hw v) hp
    · intro o ho
      obtain ⟨u, hu⟩ := tickBatch_origin t w o ho
      obtain ⟨ds, hd, _⟩ := timeBatch_block t w
      have hu' : GenEmits w (timeBatch t w).2 u o t := by
        rw [hd]
        exact genEmits_append_left w _ ds u o t hu
      refine ⟨u, t, le_add_of_nonneg_right (by decide), ?_⟩
      apply genEmits_append_right V2.D.World.init es _ u o t
      rw [← he]
      exact hu'
  · intro v o s hm o' hcarry
    rcases List.mem_append.mp hm with hm | hm
    · exact gen_past_append es _ s o' (hc v o s hm o' hcarry)
    · obtain ⟨hs, ho⟩ := gen_timeBatch_delivered t w v o s hm
      subst s
      have hk := (gen_tick_fold_known (GenPast es t) t (awakeNodes t) w [] hw (by simp)).2
      exact gen_past_append es _ t o' (hk o ho o' hcarry)

/-- Symbolic signature-origin induction for the entire prefix generator. -/
theorem gen_prefix_carried (steps : Nat) :
    (∀ v, GenKnown (GenPast (buildPrefix steps).2 steps) ((buildPrefix steps).1 v).st) ∧
      GenCarried (buildPrefix steps).2 := by
  induction steps with
  | zero =>
    rw [buildPrefix]
    constructor
    · intro v
      exact ⟨by simp [V2.D.World.init, fgsa, initial],
        by intro w hw; exact (List.not_mem_nil hw).elim,
        by simp [V2.D.World.init, fgsa, initial, GridCO.initial]⟩
    · intro v o t hm; exact (List.not_mem_nil hm).elim
  | succ steps ih =>
    rw [buildPrefix]
    simpa only [Nat.cast_add, Nat.cast_one] using
      gen_batch_carried (buildPrefix steps).2 steps (buildPrefix steps).1
        (prefix_replay_fresh steps).1 ih.1 ih.2

section
/-- The suffix starts with the proved prefix state and retains all prefix emissions. -/
private theorem suffixFrom_carried (es : List Event) (start : World)
    (hstart : start = genFold V2.D.World.init es)
    (hw : ∀ v, GenKnown (GenPast es 254) (start v).st) (hc : GenCarried es)
    (steps : Nat) :
    (∀ v, GenKnown (GenPast (es ++ (buildSuffixFrom 254 start steps).2)
      (254 + steps : Nat)) ((buildSuffixFrom 254 start steps).1 v).st) ∧
      GenCarried (es ++ (buildSuffixFrom 254 start steps).2) := by
  induction steps with
  | zero =>
    simpa only [buildSuffixFrom, List.append_nil, Nat.add_zero, Nat.cast_ofNat] using
      And.intro hw hc
  | succ steps ih =>
    have he : (buildSuffixFrom 254 start steps).1 =
        genFold V2.D.World.init (es ++ (buildSuffixFrom 254 start steps).2) := by
      rw [genFold_append, ← hstart]
      exact (suffixFrom_replay_fresh start steps).1
    simpa only [buildSuffixFrom, List.append_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using
      gen_batch_carried _ (254 + steps : Nat) (buildSuffixFrom 254 start steps).1 he ih.1 ih.2


theorem gen_suffix_carried (steps : Nat) :
    (∀ v, GenKnown (GenPast ((buildPrefix 254).2 ++ (buildSuffix steps).2)
      (254 + steps : Nat)) ((buildSuffix steps).1 v).st) ∧
      GenCarried ((buildPrefix 254).2 ++ (buildSuffix steps).2) :=
  suffixFrom_carried (buildPrefix 254).2 (buildPrefix 254).1
    (prefix_replay_fresh 254).1 (gen_prefix_carried 254).1 (gen_prefix_carried 254).2 steps

end

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- A carried-signature witness identifies the holder of its earlier emission. -/
theorem genCarried_runData (h : Time) (es : List Event) (hc : GenCarried es)
    (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes (runData h es) v o t)
    (o' : Obj params) (hcarry : (fgsa params unitCodec).carries o o') (u : Validator)
    (hh : V2.D.Run.holder (runData h es) o'.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits weakEnv (runData h es) u o' t' := by
  obtain ⟨i, hi⟩ := hp
  obtain ⟨x, s, ht, he⟩ := hc v o t (List.mem_of_getElem? hi) o' hcarry
  have hem := genEmits_runData h es x o' s he
  obtain ⟨pre, post, _, ho⟩ := he
  have hh' := gen_tick_holder (genFold V2.D.World.init pre x) x s o' ho
  have hu : u = x := Option.some.inj (hh.symm.trans hh')
  exact ⟨s, ht, hu.symm ▸ hem⟩

theorem source_carried (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes source v o t) (o' : Obj params)
    (hc : (fgsa params unitCodec).carries o o') (u : Validator) (_hu : u ∈ source.honest)
    (hh : V2.D.Run.holder source o'.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits strongEnv source u o' t' := by
  obtain ⟨s, ht, he⟩ := genCarried_runData 253 (buildPrefix 254).2
    (gen_prefix_carried 254).2 v o t hp o' hc u hh
  exact ⟨s, ht, source_emits_weak_to_strong u o' s he⟩

theorem continuation_carried (v : Validator) (o : Obj params) (t : Time)
    (hp : V2.D.Run.processes continuation v o t) (o' : Obj params)
    (hc : (fgsa params unitCodec).carries o o') (u : Validator)
    (_hu : u ∈ continuation.honest)
    (hh : V2.D.Run.holder continuation o'.auth = some u) :
    ∃ t', t' ≤ t ∧ V2.D.Run.emits weakEnv continuation u o' t' :=
  genCarried_runData 269 _ (gen_suffix_carried 16).2 v o t hp o' hc u hh

theorem source_signatures : V2.D.UnforgeableSignatures strongEnv source where
  unforgeable := source_unforgeable
  carried := source_carried

theorem continuation_signatures : V2.D.UnforgeableSignatures weakEnv continuation where
  unforgeable := continuation_unforgeable
  carried := continuation_carried

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- The full tick fold keeps each node's row pool. -/
theorem i7_tick_fold_pool_eq (t : Time) (vs : List Validator) (w : World)
    (os : List (Obj params)) (u : Validator) :
    let result := vs.foldl (fun acc v =>
      let result := V2.D.tick weakEnv (runData 269 []) (acc.1 v) v t
      (Function.update acc.1 v result.1, acc.2 ++ result.2)) (w, os)
    (result.1 u).st.rowPool = (w u).st.rowPool := by
  induction vs generalizing w os with
  | nil => rfl
  | cons v vs ih => exact (ih _ _).trans (gen_tick_pool_fields w v t u).1

/-- Every proposal actually released by a batch carries only rows in node zero's pool. -/
theorem i7_batch_emitted_rows (t : Time) (w : World) (hw : GenPoolWitness w)
    (o : Obj params) (ho : o ∈ (tickBatch t w).2)
    (b : NamedProposal params.n)
    (he : o.payload = .proposal b) : ∀ a ∈ b.rows, a ∈ (w 0).st.rowPool := by
  have hr := (gen_tick_fold_pool t (awakeNodes t) w [] hw (by simp)).2 o ho b he
  simpa only [i7_tick_fold_pool_eq] using hr

/-- H for the actual prefix emissions, for every generator length. -/
theorem i7_prefix_emitted_rows (steps : Nat) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).1).2)
    (b : NamedProposal params.n)
    (he : o.payload = .proposal b) :
    ∀ a ∈ b.rows, a ∈ ((buildPrefix steps).1 0).st.rowPool :=
  i7_batch_emitted_rows steps _ (gen_prefix_pool steps) o ho b he

/-- H for the actual suffix emissions, without a bound on the generator length. -/
theorem i7_suffix_emitted_rows (steps : Nat) (o : Obj params)
    (ho : o ∈ (tickBatch (254 + steps : Nat) (buildSuffix steps).1).2)
    (b : NamedProposal params.n)
    (he : o.payload = .proposal b) :
    ∀ a ∈ b.rows, a ∈ ((buildSuffix steps).1 0).st.rowPool :=
  i7_batch_emitted_rows (254 + steps : Nat) _ (gen_suffix_pool steps) o ho b he

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end

@[expose] public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

attribute [local irreducible] buildPrefix

/-- A row with a generated emission passes the row wire check. -/
theorem gen_past_row_valid (es : List Event) (t : Time) (a : RowWire params.n)
    (h : GenPast es t (ofRow params a)) : a.valid = true := by
  obtain ⟨v, s, _, pre, post, _, ho⟩ := h
  have hw := gen_tick_nonproposal_wire (genFold V2.D.World.init pre v) v s (ofRow params a) ho
    (by intro b; cases a with | mk auth body => cases auth <;> simp [ofRow,
      ofWire])
  obtain ⟨auth, body⟩ := a
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;>
    simp [fgsa, FGSA.wellFormed, toWire, toAuth, ofRow, ofWire, ofAuth, Wire.decode,
      RowWire.valid, RowWire.decode?] at hw ⊢
  exact hw

/-- Both row stores in every generated prefix contain valid rows. -/
theorem gen_prefix_rows_valid (steps : Nat) (v : Validator) :
    (∀ a ∈ ((buildPrefix steps).1 v).st.rowPool, a.valid = true) ∧
      GenStoredRows (fun a => a.valid = true) ((buildPrefix steps).1 v).st := by
  have h := (gen_prefix_carried steps).1 v
  exact ⟨fun a ha => gen_past_row_valid _ _ a (h.1 a ha),
    fun w hw s b hd a ha =>
      gen_past_row_valid _ _ a (h.2.1 w hw s b hd a ha)⟩

/-- The same row validity invariant holds throughout the generated suffix. -/
theorem gen_suffix_rows_valid (steps : Nat) (v : Validator) :
    (∀ a ∈ ((buildSuffix steps).1 v).st.rowPool, a.valid = true) ∧
      GenStoredRows (fun a => a.valid = true) ((buildSuffix steps).1 v).st := by
  have h := (gen_suffix_carried steps).1 v
  exact ⟨fun a ha => gen_past_row_valid _ _ a (h.1 a ha),
    fun w hw s b hd a ha =>
      gen_past_row_valid _ _ a (h.2.1 w hw s b hd a ha)⟩

/-- Proposal row validity in the source is now a generator invariant. -/
theorem i7_prefix_proposal_rows_valid (steps : Nat) (v : Validator) (H : Block) :
    ∀ a ∈ proposalRows params (FGSA.clock params ((buildPrefix steps).1 v).st steps) H,
      a.valid = true := by
  have h := gen_prefix_rows_valid steps v
  apply gen_proposalRows_origin
  · simpa only [i7_clock_rowPool] using h.1
  · exact gen_storedRows_clock _ _ _ h.2

/-- Proposal row validity in the continuation uses the same invariant. -/
theorem i7_suffix_proposal_rows_valid (steps : Nat) (v : Validator) (H : Block) :
    ∀ a ∈ proposalRows params
      (FGSA.clock params ((buildSuffix steps).1 v).st (254 + steps : Nat)) H, a.valid = true := by
  have h := gen_suffix_rows_valid steps v
  apply gen_proposalRows_origin
  · simpa only [i7_clock_rowPool] using h.1
  · exact gen_storedRows_clock _ _ _ h.2

/-- The time-eight batch belongs to both generated runs. -/
theorem i7_eight_in_both_runs (e : Event)
    (he : e ∈ (timeBatch 8 (buildPrefix 8).1).2) :
    e ∈ source.events ∧ e ∈ continuation.events := by
  have hs : e ∈ source.events := by
    change e ∈ (buildPrefix 254).2
    rw [prefix_blocks]
    exact List.mem_flatMap.mpr ⟨8, by decide, he⟩
  exact ⟨hs, List.mem_append_left _ hs⟩


/-! P-Fx: execution checks for the awake-only generator. -/

section Wire
variable {p : Params}

theorem fx_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, b, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s b hd a hm

theorem fx_proposal_votes (st : State p.n) (s : Slot) :
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

theorem fx_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
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
  obtain ⟨hraw, hsup⟩ := fx_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (fx_proposal_rows st H hv)
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

/-- A list fold preserves knowledge when each delivery and its children have it. -/
theorem fx_known_fold (P : Obj params → Prop) (w : World) (es : List Event)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es)
    (hw : ∀ v, GenKnown P (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P o ∧ ∀ o', carriesS params o o' → P o') :
    ∀ v, GenKnown P (genFold w es v).st := by
  induction es generalizing w with
  | nil => exact hw
  | cons e es ih =>
    apply ih
    · exact fun v t hm => hnr v t (List.mem_cons_of_mem _ hm)
    · intro u
      cases e with
      | restart v t =>
        exact (hnr v t (List.mem_cons_self ..)).elim
      | tick v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact (i7_tick_st (w v) v t).symm ▸ gen_known_clock P _ t (hw v)
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
      | deliver v o t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact gen_known_process P _ o (hw v)
            (he v o t (List.mem_cons_self ..)).1
            (he v o t (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
    · intro v o t hm
      exact he v o t (List.mem_cons_of_mem _ hm)

/-- I3 and I7 give row validity at every event prefix, without delivery validity. -/
theorem fx_rows_at_index (h : Time) (es : List Event)
    (ho : GenOrigin V2.D.World.init es) (hc : GenCarried es)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es) (i : Nat) (v : Validator) :
    EmissionRowsValid (V2.D.Run.stateBefore weakEnv (runData h es) i v).st := by
  let P := fun o => ∃ t, GenPast es t o
  have hk : GenKnown P (genFold V2.D.World.init (es.take i) v).st := by
    apply fx_known_fold
    · exact fun v t hm => hnr v t (List.mem_of_mem_take hm)
    · intro u
      exact ⟨by simp [V2.D.World.init, fgsa, initial],
        by simp [GenStoredRows, V2.D.World.init, fgsa, initial],
        by simp [V2.D.World.init, fgsa, initial, GridCO.initial]⟩
    · intro u o t hm
      have hm' := List.mem_of_mem_take hm
      obtain ⟨x, hx⟩ := ho u o t hm'
      exact ⟨⟨t, x, t, le_rfl, hx⟩, fun o' hcarry => ⟨t, hc u o t hm' o' hcarry⟩⟩
  rw [runData_stateBefore]
  exact ⟨fun a ha => by
      obtain ⟨t, ht⟩ := hk.1 a ha
      exact gen_past_row_valid es t a ht,
    fun w hw s b hd a ha => by
      obtain ⟨t, ht⟩ := hk.2.1 w hw s b hd a ha
      exact gen_past_row_valid es t a ht⟩

/-- Every release passes the wire check, using the symbolic row invariant. -/
theorem fx_emit_wire (h : Time) (es : List Event)
    (hs : V2.D.ScheduleWellFormed weakEnv (runData h es))
    (horigin : GenOrigin V2.D.World.init es) (hcarried : GenCarried es)
    (hnr : ∀ v t, V2.Event.restart v t ∉ es)
    (v : Validator) (o : Obj params) (t : Time)
    (hem : V2.D.Run.emits weakEnv (runData h es) v o t) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨i, hi, ho⟩ := hem
  rw [(V2.D.Run.step_tick_eq weakEnv (runData h es) hi).2] at ho
  obtain ⟨l, j, m, rfl, hl, ha⟩ := gen_tick_seat
    (V2.D.Run.stateBefore weakEnv (runData h es) i v) v t o ho
  cases l with
  | headAction s =>
    change (if joinedNow params _ then some (Msg.head (headVote params _ s).root)
      else none) = some m at ha
    split at ha <;> try contradiction
    have he : .head (headVote params
        (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st t) s).root = m :=
      Option.some.inj ha
    subst m
    rfl
  | fgAction r =>
    change (attest params (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st t)
      (V2.D.Run.stateBefore weakEnv (runData h es) i v).record ⟨0, params.nPos⟩).1.map Msg.row
        = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact gen_attest_valid _ _ _ _ hb
  | propAction s =>
    have ht : SA.proposalTime params.toParams s = t :=
      ((fgsa params unitCodec).duties_spec (.propAction s) t).1 hl
    subst t
    change (if joinedNow params _ then (propose params _ s).map (withApp params 0)
      else none) = some m at ha
    split at ha <;> try contradiction
    have hm : (propose params
        (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st
          (SA.proposalTime params.toParams s)) s).map (withApp params 0) = some m := ha
    have hs0 : 0 < s := by
      by_contra hn
      have he : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      change none = some m at hm
      cases hm
    have hv := fx_rows_at_index h es horigin hcarried hnr i v
    have hv' : EmissionRowsValid
        (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st
          (SA.proposalTime params.toParams s)) := by
      simpa only [EmissionRowsValid, i7_clock_rowPool, i7_clock_proposals] using hv
    exact fx_proposal_wf _ s 0 hv'
      (fgsa_propose_parent_lt weakEnv (runData h es) hs hi hs0) hm

/-- The source schedule has the same public times in the weak environment. -/
theorem fx_source_schedule : V2.D.ScheduleWellFormed weakEnv source :=
  { witness_source_schedule with
    tick_public := witness_source_schedule.tick_public
    tick_total := fun v hv t hp ht hh _ => witness_source_tick_total v hv t hp ht hh }

/-- Proposal wire checks now hold for every source delivery. -/
theorem fx_source_wire (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : source.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨u, hu⟩ := prefix_origin 254 v o t (List.mem_of_getElem? hi)
  exact fx_emit_wire 253 _ fx_source_schedule (prefix_origin 254)
    (gen_prefix_carried 254).2 (prefix_no_restart 254) u o t (genEmits_runData 253 _ u o t hu)

/-- Proposal wire checks also hold for every continuation delivery. -/
theorem fx_continuation_wire (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : continuation.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨u, hu⟩ := continuation_genOrigin v o t (List.mem_of_getElem? hi)
  exact fx_emit_wire 269 _ continuation_schedule continuation_genOrigin
    (gen_suffix_carried 16).2 (fun v t hm => by
      rcases List.mem_append.mp hm with hm | hm
      · exact prefix_no_restart 254 v t hm
      · exact suffix_no_restart 16 v t hm) u o t (genEmits_runData 269 _ u o t hu)

/-- A skipped offer has exactly the store effect of the real handler. -/
theorem fx_process_inert (st : State params.n) (o : Obj params)
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
      obtain rfl := i7_decode_row o i body hd
      exact i7_admitRow_duplicate st i body hm
    | block s b =>
      have hm := of_decide_eq_true hp
      apply admitBlock_refused
      cases hP : parentFG st b.erase with
      | none => exact Or.inr (Or.inl rfl)
      | some P => exact Or.inr (Or.inr ⟨P, rfl, by simp [blockAccepted, hm]⟩)

/-- The store update does not depend on whether the offer was skipped. -/
theorem fx_deliver_st (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) :
    ((deliverOne t acc vo).1 u).st =
      if u = vo.1 then FGSA.process params (acc.1 u).st (toWire params vo.2)
      else (acc.1 u).st := by
  unfold deliverOne
  split
  · rename_i hp
    by_cases hu : u = vo.1
    · subst u
      rw [ite_eq_left rfl, fx_process_inert _ _ hp]
    · rw [ite_eq_right hu]
  · dsimp only
    by_cases hu : u = vo.1
    · subst u
      simp only [V2.D.World.step, Function.update_self]
      rfl
    · simp only [V2.D.World.step, Function.update_of_ne hu, ite_eq_right hu]

/-- Each node receives one store update for one offered object. -/
theorem fx_offer_st (t : Time) (acc : World × List Event) (o : Obj params)
    (vs : List Validator) (hn : vs.Nodup) (u : Validator) :
    (((vs.map (fun v => (v, o))).foldl (deliverOne t) acc).1 u).st =
      if u ∈ vs then FGSA.process params (acc.1 u).st (toWire params o)
      else (acc.1 u).st := by
  induction vs generalizing acc with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.foldl_cons, ih _ hn.of_cons, fx_deliver_st]
    by_cases huv : u = v
    · subst u
      simp only [List.mem_cons, true_or, ↓reduceIte, hn.notMem]
    · by_cases hu : u ∈ vs <;> simp [huv, hu]

/-- An awake node's tick store is the clock of its input store. -/
theorem fx_tickBatch_st (t : Time) (w : World) (u : Validator)
    (hu : weakEnv.awake u t = true) :
    ((tickBatch t w).1 u).st = FGSA.clock params (w u).st t := by
  by_cases ht : t ≤ 253
  · have he : awakeNodes t = nodes := by simp [awakeNodes, weakEnv, nodes, ht]
    rw [tickBatch, he]
    fin_cases u <;> simp [nodes, List.foldl_cons] <;> apply i7_tick_st
  · have he : u = 0 := ((weak_awake_iff u t).mp hu).resolve_left ht
    subst u
    have he : awakeNodes t = [0] := by simp [awakeNodes, weakEnv, nodes, ht]
    rw [tickBatch, he]
    simp only [List.foldl_cons, List.foldl_nil, Function.update_self]
    apply i7_tick_st

/-- Awake stores agree at the time of the next generated batch. -/
def FxUniformStores (t : Time) (w : World) : Prop :=
  ∀ u v, weakEnv.awake u t = true → weakEnv.awake v t = true → (w u).st = (w v).st

theorem fx_awake_mono (v : Validator) (a b : Time) (hab : a ≤ b)
    (hb : weakEnv.awake v b = true) : weakEnv.awake v a = true := by
  apply (weak_awake_iff v a).mpr
  rcases (weak_awake_iff v b).mp hb with ht | hv
  · exact Or.inl (hab.trans ht)
  · exact Or.inr hv

theorem fx_offer_uniform (t : Time) (acc : World × List Event) (o : Obj params)
    (hw : FxUniformStores t acc.1) :
    FxUniformStores t (((awakeNodes t).map (fun v => (v, o))).foldl (deliverOne t) acc).1 := by
  intro u v hu hv
  rw [fx_offer_st t acc o _ (awakeNodes_nodup t),
    fx_offer_st t acc o _ (awakeNodes_nodup t),
    ite_eq_left ((awakeNodes_mem u t).mpr hu),
    ite_eq_left ((awakeNodes_mem v t).mpr hv), hw u v hu hv]

theorem fx_objects_uniform (t : Time) (os : List (Obj params))
    (acc : World × List Event) (hw : FxUniformStores t acc.1) :
    FxUniformStores t ((os.flatMap (fun o => (awakeNodes t).map (fun v => (v, o)))).foldl
      (deliverOne t) acc).1 := by
  induction os generalizing acc with
  | nil => exact hw
  | cons o os ih =>
    rw [List.flatMap_cons, List.foldl_append]
    exact ih _ (fx_offer_uniform t acc o hw)

theorem fx_batch_uniform (t : Time) (w : World) (hw : FxUniformStores t w) :
    FxUniformStores t (timeBatch t w).1 := by
  apply fx_objects_uniform
  intro u v hu hv
  rw [fx_tickBatch_st t w u hu, fx_tickBatch_st t w v hv, hw u v hu hv]

theorem fx_prefix_uniform (steps : Nat) : FxUniformStores steps (buildPrefix steps).1 := by
  induction steps with
  | zero => simp [buildPrefix, FxUniformStores, V2.D.World.init]
  | succ steps ih =>
    rw [buildPrefix]
    intro u v hu hv
    exact fx_batch_uniform steps _ ih u v
      (fx_awake_mono u _ _ (by exact_mod_cast Nat.le_succ steps) hu)
      (fx_awake_mono v _ _ (by exact_mod_cast Nat.le_succ steps) hv)

theorem fx_suffix_uniform (steps : Nat) :
    FxUniformStores (254 + steps : Nat) (buildSuffix steps).1 := by
  intro u v hu hv
  have ht : ¬ ((254 + steps : Nat) : Time) ≤ 253 := by simp only [Time] at *; omega
  have hu0 := ((weak_awake_iff u _).mp hu).resolve_left ht
  have hv0 := ((weak_awake_iff v _).mp hv).resolve_left ht
  rw [hu0, hv0]

/-- A batch releases exactly the objects from its four independent ticks. -/
theorem fx_tickBatch_emits (t : Time) (w : World) (o : Obj params) :
    o ∈ (tickBatch t w).2 ↔
      ∃ v, o ∈ (V2.D.tick weakEnv (runData 269 []) (w v) v t).2 := by
  by_cases ht : t ≤ 253
  · have he : awakeNodes t = nodes := by simp [awakeNodes, weakEnv, nodes, ht]
    constructor
    · intro ho
      rw [tickBatch, he] at ho
      simp [nodes] at ho
      rcases List.mem_append.mp ho with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
        · exact ⟨2, h⟩
      · exact ⟨3, h⟩
    · rintro ⟨v, hv⟩
      rw [tickBatch, he]
      simp [nodes]
      fin_cases v
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hv))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hv))
      · exact List.mem_append_left _ (List.mem_append_right _ hv)
      · exact List.mem_append_right _ hv
  · have he : awakeNodes t = [0] := by simp [awakeNodes, nodes, weakEnv, ht]
    rw [tickBatch, he, List.foldl_cons, List.foldl_nil]
    dsimp only
    constructor
    · exact fun ho => ⟨0, ho⟩
    · rintro ⟨v, hv⟩
      have ha : weakEnv.awake v t = true := by
        by_contra hn
        have hf : weakEnv.awake v t = false := Bool.eq_false_iff.mpr hn
        simp [V2.D.tick, hf] at hv
        exact List.not_mem_nil hv
      have hv0 := ((weak_awake_iff v t).mp ha).resolve_left ht
      subst v
      exact hv

/-- Every replayed generator store is reachable. -/
theorem fx_reachable (es : List Event) (u : Validator) :
    Reachable params (genFold V2.D.World.init es u).st := by
  have h := reachable_stateBefore weakEnv (runData 269 es) es.length u
  rwa [runData_stateBefore, List.take_length] at h

/-- An emitted proposal has a parent in the emitting store. -/
theorem fx_tick_deps (st : Node params) (v : Validator) (t : Time)
    (hr : Reachable params st.st) (o : Obj params)
    (ho : o ∈ (V2.D.tick weakEnv (runData 269 []) st v t).2) :
    depsS params (FGSA.clock params st.st t) o = true := by
  obtain ⟨l, j, m, rfl, _, ha⟩ := gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
    change (if joinedNow params _ then some (Msg.head (headVote params _ s).root)
      else none) = some m at ha
    split at ha <;> try contradiction
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
    change (if joinedNow params _ then
      (propose params (FGSA.clock params st.st t) s).map (withApp params 0)
      else none) = some m at ha
    split at ha <;> try contradiction
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
theorem fx_batch_deps_start (t : Time) (w : World) (hw : FxUniformStores t w)
    (hr : ∀ v, Reachable params (w v).st) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) (u : Validator) (hu : weakEnv.awake u t = true) :
    depsS params ((tickBatch t w).1 u).st o = true := by
  obtain ⟨v, hv⟩ := (fx_tickBatch_emits t w o).1 ho
  have hvawake : weakEnv.awake v t = true := by
    by_contra hn
    have hf : weakEnv.awake v t = false := Bool.eq_false_iff.mpr hn
    simp [V2.D.tick, hf] at hv
    exact List.not_mem_nil hv
  rw [fx_tickBatch_st t w u hu, hw u v hu hvawake]
  exact fx_tick_deps _ v t (hr v) o hv

/-- Dependencies persist when the FG store grows. -/
theorem fx_deps_mono {st st' : State params.n} (hT : st.fg.TF ⊆ st'.fg.TF)
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
theorem fx_deliver_deps (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) (o : Obj params)
    (h : depsS params (acc.1 u).st o = true) :
    depsS params ((deliverOne t acc vo).1 u).st o = true := by
  rw [fx_deliver_st]
  split
  · exact fx_deps_mono (process_cumulative params _ _).1
      (process_namedBodies_subset _ _) o h
  · exact h

/-- Dependency checks at every delivery in a list. -/
def FxDeps : World → List Event → Prop
  | _, [] => True
  | w, e :: es =>
      (match e with
        | .deliver v o _ => depsS params (w v).st o = true
        | _ => True) ∧
      FxDeps (V2.D.World.step weakEnv (runData 269 []) w e) es

theorem fx_deps_append (w : World) (es ds : List Event) :
    FxDeps w (es ++ ds) ↔ FxDeps w es ∧ FxDeps (genFold w es) ds := by
  induction es generalizing w with
  | nil => simp [FxDeps, genFold]
  | cons e es ih =>
    simp only [List.cons_append, FxDeps, ih, genFold, List.foldl_cons]
    tauto

/-- The delivery fold keeps the dependency checks in its accumulated trace. -/
theorem fx_delivery_fold_deps (t : Time) (xs : List (Validator × Obj params))
    (w : World) (acc : World × List Event) (hr : genFold w acc.2 = acc.1)
    (hd : FxDeps w acc.2)
    (hx : ∀ vo ∈ xs, depsS params (acc.1 vo.1).st vo.2 = true) :
    FxDeps w (xs.foldl (deliverOne t) acc).2 := by
  induction xs generalizing acc with
  | nil => exact hd
  | cons vo xs ih =>
    rw [List.foldl_cons]
    apply ih
    · unfold deliverOne
      split
      · exact hr
      · simp only [genFold_append, hr]
        rfl
    · unfold deliverOne
      split
      · exact hd
      · apply (fx_deps_append w acc.2 _).2
        exact ⟨hd, by simpa only [FxDeps, hr, and_true] using hx vo (List.mem_cons_self ..)⟩
    · intro vo' hm
      exact fx_deliver_deps t acc vo vo'.1 vo'.2 (hx vo' (List.mem_cons_of_mem _ hm))

theorem fx_ticks_deps (w : World) (t : Time) (vs : List Validator) :
    FxDeps w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih _⟩

/-- I6 holds throughout a complete generated time block. -/
theorem fx_batch_deps (t : Time) (w : World) (hw : FxUniformStores t w)
    (hr : ∀ v, Reachable params (w v).st) : FxDeps w (timeBatch t w).2 := by
  apply fx_delivery_fold_deps
  · exact (tickBatch_replay t w).symm
  · exact fx_ticks_deps w t (awakeNodes t)
  · intro vo hm
    obtain ⟨o, ho, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    exact fx_batch_deps_start t w hw hr o ho v ((awakeNodes_mem v t).mp hv)

/-- I6 for the source generator, by induction over time blocks. -/
theorem fx_prefix_deps (steps : Nat) : FxDeps V2.D.World.init (buildPrefix steps).2 := by
  induction steps with
  | zero => simp [buildPrefix, FxDeps]
  | succ steps ih =>
    rw [buildPrefix]
    apply (fx_deps_append _ _ _).2
    refine ⟨ih, ?_⟩
    rw [← (prefix_replay_fresh steps).1]
    exact fx_batch_deps _ _ (fx_prefix_uniform steps) (fun v => by
      rw [(prefix_replay_fresh steps).1]
      exact fx_reachable _ v)

/-- I6 for the suffix generator, from the source's final store. -/
theorem fx_suffix_deps (steps : Nat) : FxDeps (buildPrefix 254).1 (buildSuffix steps).2 := by
  induction steps with
  | zero => trivial
  | succ steps ih =>
    change FxDeps (buildPrefix 254).1 ((buildSuffix steps).2 ++
      (timeBatch (254 + steps : Nat) (buildSuffix steps).1).2)
    apply (fx_deps_append _ _ _).2
    refine ⟨ih, ?_⟩
    rw [← (suffix_replay_fresh steps).1]
    exact fx_batch_deps _ _ (fx_suffix_uniform steps) (fun v => by
      rw [(suffix_replay_fresh steps).1, (prefix_replay_fresh 254).1,
        ← genFold_append]
      exact fx_reachable _ v)

/-- Read a dependency check at an indexed delivery. -/
theorem fx_deps_get (w : World) (es : List Event) (hd : FxDeps w es)
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

attribute [irreducible] FxDeps

/-- The complete continuation has I6 at every delivery. -/
theorem fx_continuation_genDeps : FxDeps V2.D.World.init continuation.events := by
  change FxDeps V2.D.World.init ((buildPrefix 254).2 ++ (buildSuffix 16).2)
  rw [fx_deps_append, ← (prefix_replay_fresh 254).1]
  exact ⟨fx_prefix_deps 254, fx_suffix_deps 16⟩

set_option maxRecDepth 4096 in
/-- Proposal dependencies hold for the full continuation. -/
theorem fx_continuation_deps (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : continuation.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore weakEnv continuation i v) o
      = true := by
  change depsS params (genFold V2.D.World.init (continuation.events.take i) v).st o = true
  exact fx_deps_get V2.D.World.init continuation.events fx_continuation_genDeps i v o t hi

/-- Proposal dependencies hold for the source in its strong environment. -/
theorem fx_source_deps (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : source.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore strongEnv source i v) o = true := by
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  have hi' : continuation.events[i]? = some (.deliver v o t) := by
    change (source.events ++ (buildSuffix 16).2)[i]? = _
    rw [List.getElem?_append_left hil]
    exact hi
  have h := fx_continuation_deps i v o t hi'
  rw [source_replay (Nat.le_of_lt hil)] at h
  exact h


/-- Every batch event belongs to an awake node. -/
theorem fx_batch_awake (t : Time) (w : World) (e : Event)
    (he : e ∈ (timeBatch t w).2) : weakEnv.awake e.node e.time = true := by
  obtain ⟨ds, hb, hs⟩ := timeBatch_block t w
  rw [hb] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact (awakeNodes_mem v t).mp hv
  · obtain ⟨o, _, he⟩ := List.mem_flatMap.mp (hs.subset he)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact (awakeNodes_mem v t).mp hv

theorem fx_prefix_awake (steps : Nat) (e : Event) (he : e ∈ (buildPrefix steps).2) :
    weakEnv.awake e.node e.time = true := by
  rw [prefix_blocks] at he
  obtain ⟨t, _, he⟩ := List.mem_flatMap.mp he
  exact fx_batch_awake _ _ e he

theorem fx_suffix_awake (steps : Nat) (e : Event) (he : e ∈ (buildSuffix steps).2) :
    weakEnv.awake e.node e.time = true := by
  rw [suffix_blocks] at he
  obtain ⟨t, _, he⟩ := List.mem_flatMap.mp he
  exact fx_batch_awake _ _ e he

/-- Nodes in this continuation sleep once and do not wake within its horizon. -/
theorem fx_weak_no_wakes (v : Validator) (t : Time) : ¬ V2.D.Wakes weakEnv v t := by
  rintro ⟨ha, hs⟩
  have hb := fx_awake_mono v (t - 1) t (by simp only [Time] at *; omega) ha
  rw [hs] at hb
  contradiction

theorem fx_source_sleep : V2.D.SleepWellFormed strongEnv source where
  tick_awake := fun _ _ _ => rfl
  deliver_awake := fun _ _ _ _ => rfl
  restart_awake := fun _ _ _ => rfl
  wake_restart := by
    intro v _ t _ _ hw
    have hf : strongEnv.awake v (t - 1) = true := rfl
    unfold V2.D.Wakes at hw
    rw [hf] at hw
    exact Bool.noConfusion hw.2

theorem fx_continuation_sleep : V2.D.SleepWellFormed weakEnv continuation where
  tick_awake := by
    intro v t he
    rcases List.mem_append.mp he with he | he
    · exact fx_prefix_awake 254 _ he
    · exact fx_suffix_awake 16 _ he
  deliver_awake := by
    intro v o t he
    rcases List.mem_append.mp he with he | he
    · exact fx_prefix_awake 254 _ he
    · exact fx_suffix_awake 16 _ he
  restart_awake := by
    intro v t he
    rcases List.mem_append.mp he with he | he
    · exact (prefix_no_restart 254 v t he).elim
    · exact (suffix_no_restart 16 v t he).elim
  wake_restart := fun v _ t _ _ hw => (fx_weak_no_wakes v t hw).elim

/-- Complete execution validity, including the full-sleep parent. -/
theorem fx_source_execution : V2.D.ExecutionValid strongEnv source where
  toScheduleWellFormed := witness_source_schedule
  wire := fx_source_wire
  deps := fx_source_deps
  fresh := source_fresh
  toUnforgeableSignatures := source_signatures
  toSleepWellFormed := fx_source_sleep

theorem fx_continuation_execution : V2.D.ExecutionValid weakEnv continuation where
  toScheduleWellFormed := continuation_schedule
  wire := fx_continuation_wire
  deps := fx_continuation_deps
  fresh := continuation_fresh
  toUnforgeableSignatures := continuation_signatures
  toSleepWellFormed := fx_continuation_sleep

theorem fx_source_restarts : V2.D.RestartsAtWakes strongEnv source := by
  intro v t he
  exact (prefix_no_restart 254 v t he).elim

theorem fx_continuation_restarts : V2.D.RestartsAtWakes weakEnv continuation := by
  intro v t he
  rcases List.mem_append.mp he with he | he
  · exact (prefix_no_restart 254 v t he).elim
  · exact (suffix_no_restart 16 v t he).elim

/-- Exact proposal bodies from the finite event-index emission table. -/
def fx_emittedTable (E : Generic.Env Validator)
    (rho : V2.D.Run Validator (fgsa params unitCodec)) : List (NamedProposal params.n) :=
  (List.range rho.events.length).flatMap (fun i =>
    (V2.D.Run.emitsAt E rho i).filterMap (fun o => match o.payload with
      | .proposal N => some N
      | _ => none))

/-- P23-A: an honest emission is a body in the generator's finite scope table. -/
theorem fx_emitted_in_table (E : Generic.Env Validator)
    (rho : V2.D.Run Validator (fgsa params unitCodec)) (v : Validator)
    (o : Obj params) (t : Time) (N : NamedProposal params.n)
    (hem : V2.D.Run.emits E rho v o t) (hp : o.payload = .proposal N) :
    N ∈ fx_emittedTable E rho := by
  obtain ⟨i, hi, ho⟩ := hem
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨o, ho, by rw [hp]⟩

/-- P23-A: exact emitted bodies and their named ancestors belong to receipt scope. -/
theorem fx_emitted_in_scope (E : Generic.Env Validator)
    (rho : V2.D.Run Validator (fgsa params unitCodec)) (v : Validator)
    (hv : v ∈ rho.honest) (o : Obj params) (t : Time) (N A : NamedProposal params.n)
    (hem : V2.D.Run.emits E rho v o t) (hp : o.payload = .proposal N)
    (ha : NamedProposal.Preceq A N) : NamedProposalReceiptScope params unitCodec E rho A :=
  Or.inr ⟨v, hv, o, t, N, hem, hp, ha⟩

/-- P23-A table interface for P-As: include emitted bodies before proving injectivity. -/
theorem fx_receipt_roots_of_table (E : Generic.Env Validator)
    (rho : V2.D.Run Validator (fgsa params unitCodec)) (table : List (NamedProposal params.n))
    (hscope : ∀ N, NamedProposalInRun params unitCodec E rho N → N ∈ table)
    (hemit : ∀ N ∈ fx_emittedTable E rho, N ∈ table)
    (hancestor : ∀ N ∈ table, ∀ A, NamedProposal.Preceq A N → A ∈ table)
    (hinjective : ∀ N ∈ table, ∀ M ∈ table, N.root = M.root → N = M) :
    NamedReceiptRootCollisionFree params unitCodec E rho := by
  have hmem (A : NamedProposal params.n)
      (ha : NamedProposalReceiptScope params unitCodec E rho A) : A ∈ table := by
    rcases ha with hs | ⟨v, _, o, t, N, hem, hp, hAN⟩
    · exact hscope A hs
    · exact hancestor N (hemit N (fx_emitted_in_table E rho v o t N hem hp)) A hAN
  exact fun A B ha hb he => hinjective A (hmem A ha) B (hmem B hb) he

-- P-Fx strict audit of the generator and its validity suppliers.
#print axioms awakeNodes_mem
#print axioms awakeNodes_nodup
#print axioms design_numbers
#print axioms delta_ratio
#print axioms bounds
#print axioms witness_window_bounds
#print axioms horizons
#print axioms endpoint
#print axioms witness_covered
#print axioms environments
#print axioms honest_sets
#print axioms faulty_sets
#print axioms fault_bound
#print axioms strong_awake
#print axioms weak_awake_iff
#print axioms awake_agreement
#print axioms strong_awake_set
#print axioms weak_awake_set_before
#print axioms weak_awake_set_after
#print axioms awake_counts
#print axioms witness_participation
#print axioms strict_drop
#print axioms later_sleep
#print axioms cstar
#print axioms linked
#print axioms gap_positive
#print axioms gap_aligned
#print axioms source_gap
#print axioms boundary_duties
#print axioms delivery_fold_mem
#print axioms timeBatch_shape
#print axioms timeBatch_time
#print axioms timeBatch_no_restart
#print axioms nodes_complete
#print axioms timeBatch_tick
#print axioms witness_prefix_times
#print axioms suffix_times
#print axioms prefix_no_restart
#print axioms suffix_no_restart
#print axioms no_restart
#print axioms event_prefix
#print axioms suffix_after_endpoint
#print axioms agreement_of_suffix
#print axioms agreement
#print axioms witness_committees
#print axioms recovery_awake
#print axioms prefix_tick
#print axioms suffix_tick
#print axioms source_horizon_nonneg
#print axioms continuation_horizon_nonneg
#print axioms source_in_horizon
#print axioms continuation_in_horizon
#print axioms source_honest_only
#print axioms continuation_honest_only
#print axioms source_tick_public
#print axioms continuation_tick_public
#print axioms witness_source_tick_total
#print axioms continuation_tick_total
#print axioms suffix_has_ticks
#print axioms phase_le_two
#print axioms key_le_delivery
#print axioms delivery_fold_sorted
#print axioms timeBatch_sorted
#print axioms prefix_sorted
#print axioms suffix_sorted
#print axioms source_sorted
#print axioms continuation_sorted
#print axioms replay_of_agreement
#print axioms source_replay
#print axioms genFold_append
#print axioms genFresh_append
#print axioms tick_fold_replay
#print axioms tickBatch_replay
#print axioms tick_list_fresh
#print axioms delivery_fold_replay_fresh
#print axioms timeBatch_replay_fresh
#print axioms prefix_replay_fresh
#print axioms suffix_replay_fresh
#print axioms genFresh_get
#print axioms genFold_runData
#print axioms genFresh_join
#print axioms runData_fresh
#print axioms continuation_events_eq
#print axioms continuation_genFresh
#print axioms continuation_fresh
#print axioms source_fresh
#print axioms genEmits_cons
#print axioms genEmits_append_left
#print axioms genEmits_append_right
#print axioms genOrigin_append
#print axioms tick_fold_origin
#print axioms tickBatch_origin
#print axioms delivery_fold_sublist
#print axioms timeBatch_block
#print axioms prefix_blocks
#print axioms suffix_blocks
#print axioms timeBatch_origin
#print axioms prefix_origin
#print axioms suffix_origin
#print axioms genEmits_runData
#print axioms gen_tick_holder
#print axioms genOrigin_unforgeable
#print axioms continuation_genOrigin
#print axioms continuation_unforgeable
#print axioms source_emits_weak_to_strong
#print axioms source_unforgeable
#print axioms tick_nodup_without_gossip
#print axioms gen_tick_nodup
#print axioms tick_fold_nodup
#print axioms tickBatch_nodup
#print axioms timeBatch_nodup
#print axioms prefix_nodup
#print axioms suffix_nodup
#print axioms source_nodup
#print axioms continuation_nodup
#print axioms witness_source_schedule
#print axioms continuation_schedule
#print axioms runData_stateBefore
#print axioms genOrigin_runData
#print axioms source_delivery_origin
#print axioms continuation_delivery_origin
#print axioms gen_nonproposal_deps
#print axioms gen_derive_positive
#print axioms gen_attest_valid
#print axioms gen_tick_seat
#print axioms gen_tick_nonproposal_wire
#print axioms delivery_fold_offered
#print axioms timeBatch_offered
#print axioms genOrigin_nonproposal_wire
#print axioms source_nonproposal_wire
#print axioms continuation_nonproposal_wire
#print axioms i7_admitRow_duplicate
#print axioms i7_clock_fields
#print axioms i7_clock_proposals
#print axioms i7_clock_rowPool
#print axioms i7_reconcile_fields
#print axioms i7_admitRow_eq
#print axioms i7_foldl_admitRow_eq
#print axioms i7_tick_st
#print axioms gen_proposalRows_origin
#print axioms gen_storedRows_clock
#print axioms gen_storedRows_fold
#print axioms gen_storedRows_process
#print axioms gen_process_pool_mono
#print axioms gen_tick_proposal_rows
#print axioms gen_tick_pool_fields
#print axioms gen_tick_fold_pool
#print axioms gen_deliver_pool
#print axioms gen_delivery_fold_pool
#print axioms gen_timeBatch_pool
#print axioms gen_prefix_pool
#print axioms gen_suffix_pool
#print axioms i7_prefix_selected_rows
#print axioms i7_suffix_selected_rows
#print axioms i7_clock_votes
#print axioms gen_known_mono
#print axioms gen_known_clock
#print axioms gen_known_row
#print axioms gen_known_rows
#print axioms gen_known_vote
#print axioms i7_lift_baseVote
#print axioms gen_known_base_proposal
#print axioms i7_decode_vote
#print axioms i7_decode_row
#print axioms i7_decode_proposal
#print axioms gen_known_reconcile
#print axioms gen_known_process
#print axioms gen_tick_children_known
#print axioms gen_tick_fold_known
#print axioms gen_delivery_fold_known
#print axioms gen_timeBatch_known
#print axioms gen_timeBatch_delivered
#print axioms gen_past_append
#print axioms gen_past_bound
#print axioms gen_batch_carried
#print axioms gen_prefix_carried
#print axioms gen_suffix_carried
#print axioms genCarried_runData
#print axioms source_carried
#print axioms continuation_carried
#print axioms source_signatures
#print axioms continuation_signatures
#print axioms i7_tick_fold_pool_eq
#print axioms i7_batch_emitted_rows
#print axioms i7_prefix_emitted_rows
#print axioms i7_suffix_emitted_rows
#print axioms gen_past_row_valid
#print axioms gen_prefix_rows_valid
#print axioms gen_suffix_rows_valid
#print axioms i7_prefix_proposal_rows_valid
#print axioms i7_suffix_proposal_rows_valid
#print axioms i7_eight_in_both_runs
#print axioms fx_proposal_rows
#print axioms fx_proposal_votes
#print axioms fx_proposal_wf
#print axioms fx_known_fold
#print axioms fx_rows_at_index
#print axioms fx_emit_wire
#print axioms fx_source_schedule
#print axioms fx_source_wire
#print axioms fx_continuation_wire
#print axioms fx_process_inert
#print axioms fx_deliver_st
#print axioms fx_offer_st
#print axioms fx_tickBatch_st
#print axioms fx_awake_mono
#print axioms fx_offer_uniform
#print axioms fx_objects_uniform
#print axioms fx_batch_uniform
#print axioms fx_prefix_uniform
#print axioms fx_suffix_uniform
#print axioms fx_tickBatch_emits
#print axioms fx_reachable
#print axioms fx_tick_deps
#print axioms fx_batch_deps_start
#print axioms fx_deps_mono
#print axioms fx_deliver_deps
#print axioms fx_deps_append
#print axioms fx_delivery_fold_deps
#print axioms fx_ticks_deps
#print axioms fx_batch_deps
#print axioms fx_prefix_deps
#print axioms fx_suffix_deps
#print axioms fx_deps_get
#print axioms fx_continuation_genDeps
#print axioms fx_continuation_deps
#print axioms fx_source_deps
#print axioms fx_batch_awake
#print axioms fx_prefix_awake
#print axioms fx_suffix_awake
#print axioms fx_weak_no_wakes
#print axioms fx_source_sleep
#print axioms fx_continuation_sleep
#print axioms fx_source_execution
#print axioms fx_continuation_execution
#print axioms fx_source_restarts
#print axioms fx_continuation_restarts
#print axioms fx_emitted_in_table
#print axioms fx_emitted_in_scope
#print axioms fx_receipt_roots_of_table

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end
