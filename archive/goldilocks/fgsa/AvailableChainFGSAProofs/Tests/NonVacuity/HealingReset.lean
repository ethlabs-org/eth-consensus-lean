module
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
-- shake: keep (own-library route)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources -- shake: keep (row source fields)
public meta import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
-- shake: keep (closed evaluations)

@[expose] public section

set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
set_option exponentiation.threshold 2000

-- Each test is complete on its own. The layer rules forbid test-to-test imports.
namespace AvailableChain.FGSA.Run.Tests.NonVacuity.HealingReset

/-- ROOT-DIGEST W3b. S5 fixture: one honest node, positive horizon, and unchanged SA clocks. -/
def params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩

def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def deltaF : Time := 3
def gap : Time := 4
def horizon : Time := 304

theorem params_delta : params.Δ = 1 := rfl
theorem params_n : params.n = 1 := rfl
theorem params_k : params.k = 2 := rfl
theorem params_eta : params.η = 0 := rfl
theorem params_R : params.R = 3 := rfl
theorem params_timeout : params.δt = 6 := rfl
theorem params_window : params.K_W = 2 := rfl
theorem env_delta : env.Δ = params.Δ := rfl
theorem env_gst : env.t_GST = 0 := rfl
theorem env_awake (v : Fin 1) (t : Time) : env.awake v t = true := rfl
theorem deltaF_value : deltaF = 3 := rfl
theorem gap_value : gap = 4 := rfl
theorem horizon_value : horizon = 304 := rfl
theorem horizon_pos : 0 < horizon := by decide
theorem deltaF_lower : env.Δ ≤ deltaF := by decide
theorem gap_lower : 4 * params.Δ ≤ gap := by decide

theorem kappaF_value : kappaF params deltaF = 3 := by decide
theorem betaF_value : betaF params deltaF = 12 := by decide
theorem epsF_value : epsF params deltaF = 4 := by decide
theorem period_value : P params = 12 := by decide
theorem gamma_value : Γ params gap = 4 := by decide
theorem lease_value : L params = 7 := by decide
theorem rhoGamma_value : ρΓ params gap = 26 := by decide
theorem rhoOne_value : ρ₁ params gap = 21 := by decide
theorem short_k : params.k ≤ 2 * params.R + 1 := by decide
theorem Eg_two_value : E_gF params deltaF gap (ρΓ params gap) = 53 := by decide
theorem Eg_one_value : E_gF params deltaF gap (ρ₁ params gap) = 48 := by decide
theorem Ej_two_value : E_jF params deltaF gap (ρΓ params gap) = 49 := by decide
theorem Ej_one_value : E_jF params deltaF gap (ρ₁ params gap) = 44 := by decide
theorem Bc_two_value : B_cF params deltaF gap (ρΓ params gap) = 48 := by decide
theorem Bc_one_value : B_cF params deltaF gap (ρ₁ params gap) = 43 := by decide
theorem Dc_two_value : D_cF params (ρΓ params gap) = 37 := by decide
theorem Dc_one_value : D_cF params (ρ₁ params gap) = 32 := by decide
theorem reset_two_value : B_resetF params deltaF gap (ρΓ params gap) = 325 := by decide
theorem reset_one_value : B_resetF params deltaF gap (ρ₁ params gap) = 295 := by decide
theorem reset_value : B'_resetF params deltaF gap = 295 := by decide
theorem healing_two_value : B_H2F params deltaF gap = 333 := by decide
theorem healing_one_value : B_H1F params deltaF gap = 303 := by decide
theorem healing_value : B_HF params deltaF gap = 303 := by decide

theorem healing_strict_horizon : B_HF params deltaF gap < horizon := by decide
theorem healing_horizon : env.t_GST + B_HF params deltaF gap ≤ horizon := by decide
theorem reset_horizon : env.t_GST + B'_resetF params deltaF gap ≤ horizon := by decide
theorem reset_full_horizon :
    env.t_GST + B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ ≤ horizon := by
  decide
theorem reset_full_budget : B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ = 303 := by
  decide
theorem action_three_value : params.actionTime 3 = 42 := by decide
theorem renewed_three_budget :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ = 66 := by decide
theorem renewed_three_horizon :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ ≤ horizon := by decide

theorem livenessBound : LivenessBoundW params deltaF := ⟨by decide⟩



open AvailableChain.SimplexFG
open AvailableChain.V2.D.Engine

abbrev Object := (fgsa params unitCodec).Object
abbrev Event := V2.Event (Fin 1) Object
abbrev FixtureNode := (fgsa params unitCodec).State

def mkRun (es : List Event) : V2.D.Run (Fin 1) (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := horizon
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- One tick, then one delivery of each released object, in release order. -/
def batch (acc : List Event × FixtureNode) (n : Nat) : List Event × FixtureNode :=
  let out := V2.D.tick env (mkRun []) acc.2 0 (n : Time)
  (acc.1 ++ [.tick 0 (n : Time)] ++ out.2.map (fun o => .deliver 0 o (n : Time)),
    out.2.foldl (fgsa params unitCodec).process out.1)

/-- The cached node avoids a repeated fold of all preceding events. -/
def runPrefix (n : Nat) : List Event × FixtureNode :=
  (List.range n).foldl batch ([], (fgsa params unitCodec).init)

def run := mkRun (runPrefix 305).1

theorem runPrefix_zero : runPrefix 0 = ([], (fgsa params unitCodec).init) := rfl

theorem runPrefix_succ (n : Nat) : runPrefix (n + 1) = batch (runPrefix n) n := by
  simp [runPrefix, List.range_succ, List.foldl_append]

theorem duties_length (t : Time) : (duties params t).length ≤ 1 := by
  have hp : SA.proposalTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) := rfl
  have hv : SA.voteTime params.toParams (params.slotOf t) = 4 * (params.slotOf t : Time) + 1 := rfl
  have ha : params.actionTime ((params.slotOf t - 1) / params.R) =
      12 * (((params.slotOf t - 1) / params.R : Nat) : Time) + 6 := by
    change 4 * ((((params.slotOf t - 1) / params.R) * 3 : Nat) : Time) + 6 = _
    push_cast
    ring
  have hpa (a b : Time) : 4 * a ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  have hva (a b : Time) : 4 * a + 1 ≠ 12 * b + 6 := by dsimp only [Time] at *; omega
  simp only [duties, hp, hv, ha]
  split_ifs <;> simp_all
  · exact hpa (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)
  · exact hva (params.slotOf t : Time) ((params.slotOf t - 1 : Nat) / (params.R : Time))
      (by dsimp only [Time] at *; omega)

theorem ownSeats_single (d : RunDuty) :
    (mkRun []).ownSeats (RunDuty.signLabel d) 0 = [⟨0, by cases d <;> exact Nat.one_pos⟩] := by
  cases d <;> change (List.finRange 1).filter (fun _ => decide ((0 : Fin 1) = 0)) = [0]
  all_goals decide

theorem released_length (nd : FixtureNode) (t : Time) :
    (V2.D.tick env (mkRun []) nd 0 t).2.length ≤ 1 := by
  change (((duties params t).flatMap (fun d =>
    ((mkRun []).ownSeats (RunDuty.signLabel d) 0).filterMap (fun i =>
      ((fgsa params unitCodec).act ((fgsa params unitCodec).clock nd t) d ()).map
        (fun m => (⟨.seat (RunDuty.signLabel d) i, m⟩ : Object))))) ++ []).length ≤ 1
  rw [List.append_nil]
  have h := duties_length t
  cases he : duties params t with
  | nil => simp
  | cons d ds =>
    have hds : ds = [] := by simpa [he] using h
    rw [hds]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ownSeats_single,
      List.filterMap_cons, List.filterMap_nil]
    split <;> simp

theorem prefix_events_time (n : Nat) :
    ∀ e ∈ (runPrefix n).1, ∃ m < n, e.time = (m : Time) ∧
      (e = .tick 0 (m : Time) ∨ ∃ o, e = .deliver 0 o (m : Time)) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    intro e he
    simp only [batch, List.mem_append, List.mem_singleton, List.mem_map] at he
    rcases he with (he | he) | ⟨o, _, he⟩
    · obtain ⟨m, hm, ht, he⟩ := ih e he
      exact ⟨m, by omega, ht, he⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inl rfl⟩
    · subst e; exact ⟨n, Nat.lt_succ_self n, rfl, Or.inr ⟨o, rfl⟩⟩

theorem prefix_ticks (n m : Nat) (hm : m < n) : .tick 0 (m : Time) ∈ (runPrefix n).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [runPrefix_succ]
    by_cases hmn : m < n
    · exact List.mem_append_left _ (List.mem_append_left _ (ih hmn))
    · have he : m = n := by omega
      subst m
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem prefix_mono {n m : Nat} (h : n ≤ m) :
    (runPrefix n).1.IsPrefix (runPrefix m).1 := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact List.prefix_refl _
  | succ m ih =>
    by_cases hn : n ≤ m
    · apply (ih hn).trans
      rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.append_assoc]
      exact List.prefix_append _ _
    · have : n = m + 1 := by omega
      subst n; exact List.prefix_refl _

theorem step_constant (nd : FixtureNode) (e : Event) :
    V2.D.World.step env (mkRun []) (fun _ => nd) e =
      fun _ => match e with
      | .restart _ t => (fgsa params unitCodec).restore ((fgsa params unitCodec).durable nd) t
      | .tick _ t => (V2.D.tick env (mkRun []) nd 0 t).1
      | .deliver _ o _ => (fgsa params unitCodec).process nd o := by
  funext v
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  cases e with
  | restart w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | tick w t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl
  | deliver w o t => have hw : w = 0 := Subsingleton.elim _ _; subst w; rfl

theorem fold_deliveries (os : List Object) (nd : FixtureNode) (t : Time) :
    (os.map (fun o => (.deliver 0 o t : Event))).foldl
        (V2.D.World.step env (mkRun [])) (fun _ => nd) =
      fun _ => os.foldl (fgsa params unitCodec).process nd := by
  induction os generalizing nd with
  | nil => rfl
  | cons o os ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, step_constant]
    exact ih _

/-- The cached node equals the engine fold, for every prefix length. -/
theorem prefix_cached (n : Nat) :
    (runPrefix n).1.foldl (V2.D.World.step env (mkRun [])) V2.D.World.init =
      fun _ => (runPrefix n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runPrefix_succ]
    simp only [batch, List.foldl_append, ih]
    rw [List.foldl_cons, List.foldl_nil, step_constant, fold_deliveries]

def batchEvents (n : Nat) : List Event :=
  [.tick 0 (n : Time)] ++
    (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2.map
      (fun o => .deliver 0 o (n : Time))

theorem prefix_flat (n : Nat) :
    (runPrefix n).1 = (List.range n).flatMap batchEvents := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runPrefix_succ, batch, List.range_succ, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, batchEvents]
    rw [← ih, List.append_assoc]

theorem tick_at (n : Nat) (hn : n < 305) :
    run.events[(runPrefix n).1.length]? = some (.tick 0 (n : Time)) := by
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 305 by omega)
  change (runPrefix 305).1[(runPrefix n).1.length]? = _
  rw [← he, runPrefix_succ]
  simp [batch, List.append_assoc]

theorem state_before_tick (n : Nat) (hn : n < 305) :
    V2.D.Run.stateBefore env run (runPrefix n).1.length = fun _ => (runPrefix n).2 := by
  obtain ⟨tail, he⟩ := prefix_mono (show n ≤ 305 by omega)
  unfold V2.D.Run.stateBefore
  change ((runPrefix 305).1.take (runPrefix n).1.length).foldl
      (V2.D.World.step env run) V2.D.World.init = _
  rw [← he]
  simp only [List.take_append, List.take_length, Nat.sub_self, List.take_zero,
    List.append_nil]
  exact prefix_cached n

theorem emits_at_tick (n : Nat) (hn : n < 305) :
    V2.D.Run.emitsAt env run (runPrefix n).1.length =
      (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  rw [V2.D.Run.emitsAt, tick_at n hn, state_before_tick n hn]
  rfl

theorem immediate_delivery (n : Nat) (hn : n < 305) (o : Object)
    (ho : o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2) :
    run.events[(runPrefix n).1.length + 1]? = some (.deliver 0 o (n : Time)) := by
  have hos : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 = [o] := by
    have hl := released_length (runPrefix n).2 (n : Time)
    cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
    | nil => simp [he] at ho
    | cons a as =>
      have has : as = [] := by simpa [he] using hl
      rw [he, has] at ho
      rw [has]
      exact (List.mem_singleton.mp ho) ▸ rfl
  obtain ⟨tail, he⟩ := prefix_mono (show n + 1 ≤ 305 by omega)
  change (runPrefix 305).1[(runPrefix n).1.length + 1]? = _
  rw [← he, runPrefix_succ]
  simp [batch, hos, List.append_assoc]

theorem prefix_strict (n : Nat) :
    (runPrefix n).1.Pairwise (fun e f => e.key < f.key) := by
  induction n with
  | zero => simp [runPrefix_zero]
  | succ n ih =>
    rw [runPrefix_succ]
    dsimp only [batch]
    rw [List.append_assoc, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · have hl := released_length (runPrefix n).2 (n : Time)
      cases he : (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 with
      | nil => simp
      | cons o os =>
        have hos : os = [] := by simpa [he] using hl
        rw [hos]
        simp [V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.lt_iff]
    · intro e he f hf
      obtain ⟨m, hm, ht, _⟩ := prefix_events_time n e he
      have hft : f.time = (n : Time) := by
        simp only [List.mem_append, List.mem_singleton, List.mem_map] at hf
        rcases hf with rfl | ⟨o, _, rfl⟩ <;> rfl
      apply Prod.Lex.lt_iff.mpr
      left
      change e.time < f.time
      rw [ht, hft]
      exact_mod_cast hm

theorem nvSchedule : V2.D.ScheduleWellFormed env run where
  horizon_nonneg := le_of_lt horizon_pos
  sorted := (prefix_strict 305).imp (fun h => le_of_lt h)
  nodup := by
    have hne : run.events.Pairwise (fun e f => e ≠ f) :=
      (prefix_strict 305).imp (fun h he => by rw [he] at h; exact lt_irrefl _ h)
    exact hne
  in_horizon := by
    intro e he
    obtain ⟨m, hm, ht, _⟩ := prefix_events_time 305 e he
    rw [ht]
    change 0 ≤ (m : Time) ∧ (m : Time) ≤ 304
    exact ⟨Int.natCast_nonneg m, by dsimp only [Time] at *; omega⟩
  honest_only := by intro e _; exact Finset.mem_univ _
  tick_public := by
    intro v t he
    obtain ⟨m, _, ht, _⟩ := prefix_events_time 305 (.tick v t) he
    exact ⟨m, by simpa only [V2.Event.time, env, Int.mul_one] using ht⟩
  tick_total := by
    intro v _ t _ ht hh _
    have hv : v = 0 := Subsingleton.elim _ _
    subst v
    change t ≤ 304 at hh
    have he : t = (t.toNat : Time) := (Int.toNat_of_nonneg ht).symm
    rw [he]
    exact prefix_ticks 305 t.toNat (by dsimp only [Time] at *; omega)

theorem noRestart : V2.D.NoRestart run := by
  intro i v t hi
  obtain ⟨_, _, _, he⟩ := prefix_events_time 305 (.restart v t) (List.mem_of_getElem? hi)
  rcases he with he | ⟨o, he⟩ <;> cases he

set_option maxHeartbeats 2000000 in
-- Index uniqueness uses the symbolic prefix proof through the concrete run type.
theorem delivery_source {i : Nat} {v : Fin 1} {o : Object} {t : Time}
    (hi : run.events[i]? = some (.deliver v o t)) :
    ∃ n : Nat, n < 305 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length + 1 ∧
      o ∈ (V2.D.tick env (mkRun []) (runPrefix n).2 0 (n : Time)).2 := by
  have hm := List.mem_of_getElem? hi
  rw [show run.events = (runPrefix 305).1 from rfl, prefix_flat] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < 305 := List.mem_range.mp hn
  simp only [batchEvents, List.mem_append, List.mem_singleton, List.mem_map] at hm
  rcases hm with he | ⟨a, ha, he⟩
  · cases he
  · cases he
    have hd := immediate_delivery n hn' o ha
    obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
    have hij : i = (runPrefix n).1.length + 1 :=
      (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)
    exact ⟨n, hn', rfl, hij, ha⟩

theorem tick_source {i : Nat} {v : Fin 1} {t : Time}
    (hi : run.events[i]? = some (.tick v t)) :
    ∃ n : Nat, n < 305 ∧ t = (n : Time) ∧ i = (runPrefix n).1.length := by
  obtain ⟨n, hn, ht, _⟩ := prefix_events_time 305 (.tick v t) (List.mem_of_getElem? hi)
  change t = (n : Time) at ht
  have hv : v = 0 := Subsingleton.elim _ _
  subst v
  have hd := tick_at n hn
  rw [← ht] at hd
  obtain ⟨hil, hei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hej⟩ := List.getElem?_eq_some_iff.mp hd
  exact ⟨n, hn, ht,
    (nvSchedule.nodup.getElem_inj_iff (hi := hil) (hj := hjl)).mp (hei.trans hej.symm)⟩

-- NV4 uses the same fixture and the prefix invariants above.
def actionNode (r : Nat) : FixtureNode :=
  (fgsa params unitCodec).clock (runPrefix (params.actionTime r).toNat).2
    (params.actionTime r)

def rowAtAction (r : Nat) : Option RowPayload :=
  (attest params (actionNode r).st (actionNode r).record ⟨0, params.nPos⟩).1

def sourceAtAction (r : Nat) : Option (FGBlock (Fin params.n)) :=
  (fgInputs params (actionNode r).st).1

def rowEntry (r : Nat) : Option (Nat × BlockId) :=
  (rowAtAction r).bind (fun a => namedEntry a.height_pair)

-- These evaluations use at most 43 ticks, through cached nodes.
#eval (runPrefix 31).2.st.fg.h_max
#eval (List.range 4).map (fun r => (r, params.actionTime r, (rowEntry r).map Prod.fst,
  (sourceAtAction r).map (fun C => (C.slot, (heightView params C).h))))

/-- The time filter of any longer prefix gives the same shorter prefix. -/
theorem prefix_cut (n m : Nat) (hn : n ≤ m) :
    (runPrefix m).1.filter (fun e => decide (e.time < (n : Time))) = (runPrefix n).1 := by
  induction m generalizing n with
  | zero =>
    have he : n = 0 := by omega
    subst n
    rfl
  | succ m ih =>
    by_cases hnm : n ≤ m
    · rw [runPrefix_succ]
      dsimp only [batch]
      rw [List.filter_append, List.filter_append, ih n hnm]
      have ht : decide ((m : Time) < (n : Time)) = false := by
        apply decide_eq_false
        exact not_lt.mpr (by exact_mod_cast hnm)
      have hd : ((V2.D.tick env (mkRun []) (runPrefix m).2 0 (m : Time)).2.map
          (fun o => (.deliver 0 o (m : Time) : Event))).filter
            (fun e => decide (e.time < (n : Time))) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e he
        obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
        change ¬ decide ((m : Time) < (n : Time)) = true
        rw [ht]
        decide
      rw [hd]
      simp only [List.filter_cons, List.filter_nil]
      change ((runPrefix n).1 ++
        (if decide ((m : Time) < (n : Time)) = true then [.tick 0 (m : Time)] else [])) ++ [] = _
      rw [ht]
      simp
    · have he : n = m + 1 := by omega
      subst n
      apply List.filter_eq_self.mpr
      intro e he
      obtain ⟨k, hk, ht, _⟩ := prefix_events_time (m + 1) e he
      rw [ht]
      exact decide_eq_true (by exact_mod_cast hk)

/-- The inclusive read at tick n is the cached node after tick n. -/
theorem read_prefix (n : Nat) (hn : n < 305) :
    V2.D.Run.readAt env run (n : Time) = fun _ => (runPrefix (n + 1)).2 := by
  have hp : run.events.filter (fun e => decide (e.time ≤ (n : Time))) =
      (runPrefix (n + 1)).1 := by
    have he : (fun e : Event => decide (e.time ≤ (n : Time))) =
        (fun e : Event => decide (e.time < ((n + 1 : Nat) : Time))) := by
      funext e
      have hp : e.time ≤ (n : Time) ↔ e.time < ((n + 1 : Nat) : Time) := by
        dsimp only [Time]
        push_cast
        omega
      exact decide_eq_decide.mpr hp
    rw [he]
    exact prefix_cut (n + 1) 305 (by omega)
  unfold V2.D.Run.readAt
  rw [hp]
  exact prefix_cached (n + 1)

theorem frontier_cached (n : Nat) (hn : n < 305) :
    honestFrontier params unitCodec env run (n : Time) = (runPrefix (n + 1)).2.st.fg.h_max := by
  unfold honestFrontier
  rw [read_prefix n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix (n + 1)).2.st.fg.h_max) = _
  simp

theorem frontier_idx_cached (n : Nat) (hn : n < 305) :
    frontierAtIdx params unitCodec env run (runPrefix n).1.length =
      (runPrefix n).2.st.fg.h_max := by
  unfold frontierAtIdx storeAt
  rw [state_before_tick n hn]
  change (Finset.univ : Finset (Fin 1)).sup (fun _ => (runPrefix n).2.st.fg.h_max) = _
  simp

set_option maxHeartbeats 2000000 in
-- The kernel checks the cached state after the first 31 ticks.
theorem nvCachedFrontier : (runPrefix 31).2.st.fg.h_max = 2 := by decide +kernel

theorem nvFrontier : honestFrontier params unitCodec env run 30 = 2 :=
  (frontier_cached 30 (by decide)).trans nvCachedFrontier

theorem nvFrontierAtIdx : frontierAtIdx params unitCodec env run (runPrefix 31).1.length = 2 :=
  (frontier_idx_cached 31 (by decide)).trans nvCachedFrontier

theorem action_read (r : Nat) (hr : (params.actionTime r).toNat < 305) :
    postClock env run 0 (params.actionTime r) = some (actionNode r) := by
  have ht : ((params.actionTime r).toNat : Time) = params.actionTime r := by
    apply Int.toNat_of_nonneg
    change 0 ≤ 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1
    omega
  have he := tick_at (params.actionTime r).toNat hr
  rw [ht] at he
  rw [postClock_def, preTick_def,
    fgsa_tickIdx_of_event params unitCodec env run nvSchedule he,
    Option.map_some, state_before_tick (params.actionTime r).toNat hr]
  rfl

theorem source_read (r : Nat) (hr : (params.actionTime r).toNat < 305) :
    actionSourceFG params unitCodec env run 0 r = some (sourceAtAction r) := by
  rw [actionSourceFG_def, action_read r hr]
  rfl

-- The reset source and wire come from the round-3 action itself.
def resetSource : FGBlock (Fin params.n) := (sourceAtAction 3).getD .genesis
def resetRow : RowWire params.n :=
  ⟨.seat .fg ⟨0, params.nPos⟩, (rowAtAction 3).getD (.vote ⟨.empty, none⟩)⟩

def w : HealingWitness :=
  ⟨0, 30, 2, 3, 9, eraseFG resetSource, 0, .genesis⟩

set_option maxHeartbeats 2000000 in
-- The kernel checks the source at tick 42, using its cached prefix.
theorem nvSourceHeight : (sourceAtAction 3).map (fun C => (heightView params C).h) = some 3 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete source slot at tick 42.
theorem nvSourceSlot : resetSource.slot = 9 := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete row and source entry at tick 42.
theorem nvResetRowFields :
    namedEntry resetRow.payload.height_pair =
      some (3, (heightView params resetSource).T_h.root) := by decide +kernel

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete wire emission at tick 42.
theorem nvResetEmissionWire :
    toWire params (ofRow params resetRow) ∈
      (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2.map (toWire params) := by
  decide +kernel

theorem nvResetEmission :
    ofRow params resetRow ∈ (V2.D.tick env (mkRun []) (runPrefix 42).2 0 42).2 := by
  obtain ⟨o, ho, he⟩ := List.mem_map.mp nvResetEmissionWire
  have heq : o = ofRow params resetRow := (toWireEquiv params).injective he
  exact heq ▸ ho

theorem nvSource : sourceAtAction 3 = some resetSource := by
  have h := nvSourceHeight
  cases he : sourceAtAction 3 with
  | none => rw [he] at h; cases h
  | some C => simp only [resetSource, he, Option.getD_some]

theorem nvResetHeight : (heightView params resetSource).h = 3 := by
  have h := nvSourceHeight
  rw [nvSource] at h
  exact Option.some.inj h

theorem nvHonestResetRow :
    HonestRowAt params unitCodec env run (runPrefix 42).1.length 0 3 resetRow := by
  refine ⟨Finset.mem_univ _, tick_at 42 (by decide), ?_⟩
  rw [emits_at_tick 42 (by decide)]
  exact nvResetEmission

set_option maxHeartbeats 2000000 in
-- The kernel checks only the first three action prefixes.
theorem nvEarlySourceHeights :
    ((sourceAtAction 0).map (fun C => (heightView params C).h),
     (sourceAtAction 1).map (fun C => (heightView params C).h),
     (sourceAtAction 2).map (fun C => (heightView params C).h)) =
      (none, some 1, some 2) := by decide +kernel

/-- Every named honest row in rounds 0--2 has height at most 2. -/
theorem nvEarlyRowCap {j : Nat} {y : Fin 1} {r h : Nat} {a : RowWire params.n} {e : BlockId}
    (ha : HonestRowAt params unitCodec env run j y r a)
    (he : namedEntry a.payload.height_pair = some (h, e)) (hr : r < 3) : h ≤ 2 := by
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  have hb : (params.actionTime r).toNat < 305 := by
    change (4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1).toNat < 305
    push_cast
    omega
  obtain ⟨C, _, hC, hh, _⟩ := emittedName_window params unitCodec env run nvSchedule ha he
  rw [source_read r hb] at hC
  have hs : (sourceAtAction r).map (fun C => (heightView params C).h) = some h := by
    rw [Option.some.inj hC]
    exact congrArg some hh.symm
  have h0 : (sourceAtAction 0).map (fun C => (heightView params C).h) = none :=
    congrArg Prod.fst nvEarlySourceHeights
  have h1 : (sourceAtAction 1).map (fun C => (heightView params C).h) = some 1 :=
    congrArg (fun z => z.2.1) nvEarlySourceHeights
  have h2 : (sourceAtAction 2).map (fun C => (heightView params C).h) = some 2 :=
    congrArg (fun z => z.2.2) nvEarlySourceHeights
  have hc : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · rw [h0] at hs
    cases hs
  · rw [h1] at hs
    have hh' : h = 1 := (Option.some.inj hs).symm
    omega
  · rw [h2] at hs
    have hh' : h = 2 := (Option.some.inj hs).symm
    omega

theorem nvRowCap : ∀ j y r a h e t,
    HonestRowAt params unitCodec env run j y r a →
    run.events[j]? = some (.tick y t) → t ≤ 30 →
    namedEntry a.payload.height_pair = some (h, e) → h ≤ 2 := by
  intro j y r a h e t ha ht hcut he
  have heq : params.actionTime r = t :=
    (V2.Event.tick.inj (Option.some.inj (ha.2.1.symm.trans ht))).2
  have hr : r < 3 := by
    rw [← heq] at hcut
    change 4 * 1 * ((r * 3 : Nat) : Int) + 6 * 1 ≤ 30 at hcut
    push_cast at hcut
    omega
  exact nvEarlyRowCap ha he hr

/-- With GST zero, no source vote is strictly before GST. -/
theorem nvOldRowsEmpty : oldRowHeights params unitCodec env run = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro h ⟨j, y, r, a, e, ha, he, ht⟩
  change 4 * 1 * ((r * 3 : Nat) : Int) + 1 < 6 at ht
  have hr : r = 0 := by push_cast at ht; omega
  subst r
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  obtain ⟨C, _, hC, _, _⟩ := emittedName_window params unitCodec env run nvSchedule ha he
  rw [source_read 0 (by decide)] at hC
  have hn : sourceAtAction 0 = none := by decide +kernel
  rw [hn] at hC
  cases hC

theorem nvMu : muOf params unitCodec env run = 1 := by
  rw [muOf_def, nvOldRowsEmpty]
  simp

theorem nvHeightRow : HeightRow params unitCodec env run 3 3 :=
  ⟨(runPrefix 42).1.length, 0, resetRow, (heightView params resetSource).T_h.root,
    nvHonestResetRow, nvResetRowFields⟩

theorem nvResetFirst : ∀ r, HeightRow params unitCodec env run r 3 → 3 ≤ r := by
  rintro r ⟨j, y, a, e, ha, he⟩
  by_contra hn
  have h := nvEarlyRowCap ha he (by omega)
  omega

-- Close these terms only for the final structure assembly. Earlier proofs need
-- their defining equations to check the concrete row and source reads.
attribute [irreducible] resetSource resetRow

theorem nvFresh : ∃ j y, ∃ (a : RowWire params.n) (C : FGBlock (Fin params.n)),
    HonestRowAt params unitCodec env run j y 3 a ∧
    namedEntry a.payload.height_pair = some (3, (heightView params C).T_h.root) ∧
    actionSourceFG params unitCodec env run y 3 = some (some C) ∧
    eraseFG C = eraseFG resetSource ∧ (heightView params C).h = 3 := by
  have hs : actionSourceFG params unitCodec env run 0 3 = some (some resetSource) :=
    (source_read 3 (by decide)).trans (congrArg some nvSource)
  exact ⟨(runPrefix 42).1.length, 0, resetRow, resetSource, nvHonestResetRow,
    nvResetRowFields, hs, Eq.refl _, nvResetHeight⟩

set_option maxHeartbeats 2000000 in
-- The assembly checks the concrete witness after the short-prefix source proof.
/-- All 13 reset fields hold on the unchanged one-node run. -/
theorem nvH0Reset : H0Reset params unitCodec env run w where
  rG_after := by decide
  rG_first := by intro r _; exact Nat.zero_le r
  cut := by decide
  frontier := nvFrontier.symm
  rowCap := nvRowCap
  mu_le := by change muOf params unitCodec env run ≤ 2; rw [nvMu]; decide
  cut_lower := by decide
  cut_upper := by decide
  reset_row := nvHeightRow
  reset_first := nvResetFirst
  label := rfl
  fresh := nvFresh
  synchronous := by decide

#eval (List.range 4).map (fun r => (r, (runPrefix (params.actionTime r).toNat).1.length,
  (sourceAtAction r).map (fun C => (C.slot, (eraseFG C).depth,
    (heightView params C).T_h.slot))))
#eval (runPrefix 31).1.length
#eval (eraseFG resetSource).slot

#print axioms nvFrontier
#print axioms nvFrontierAtIdx
#print axioms nvRowCap
#print axioms nvResetFirst
#print axioms nvH0Reset

end AvailableChain.FGSA.Run.Tests.NonVacuity.HealingReset
end
