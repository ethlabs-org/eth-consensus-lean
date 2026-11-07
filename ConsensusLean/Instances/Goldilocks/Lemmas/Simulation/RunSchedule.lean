module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Release
import ConsensusLean.Lemmas.Model.Constant
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Simulation: the simulating trace's schedule and credentials

The initial state, timing, wake/restart schedule and block/message credentials of `simTrace`,
from a valid engine run. `RunBlocks` continues with payload credentials and blocks of cuts;
`Run` assembles the Goldilocks run. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `LocalRun` -/

/-- Each honest node starts from the initial node state. -/
theorem simTrace_init :
    ∀ y ∈ honestKeys S rho, (simTrace S rho hn).init y = Node.init _ :=
  fun y _ => simTrace_init_eq S rho hn y

/-! ### The engine's schedule and the trace's cuts -/

omit [DecidableEq V] in
theorem ownKey_key (y : Fin (Fintype.card V)) : rho.ownKey (rho.key y) = y :=
  rho.key.symm_apply_apply y

omit [DecidableEq V] in
theorem ownKey_key' (v : V) : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v

omit [DecidableEq V] in
theorem key_of_ownKey {v : V} {y : Fin (Fintype.card V)} (h : rho.ownKey v = y) :
    v = rho.key y := by
  rw [← h]; exact (rho.key.apply_symm_apply v).symm

private theorem event_awake (hv : rho.ExecutionValid) {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some ev) : E.awake ev.node ev.time = true := by
  have hm := List.mem_of_getElem? he
  cases ev with
  | tick v t => exact hv.tick_awake v t hm
  | deliver v o t => exact hv.deliver_awake v o t hm
  | restart v t => exact (hv.restart_at_wake v t hm).2.1

private theorem index_le {i i' k k' : Nat} (hk : cutMap S rho hn i ≤ k)
    (hk' : k' < cutMap S rho hn (i' + 1)) (h : k ≤ k') : i ≤ i' := by
  by_contra hlt
  have := cutMap_mono S rho hn (show i' + 1 ≤ i by omega)
  omega

private theorem labelled_iff (k : Nat) :
    (simTrace S rho hn).label k ≠ none ↔ k < (allCuts S rho hn).length := by
  simp [simTrace_label]

private theorem time_bounds (hv : rho.ExecutionValid) (k : Nat) :
    0 ≤ (simTrace S rho hn).time k ∧ (simTrace S rho hn).time k ≤ rho.horizon + 1 := by
  cases hk : (allCuts S rho hn)[k]? with
  | none =>
    rw [(simTrace_of_getElem?_none S rho hn hk).2]
    exact ⟨by linarith only [hv.horizon_nonneg], le_rfl⟩
  | some r =>
    have hl : (simTrace S rho hn).label k ≠ none := by rw [simTrace_label, hk]; simp
    obtain ⟨-, i, ev, -, he, -, -, -, -, ht, -⟩ := simTrace_cut S rho hn hl
    rw [ht]
    have h := hv.in_horizon ev (List.mem_of_getElem? he)
    exact ⟨h.1, by linarith only [h.2]⟩

/-- Protocol actions, unlike observation filler, stay within the engine horizon. -/
theorem simTrace_labelled_time_le (hv : rho.ExecutionValid) {k : Nat}
    (hl : (simTrace S rho hn).label k ≠ none) :
    (simTrace S rho hn).time k ≤ rho.horizon := by
  obtain ⟨_, _, ev, _, he, _, _, _, _, ht, _⟩ := simTrace_cut S rho hn hl
  rw [ht]
  exact (hv.in_horizon ev (List.mem_of_getElem? he)).2

theorem awake_iff' (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace S rho hn).awake y t ↔ E.awake (rho.key y) t = true ∧ 0 ≤ t ∧
      t ≤ rho.horizon := by
  rw [simTrace_awake_iff, awakeAt_iff]

/-- Canonical labelled coverage cannot extend its explicit observation horizon. -/
theorem simTrace_inHorizon_le (hv : rho.ExecutionValid) {t : Time}
    (ht : (simTrace S rho hn).InHorizon t) : t ≤ rho.horizon := by
  obtain ⟨k, hk, htk⟩ := (simTrace_inHorizon_iff S rho hn t).mp ht
  rcases hk with hk | hk
  · have hl : (simTrace S rho hn).label k ≠ none := by
      simpa only [simTrace_label, cutLabel_eq] using hk
    have ht' : t ≤ (simTrace S rho hn).time k := by
      simpa only [simTrace_time, cutTime_eq] using htk
    exact ht'.trans (simTrace_labelled_time_le S rho hn hv hl)
  · exact hk

/-- Environment wakefulness transports throughout the canonical observation horizon. -/
theorem simTrace_awake_to (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, E.awake (rho.key y) t = true → 0 ≤ t →
      (simTrace S rho hn).InHorizon t → (simTrace S rho hn).awake y t := by
  intro y hy t hw ht hh
  exact simTrace_awake_before_horizon S rho hn y hy t hw ht
    (simTrace_inHorizon_le S rho hn hv hh)

/-- The first cut of a group: a cut at position `0` of an engine event at the group's node and
time, whose phase is the group's event's. -/
private theorem groupAt_start {y : Fin (Fintype.card V)} {j : Nat} {t : Time}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hg : (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e) :
    ∃ r i ev, rho.events[i]? = some ev ∧ cutMap S rho hn i ≤ j ∧ j < cutMap S rho hn (i + 1) ∧
      (eventCuts S rho hn i)[j - cutMap S rho hn i]? = some r ∧ r.pos = 0 ∧
      rho.ownKey ev.node = y ∧ ev.time = t ∧ e.phase = ev.phase := by
  obtain ⟨hne, hcuts, -⟩ := hg
  obtain ⟨hn0, ht0, -, hp0, hl0⟩ := hcuts 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hn0 ht0 hp0 hl0
  have hl : (simTrace S rho hn).label j ≠ none := by rw [hl0]; simp
  obtain ⟨r, i, ev, -, he, h1, h2, hidx, hnode, htime, hpos, hlab⟩ := simTrace_cut S rho hn hl
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  have hc : r.label = c := by
    have := hlab.symm.trans hl0
    rw [Option.some.injEq] at this
    rw [this, List.getElem_of_eq hcs]
    rfl
  exact ⟨r, i, ev, he, h1, h2, hidx, hpos ▸ hp0, hnode.symm.trans hn0, htime.symm.trans ht0,
    phase_of_pos_zero S rho hn he (List.mem_of_getElem? hidx) (hpos ▸ hp0) (by rw [hc]; exact hcs)⟩

/-- An engine restart's cut is a restart of the trace, at the restart's time. -/
private theorem restart_at {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    (simTrace S rho hn).RestartAt (rho.ownKey v) (cutMap S rho hn i) ∧
      (simTrace S rho hn).time (cutMap S rho hn i) = t ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i + 1 := by
  obtain ⟨hsucc, r, hr, hn', ht, ℓ, hl, hc⟩ := restart_getElem? S rho hn he
  refine ⟨⟨ℓ, ⟨?_, ?_⟩, hc⟩, ?_, hsucc⟩
  · rw [simTrace_node, hr]; exact hn'
  · rw [simTrace_label, hr, Option.map_some, hl]
  · rw [simTrace_time, hr]; exact ht

/-- Between a time when a function on times is `false` and a later one when it is `true`, it
switches on: some `w` in between is `true` with `w - 1` `false`. -/
private theorem exists_wake (f : Time → Bool) {u t : Time} (hu : f u = false) (ht : f t = true)
    (h : u ≤ t) : ∃ w, u < w ∧ w ≤ t ∧ f w = true ∧ f (w - 1) = false := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, t = u + n := ⟨(t - u).toNat, by unfold Time at *; omega⟩
  clear h
  induction n with
  | zero => simp [hu] at ht
  | succ n ih =>
    by_cases hft : f (u + n) = true
    · obtain ⟨w, h1, h2, h3⟩ := ih hft
      exact ⟨w, h1, by push_cast at h2 ⊢; linarith only [h2], h3⟩
    · refine ⟨u + (n + 1 : Nat), by push_cast; linarith only [Int.natCast_nonneg n], le_rfl, ht,
        ?_⟩
      have : u + ((n + 1 : Nat) : Int) - 1 = u + n := by push_cast; ring
      rw [this]
      simpa using hft

/-- Cuts are at times from `0` on. -/
theorem simTrace_time_nonneg (hv : rho.ExecutionValid) :
    ∀ i, 0 ≤ (simTrace S rho hn).time i :=
  fun k => (time_bounds S rho hn hv k).1

/-- The cut order is by time. -/
theorem simTrace_time_mono (hv : rho.ExecutionValid) : Monotone (simTrace S rho hn).time := by
  intro k k' hkk'
  cases hk' : (allCuts S rho hn)[k']? with
  | none =>
    rw [(simTrace_of_getElem?_none S rho hn hk').2]
    exact (time_bounds S rho hn hv k).2
  | some r' =>
    have hl' : (simTrace S rho hn).label k' ≠ none := by rw [simTrace_label, hk']; simp
    have hl : (simTrace S rho hn).label k ≠ none :=
      (labelled_iff S rho hn k).mpr (lt_of_le_of_lt hkk' ((labelled_iff S rho hn k').mp hl'))
    obtain ⟨-, i, ev, -, he, h1, -, -, -, ht, -⟩ := simTrace_cut S rho hn hl
    obtain ⟨-, i', ev', -, he', -, h2', -, -, ht', -⟩ := simTrace_cut S rho hn hl'
    rw [ht, ht']
    rcases (index_le S rho hn h1 h2' hkk').lt_or_eq with h | rfl
    · rcases keyLe_of_lt S rho hv he he' h with h | h
      · exact h.le
      · exact h.1.le
    · rw [he] at he'
      cases he'
      exact le_rfl

/-- Finitely many labelled cuts in every bounded interval. -/
theorem simTrace_finite (_hv : rho.ExecutionValid) :
    ∀ T : Time,
      {i | (simTrace S rho hn).label i ≠ none ∧ (simTrace S rho hn).time i ≤ T}.Finite := by
  intro T
  exact (Set.finite_Iio (allCuts S rho hn).length).subset
    fun k hk => (labelled_iff S rho hn k).mp hk.1

/-- At one time, across the honest nodes, the groups are in phase order. -/
theorem simTrace_phase_order (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ y' ∈ honestKeys S rho, ∀ j j' t e e',
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e →
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y' j' t e' → j < j' →
        e.phase ≤ e'.phase := by
  intro y _ y' _ j j' t e e' hg hg' hjj'
  obtain ⟨-, i, ev, he, h1, -, -, -, -, ht, hph⟩ := groupAt_start S rho hn hg
  obtain ⟨-, i', ev', he', -, h2', -, -, -, ht', hph'⟩ := groupAt_start S rho hn hg'
  rw [hph, hph']
  rcases (index_le S rho hn h1 h2' hjj'.le).lt_or_eq with h | rfl
  · rcases keyLe_of_lt S rho hv he he' h with h | h
    · rw [ht, ht'] at h; exact absurd h (lt_irrefl _)
    · exact h.2
  · rw [he] at he'
    cases he'
    exact le_rfl

/-- A tick is at a public time. -/
theorem simTrace_tick_public (_hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t,
      (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t →
      (S.params (pubOf E) hn).toParams.IsPublic t := by
  rintro y _ j t ⟨x, hg⟩
  obtain ⟨_, i, ev, he, -, -, hidx, -, -, ht, hph⟩ := groupAt_start S rho hn hg
  cases ev with
  | tick v t' =>
    simp only [Model.Event.time] at ht
    subst ht
    by_contra hp
    rw [eventCuts_tick_other S rho hn i v t' he hp] at hidx
    simp at hidx
  | deliver v o t' => simp [Event.phase, Model.Event.phase] at hph
  | restart v t' => simp [Event.phase, Model.Event.phase] at hph

/-- One tick per node and time. -/
theorem simTrace_tick_unique (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j j' t,
      (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t →
      (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j' t → j = j' := by
  rintro y _ j j' t ⟨x, hg⟩ ⟨x', hg'⟩
  obtain ⟨r, i, ev, he, h1, -, hidx, hr0, hk, ht, hph⟩ := groupAt_start S rho hn hg
  obtain ⟨r', i', ev', he', h1', -, hidx', hr0', hk', ht', hph'⟩ := groupAt_start S rho hn hg'
  have hpos : ∀ {i j : Nat} {v : V} {s : Time} {r : CutRec (S.params (pubOf E) hn) (S.ro _)},
      rho.events[i]? = some (.tick v s) → cutMap S rho hn i ≤ j →
      (eventCuts S rho hn i)[j - cutMap S rho hn i]? = some r → r.pos = 0 →
      j = cutMap S rho hn i := by
    intro i j v s r he h1 hidx hr0
    obtain ⟨hm, rfl⟩ := List.getElem?_eq_some_iff.mp hidx
    have := pos_getElem_eventCuts_of_group S rho hn (Or.inl he) _ hm
    omega
  cases ev with
  | tick v s =>
    cases ev' with
    | tick v' s' =>
      simp only [Model.Event.node, Model.Event.time] at hk hk' ht ht'
      have hvv : v = v' := (key_of_ownKey S rho hk).trans (key_of_ownKey S rho hk').symm
      subst hvv ht ht'
      have := index_eq_of_events S rho hv he he'
      subst this
      rw [hpos he h1 hidx hr0, hpos he' h1' hidx' hr0']
    | deliver => simp [Event.phase, Model.Event.phase] at hph'
    | restart => simp [Event.phase, Model.Event.phase] at hph'
  | deliver => simp [Event.phase, Model.Event.phase] at hph
  | restart => simp [Event.phase, Model.Event.phase] at hph

/-- An honest node is called only while awake. -/
theorem simTrace_awake_of_call (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).IsCall y i →
      (simTrace S rho hn).awake y ((simTrace S rho hn).time i) := by
  rintro y _ i ⟨c, hnode, hlab⟩
  have hl : (simTrace S rho hn).label i ≠ none := by rw [hlab]; simp
  obtain ⟨-, i₀, ev, -, he, -, -, -, hn', ht, -⟩ := simTrace_cut S rho hn hl
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  refine (awake_iff' S rho hn y _).mpr
    ⟨?_, (time_bounds S rho hn hv i).1, simTrace_labelled_time_le S rho hn hv hl⟩
  rw [ht, ← hkey]
  exact event_awake S rho hv he

/-- The first call of an honest node after it was asleep is a restart. -/
theorem simTrace_restart_of_sleep (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i (u : Time), (simTrace S rho hn).IsCall y i → 0 ≤ u →
      u < (simTrace S rho hn).time i → ¬ (simTrace S rho hn).awake y u →
      (∀ j < i, (simTrace S rho hn).IsCall y j → (simTrace S rho hn).time j < u) →
        (simTrace S rho hn).RestartAt y i := by
  rintro y hy i u ⟨c, hnode, hlab⟩ hu0 hut hsleep hprev
  have hl : (simTrace S rho hn).label i ≠ none := by rw [hlab]; simp
  obtain ⟨-, i₀, ev, -, he, h1, h2, -, hn', ht, -⟩ := simTrace_cut S rho hn hl
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  have hwt : E.awake (rho.key y) ev.time = true := hkey ▸ event_awake S rho hv he
  have hwu : E.awake (rho.key y) u = false := by
    by_contra h
    exact hsleep ((awake_iff' S rho hn y u).mpr
      ⟨by simpa using h, hu0, hut.le.trans (simTrace_labelled_time_le S rho hn hv hl)⟩)
  obtain ⟨w, huw, hwt', hw1, hw2⟩ :=
    exists_wake (E.awake (rho.key y)) hwu hwt (by rw [← ht]; exact hut.le)
  have hth := (hv.in_horizon ev (List.mem_of_getElem? he)).2
  obtain ⟨ir, hir⟩ :=
    List.mem_iff_getElem?.mp
      (hv.wake_restart _ w
        (by linarith only [hu0, huw]) (by linarith only [hwt', hth])
        (by simpa only [rho.faultyAt_eq_zero hf] using (mem_honestKeys_iff S rho y).mp hy)
        ⟨hw1, hw2⟩)
  obtain ⟨hR, hRt, hsucc⟩ := restart_at S rho hn hir
  rw [ownKey_key] at hR
  have hge : i ≤ cutMap S rho hn ir := by
    by_contra h
    have := hprev _ (by omega) ⟨_, hR.choose_spec.1⟩
    rw [hRt] at this
    linarith only [this, huw]
  have hir₀ : ir = i₀ := by
    rcases lt_trichotomy ir i₀ with h | h | h
    · have := cutMap_mono S rho hn (show ir + 1 ≤ i₀ from h)
      omega
    · exact h
    · rcases keyLe_of_lt S rho hv he hir h with h' | ⟨h', h''⟩
      · exact absurd hwt' (not_le.mpr h')
      · cases ev with
        | restart v s =>
          simp only [Model.Event.node, Model.Event.time] at hkey h'
          subst hkey h'
          exact absurd (index_eq_of_events S rho hv he hir) (by omega)
        | tick => simp [Model.Event.phase] at h''
        | deliver => simp [Model.Event.phase] at h''
  subst hir₀
  have : i = cutMap S rho hn ir := by omega
  subst this
  exact hR

/-- A wake is a restart. -/
theorem simTrace_restart_at_wake (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ u v : Time, 0 ≤ u → u < v → ¬ (simTrace S rho hn).awake y u →
      (simTrace S rho hn).awake y v →
        ∃ k, (simTrace S rho hn).RestartAt y k ∧ u < (simTrace S rho hn).time k ∧
          (simTrace S rho hn).time k ≤ v := by
  intro y hy u v hu0 huv hsu hav
  obtain ⟨hwv, -, hvh⟩ := (awake_iff' S rho hn y v).mp hav
  have hwu : E.awake (rho.key y) u = false := by
    by_contra h
    exact hsu ((awake_iff' S rho hn y u).mpr ⟨by simpa using h, hu0, huv.le.trans hvh⟩)
  obtain ⟨w, huw, hwv', hw1, hw2⟩ := exists_wake _ hwu hwv huv.le
  obtain ⟨ir, hir⟩ :=
    List.mem_iff_getElem?.mp
      (hv.wake_restart _ w
        (by linarith only [hu0, huw]) (by linarith only [hwv', hvh])
        (by simpa only [rho.faultyAt_eq_zero hf] using (mem_honestKeys_iff S rho y).mp hy)
        ⟨hw1, hw2⟩)
  obtain ⟨hR, ht, -⟩ := restart_at S rho hn hir
  rw [ownKey_key] at hR
  exact ⟨_, hR, by rw [ht]; exact huw, by rw [ht]; exact hwv'⟩

/-- A restart is a wake. -/
theorem simTrace_sleep_of_restart (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).RestartAt y i →
      ∃ u : Time, 0 ≤ u ∧ u < (simTrace S rho hn).time i ∧ ¬ (simTrace S rho hn).awake y u ∧
        ∀ j < i, (simTrace S rho hn).IsCall y j → (simTrace S rho hn).time j < u := by
  rintro y hy i ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩
  have hl : (simTrace S rho hn).label i ≠ none := by rw [hlab]; simp
  obtain ⟨r, i₀, ev, -, he, h1, h2, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn he (List.mem_of_getElem? hidx) hrl hcall
  simp only [Model.Event.node, Model.Event.time] at hn' ht
  have hkey : v = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  subst hkey
  obtain ⟨ht0, -, hw2⟩ := hv.restart_at_wake _ _ (List.mem_of_getElem? he)
  obtain ⟨-, -, hsucc⟩ := restart_at S rho hn he
  refine ⟨t - 1, Int.le_sub_one_of_lt ht0, by rw [ht]; exact sub_one_lt t, fun h => ?_,
    fun j hj hcj => ?_⟩
  · have := ((awake_iff' S rho hn y _).mp h).1
    rw [hw2] at this
    exact Bool.false_ne_true this
  · obtain ⟨c, hnj, hlj⟩ := hcj
    have hlj' : (simTrace S rho hn).label j ≠ none := by rw [hlj]; simp
    obtain ⟨-, i₁, ev₁, -, he₁, h1₁, h2₁, -, hn₁, ht₁, -⟩ := simTrace_cut S rho hn hlj'
    have hkey₁ : ev₁.node = rho.key y := key_of_ownKey S rho (hn₁.symm.trans hnj)
    have hw₁ : E.awake (rho.key y) ev₁.time = true := hkey₁ ▸ event_awake S rho hv he₁
    have hle := simTrace_time_mono S rho hn hv hj.le
    rw [ht₁, ht] at hle
    rw [ht₁]
    have hi₁ : i₁ ≤ i₀ := index_le S rho hn h1₁ h2 hj.le
    have hne : ev₁.time ≠ t := by
      intro heq
      rcases hi₁.lt_or_eq with hlt | rfl
      · rcases keyLe_of_lt S rho hv he₁ he hlt with h' | ⟨-, h''⟩
        · have : ev₁.time < t := h'
          exact this.ne heq
        · cases ev₁ with
          | restart v' s =>
            simp only [Model.Event.node, Model.Event.time] at hkey₁ heq
            subst hkey₁ heq
            exact absurd (index_eq_of_events S rho hv he₁ he) (by omega)
          | tick => simp [Model.Event.phase] at h''
          | deliver => simp [Model.Event.phase] at h''
      · omega
    have hne' : ev₁.time ≠ t - 1 := by
      intro heq
      rw [heq, hw2] at hw₁
      exact Bool.false_ne_true hw₁
    unfold Time at *
    omega

/-- An honest node is asleep one tick before each of its restarts. -/
theorem simTrace_asleep_before_restart (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).RestartAt y i →
      ¬ (simTrace S rho hn).awake y ((simTrace S rho hn).time i - 1) := by
  rintro y hy i ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ h
  have hl : (simTrace S rho hn).label i ≠ none := by rw [hlab]; simp
  obtain ⟨r, i₀, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn he (List.mem_of_getElem? hidx) hrl hcall
  simp only [Model.Event.node, Model.Event.time] at hn' ht
  have hkey : v = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  subst hkey
  obtain ⟨-, -, hw2⟩ := hv.restart_at_wake _ _ (List.mem_of_getElem? he)
  have hw := ((awake_iff' S rho hn y _).mp h).1
  rw [ht, hw2] at hw
  exact Bool.false_ne_true hw

private theorem tick_block_fields {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    {B : Blk sp} {acc : Bool} {k : Nat}
    (hk : k < (exec proposer dg self st t (.tick x)).2.length)
    (hc : (exec proposer dg self st t (.tick x)).2[k] = .fg (.block B acc)) :
    B.proposer = self ∧ B.RootOk dg ∧ B.parent ≠ none ∧ k ≠ 0 := by
  have hzero : k ≠ 0 := by
    intro h
    subst k
    simp [exec, onTick, runSteps, tickSteps, tickStep, acCall] at hc
  have hm := List.getElem_mem hk
  rw [hc] at hm
  rw [show (exec proposer dg self st t (.tick x)).2 = (onTick proposer dg self st t x).2
    from rfl, onTick_cuts] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · simp [tickStep, acCall] at hm
    · simp only [tickStep] at hm
      split_ifs at hm
      · split at hm
        · simp [acProposal] at hm
        · rename_i d p hdp
          simp only [proposeBlock, onBlock] at hm
          split_ifs at hm
          · simp [acProposal] at hm
          · split at hm <;> simp [acCall, acProposal] at hm <;>
              obtain ⟨rfl, _⟩ := hm <;> exact ⟨rfl, rfl, by simp [mkBlock], hzero⟩
      · simp at hm
  · simp only [tickStep] at hm
    split at hm
    · simp [acToFG] at hm
    · simp only [attest, List.mem_cons, acToFG, reduceCtorEq, false_or] at hm
      split at hm <;> simp [onAttestation] at hm

omit [DecidableEq V] in
theorem blockObj_fields {B C : Blk (S.params (pubOf E) hn)}
    (hB : B.parent ≠ none) (hC : C.parent ≠ none)
    (hrB : B.RootOk (digestOf S rho)) (hrC : C.RootOk (digestOf S rho))
    (he : blockObj (S.params (pubOf E) hn) B = blockObj (S.params (pubOf E) hn) C) : B = C := by
  have hh := congrArg Model.Obj.msg he
  have ha := congrArg Model.Obj.auth he
  simp only [blockObj, Model.Obj.msg, Model.Msg.item.injEq] at hh
  simp only [blockObj, Model.Obj.auth, Model.Auth.signed.injEq] at ha
  have hp := congrArg (fun h => parentRoot S.genesisRoot h.parent) hh
  have hs := congrArg Header.pos hh
  have hx := congrArg Header.input hh
  have hi := congrArg (fun h => decodeInfo (Fintype.card V) h.info) hh
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hB
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hC
  simp only [headerOf, hb, hc, parentRoot_parentRef] at hp
  simp only [headerOf, decodeInfo_encodeInfo, Option.some.injEq, Prod.mk.injEq] at hi
  have hparent : B.parent = C.parent := by simpa [hb, hc] using hp
  change B.slot = C.slot at hs
  change B.input = C.input at hx
  have hroot : B.root = C.root := by
    change B.root = digestOf S rho B.parent B.slot B.input B.fgPayload B.acPayload at hrB
    rw [hrB, hparent, hs, hx, hi.1, hi.2]
    exact hrC.symm
  have hv := ha.1
  cases B; cases C
  simp_all

private theorem ownBlock_of_tick_cut {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    {B : Blk (S.params (pubOf E) hn)} {acc : Bool}
    (hc : Cut.fg (.block B acc) ∈ (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).OwnBlockAt B.proposer k B := by
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  obtain ⟨hself, _, _, hm0⟩ := tick_block_fields _ _ _ _ _ _ hm hcm
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hm' : m < (eventCuts S rho hn i).length := by
    rw [hEC, length_groupRecs]; exact hm
  have hr := allCuts_getElem?_add S rho hn i m (List.getElem?_eq_some_iff.mp he).1 hm'
  rw [List.getElem?_eq_getElem hm'] at hr
  have hgr := getElem_groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
    (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v t))) m
    (show m < _ from by rw [length_groupRecs]; exact hm)
  have hr' : (allCuts S rho hn)[cutMap S rho hn i + m]? = some
      ((groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))))[m]'
          (by rw [length_groupRecs]; exact hm)) :=
    by simpa only [hEC] using hr
  refine ⟨cutMap S rho hn i + m, ?_, ⟨acc, ?_, ?_⟩, ?_⟩
  · rw [cutMap_succ]; omega
  · rw [simTrace_node, hr']; exact hgr.1.trans hself.symm
  · rw [simTrace_label, hr']; exact congrArg some (hgr.2.2.2.2.trans hcm)
  · rw [simTrace_pos, hr']; simpa only [Option.elim_some, hgr.2.2.2.1] using hm0

private theorem released_block_cut (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time}
    (hs : rho.SendsAt v i t) (hv' : v ∉ rho.faultyAt 0)
    {B : Blk (S.params (pubOf E) hn)} (hpar : B.parent ≠ none)
    (hroot : B.RootOk (digestOf S rho))
    (hb : blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).OwnBlockAt B.proposer k B := by
  have hhead : ∀ seen ob,
      blockObj (S.params (pubOf E) hn) B ∉ relHead S rho v seen ob := by
    intro seen ob h
    obtain ⟨q, _, heq⟩ := mem_relHead S rho h
    have hh := congrArg Model.Obj.msg heq
    cases hh
  rcases hs with he | ⟨o, he⟩
  · by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, _, hR4, _⟩ :=
        tick_public_analysis S rho hn hv hv' he hp (preNode_releasable S rho hn hf hv hv' he)
      rw [hr] at hb
      have hb4 : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
        rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ _ hb)
              · exact hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ _ hb)
              · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
                all_goals have hh := congrArg Model.Obj.msg heq; cases hh
          · exact False.elim (hhead _ _ hb)
        · have hh := hG _ hb
          cases hh
      rw [hR4] at hb4
      obtain ⟨C, acc, hc, hb⟩ := mem_blockObjs.mp hb4
      obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
      obtain ⟨_, hrC, hpC, _⟩ := tick_block_fields _ _ _ _ _ _ hm hcm
      have hBC := blockObj_fields S rho hn hpar hpC hroot hrC hb
      subst C
      exact ownBlock_of_tick_cut S rho hn he hp hc
    · rcases tick_other_releases S rho hn hv hv' he hp _ hb with h | h
      · exact False.elim (hhead _ _ h)
      · cases h
  · have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [deliverDuties_eq S t ht] at hb
      erw [Model.Run.runDuties_cons, Model.Run.runDuties_nil] at hb
      simp only [List.append_nil] at hb
      rcases dutyStep_poll_sub S rho hn v _ _ _ hb with
        ⟨b, _, heq⟩ | ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
      all_goals have hh := congrArg Model.Obj.msg heq; cases hh
    · have hh := gossip_unsigned S rho _ _ _ _ hb
      cases hh

/-- A block of an honest proposer that an honest node processes is the proposer's own block,
processed by the proposer at or before (the engine's `Credentials`: a delivered block object
signed by an honest key was released by that key's node). -/
theorem simTrace_block_unforgeable (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i B, (simTrace S rho hn).BlockCallAt y i B →
      B.proposer ∈ honestKeys S rho → ∃ j ≤ i, (simTrace S rho hn).OwnBlockAt B.proposer j B := by
  rintro y _ k B ⟨acc, hnode, hlab⟩ hhon
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, hn', _, hpos, hlab'⟩ :=
    simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    rw [eventCuts_tick_public S rho hn i v t he hp] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, hp', hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    obtain ⟨hself, _, _, hm0⟩ := tick_block_fields _ _ _ _ _ _
      (by rwa [length_groupRecs] at hm) (hc.symm.trans hrl)
    exact ⟨k, le_rfl, ⟨acc, hn'.trans hself.symm, hlab⟩, by rwa [hpos, hp']⟩
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', ho, hce, m, hm, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := hc.symm.trans hrl
    have heq : e = .block B := by
      have hmem := List.getElem_mem hm
      rw [hcut] at hmem
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | block B' =>
        simp only [exec, onBlock] at hmem
        split_ifs at hmem
        · simp at hmem
        · split at hmem <;>
            simp only [acCall, List.mem_cons, Cut.fg.injEq, FGLabel.block.injEq, reduceCtorEq,
              List.not_mem_nil, or_self, or_false] at hmem <;>
            simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, not_lt]
      | message => simp [exec, onMessage, acCall] at hmem
      | attestation => simp [exec, onAttestation] at hmem
      | restart => simp [exec, Node.restart, acCall] at hmem
    subst e
    obtain rfl := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
    obtain ⟨hroot, hpar, _⟩ := decodeBlock_wire (decodeBlock_of_canonEvent hce)
    have hh : rootOf (Model.digests rho.hash o) (headerOf _ B) =
        some (rho.hash (headerOf _ B)) := by
      apply rootOf_digests_of_mem
      exact List.mem_filterMap.mpr ⟨blockObj _ B, mem_delivered ho, rfl⟩
    rw [hh, Option.map_some, Option.some.injEq] at hroot
    have hroot' : B.RootOk (digestOf S rho) := by
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hpar
      rw [digestOf_eq]
      change B.root = dgOf rho.hash S.genesisRoot B.parent B.slot B.input B.fgPayload B.acPayload
      erw [dgOf_eq, ← hroot]
      simp only [headerOf, hp]
    have hsign : rho.signerOf (blockObj (S.params (pubOf E) hn) B) =
        some (rho.key B.proposer) := rfl
    rw [mem_honestKeys_iff] at hhon
    obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _
      (contains_of_mem_delivered ho) (rho.key B.proposer) hsign
      (by simpa only [rho.faultyAt_eq_zero hf] using hhon)
    obtain ⟨q, hq, hown⟩ := released_block_cut S rho hn hf hv hs hhon hpar hroot' hb
    have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
      cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
    exact ⟨q, by omega, hown⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

private theorem delivery_block_authorized {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (Q : Blk sp → Prop) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat),
      (∀ o ∈ os, ∀ B, o = blockObj sp B → Q B) →
      ∀ r ∈ deliverRecs proposer dg hs self t i os st sub, r.pos = 0 →
      ∀ B acc, r.label = .fg (.block B acc) → Q B := by
  intro os
  induction os with
  | nil => intro st sub _ r hr; simp [deliverRecs_nil] at hr
  | cons o os ih =>
    intro st sub hQ r hr hpos B acc hl
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hr
      exact ih st (sub + 1) (fun o ho => hQ o (List.mem_cons_of_mem _ ho)) r hr hpos B acc hl
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        obtain ⟨_, _, _, hp, hlabel⟩ := getElem_groupRecs proposer dg self st t _ e k hk
        have hk0 : k = 0 := hp.symm.trans hpos
        subst k
        obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_length_pos
          (show 0 < (exec proposer dg self st t e).2.length by rwa [length_groupRecs] at hk)
        rw [List.getElem_of_eq hcs] at hlabel
        have hc : c = .fg (.block B acc) := hlabel.symm.trans hl
        subst c
        have hevent := exec_head_fg (P := sp.toParams) (A := goldilocksNode sp ro)
          (ℓ := .block B acc) proposer dg self st t e hcs
        rcases hevent with ⟨B', acc', he', hh⟩ | ⟨a, _, hh⟩
        · cases hh
          rw [he'] at he
          rcases canonEvent_eq_some (sp := sp) (ro := ro) he with
            ⟨B', hh, ho⟩ | ⟨v, hh, _⟩ | ⟨a, hh, _⟩
          · cases hh
            exact hQ o List.mem_cons_self B ho
          · cases hh
          · cases hh
        · cases hh
      · exact ih _ (sub + 1) (fun o ho => hQ o (List.mem_cons_of_mem _ ho)) r hr hpos B acc hl

/-- Engine `Credentials` assigns every delivered proposal, including a faulty signer's,
to the selected proposer. Decode the group's source object and use `selValid_proposer` to
identify its signer with the run schedule. This is separate from honest-source unforgeability. -/
theorem simTrace_proposerCredential (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t B,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t (.block B) →
        B.proposer = runProposer S rho hn B.slot := by
  intro y _ j t B hg
  obtain ⟨r, i, ev, he, hstart, _, hidx, hpos, _, _, hphase⟩ := groupAt_start S rho hn hg
  obtain ⟨hne, hcuts, _⟩ := hg
  obtain ⟨_, _, _, _, hl⟩ := hcuts 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hl
  have hr : (allCuts S rho hn)[j]? = some r := by
    have h := allCuts_getElem?_add S rho hn i (j - cutMap S rho hn i)
      (List.getElem?_eq_some_iff.mp he).1 (List.getElem?_eq_some_iff.mp hidx).1
    rw [Nat.add_sub_cancel' hstart, hidx] at h
    exact h
  cases ev with
  | tick v t' => simp [Event.phase, Model.Event.phase] at hphase
  | restart v t' => simp [Event.phase, Model.Event.phase] at hphase
  | deliver v o t' =>
    have hrmem := List.mem_of_getElem? hidx
    rw [eventCuts_deliver S rho hn i v o t' he] at hrmem
    have hrlabel : (simTrace S rho hn).label j = some r.label := by
      rw [simTrace_label, hr]
      rfl
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    rw [hrlabel, Option.some.injEq, List.getElem_of_eq hcs] at hl
    obtain ⟨acc, hc⟩ := exec_block_head _ _ _ _ _ B hcs
    apply delivery_block_authorized _ _ _ _ _ _
      (fun B => B.proposer = runProposer S rho hn B.slot) _ _ _ ?_ r hrmem hpos B acc
      (hl.trans hc)
    intro x hx B' hxB
    have hcred := hv.credentials i v o t' he x (contains_of_mem_delivered hx)
      B'.proposer (.proposer B'.slot) (by rw [hxB]; rfl)
    rw [selValid_proposer S rho hn hv.selValid] at hcred
    exact Finset.mem_singleton.mp hcred

private theorem emit_of_record {i : Nat} {ev}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) {ℓ} (hl : r.label = .ac ℓ)
    {em} (hem : em ∈ ℓ.emits) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).EmitAt (rho.ownKey ev.node) k em.msg := by
  have hnode := (mem_eventCuts S rho hn he hr).1
  obtain ⟨m, hm, hrm⟩ := List.getElem_of_mem hr
  have hk := allCuts_getElem?_add S rho hn i m (List.getElem?_eq_some_iff.mp he).1 hm
  rw [List.getElem?_eq_getElem hm, hrm] at hk
  refine ⟨cutMap S rho hn i + m, ?_, ℓ, ⟨?_, ?_⟩, em, hem, rfl⟩
  · rw [cutMap_succ]; omega
  · rw [simTrace_node, hk]; exact hnode
  · rw [simTrace_label, hk]; exact congrArg some hl

private theorem emit_of_tick_body {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {m : Vote (Fintype.card V)}
    (hm : Body.vote (encodeVote m) ∈ emitted (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
  obtain ⟨ℓ, hc, em, hem, rfl⟩ := mem_emitted.mp hm
  obtain ⟨q, hq, hcq⟩ := List.getElem_of_mem hc
  have hq' : q < (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length := by
    rwa [length_groupRecs]
  apply emit_of_record S rho hn he (r := (groupRecs (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v t))))[q]) ?_ ?_ hem
  · rw [eventCuts_tick_public S rho hn i v t he hp]; exact List.getElem_mem hq'
  · exact (getElem_groupRecs _ _ _ _ _ _ _ q hq').2.2.2.2.trans hcq

/-- A released canonical own vote comes from an emission before the event's end cut. -/
theorem released_vote_cut (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time}
    (hs : rho.SendsAt v i t) (hv' : v ∉ rho.faultyAt 0) {m : Vote (Fintype.card V)}
    (hb : voteObj m ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
  have hbody : ∀ b, voteObj m = pollObj S rho v b → b = Body.vote (encodeVote m) := by
    intro b heq
    exact (Model.Msg.data.inj (congrArg Model.Obj.msg heq)).symm
  rcases hs with he | ⟨o, he⟩
  · have hnil := outbox_empty S rho hn hv v i
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, hQ, hR4, _⟩ :=
        tick_public_analysis S rho hn hv hv' he hp (preNode_releasable S rho hn hf hv hv' he)
      have hq : ∀ seen ob, (∀ b, ob = some b → b ∈ Q) →
          voteObj m ∈ relHead S rho v seen ob →
          ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
        intro seen ob hmem hb
        obtain ⟨b, hob, heq⟩ := mem_relHead S rho hb
        have hbq := hmem b hob
        rw [hbody b heq, hQ] at hbq
        rcases List.mem_append.mp hbq with hbq | hbq
        · exact emit_of_tick_body S rho hn he hp hbq
        · exact False.elim (vote_not_mem_attBodies _ _ hbq)
      rw [hr] at hb
      rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · obtain ⟨b, hb, _⟩ := mem_relHead S rho hb
              simp [hnil] at hb
            · rw [hR4] at hb
              obtain ⟨B, acc, _, heq⟩ := mem_blockObjs.mp hb
              have hh := congrArg Model.Obj.msg heq
              cases hh
          · rcases List.mem_append.mp hb with hb | hb
            · exact hq _ _ (fun _ h => List.mem_of_mem_head? h) hb
            · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
              all_goals have hh := congrArg Model.Obj.msg heq; cases hh
        · exact hq _ _ (fun _ h => List.mem_of_mem_tail (List.mem_of_mem_head? h)) hb
      · have hh := hG _ hb; cases hh
    · rcases tick_other_releases S rho hn hv hv' he hp _ hb with hb | hb
      · obtain ⟨b, hb, _⟩ := mem_relHead S rho hb
        simp [hnil] at hb
      · cases hb
  · have ht0 := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    have hnow : (stateAt S rho hn v i).now = t :=
      (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [deliverDuties_eq S t ht0] at hb
      erw [Model.Run.runDuties_cons, Model.Run.runDuties_nil] at hb
      simp only [List.append_nil] at hb
      rcases dutyStep_poll_sub S rho hn v _ _ _ hb with
        ⟨b, hb, heq⟩ | ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
      · have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
          (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
        change (pollPre (process ((rho.stateBefore i v).st.1 hn) o
          (Model.digests rho.hash o))).outbox.head? = some b at hb
        rw [← stateAt_eq S rho hn v i] at hb
        rw [pollPre_eq, hf] at hb
        have hb' := List.mem_of_mem_head? hb
        rw [hbody b heq] at hb'
        rcases process_outbox_source (runProposer S rho hn) (digestOf S rho)
          (Model.digests rho.hash o) t i _ (stateAt S rho hn v i) 0 hnow _ hb' with
          hb | ⟨r, hr, ℓ, hl, em, hem, heq⟩
        · rw [outbox_empty S rho hn hv v i] at hb; cases hb
        · have hm := congrArg (decodeVote (Fintype.card V)) (Body.vote.inj heq)
          rw [decodeVote_encodeVote, decodeVote_encodeVote] at hm
          have hm := Option.some.inj hm
          rw [hm]
          apply emit_of_record S rho hn he (r := r) ?_ hl hem
          rw [eventCuts_deliver S rho hn i v o t he, ← self_eq_ownKey S rho hn v i]
          exact hr
      · have hh := congrArg Model.Obj.msg heq; cases hh
      · have hh := congrArg Model.Obj.msg heq; cases hh
    · have hh := gossip_unsigned S rho _ _ _ _ hb; cases hh

/-- An AC message of an honest signer that an honest node receives was emitted by that signer's
node at an earlier cut. -/
theorem simTrace_msg_unforgeable (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i (m : Vote (Fintype.card V)),
      (simTrace S rho hn).MsgCallAt y i m → m.val ∈ honestKeys S rho →
        ∃ j < i, (simTrace S rho hn).EmitAt m.val j m := by
  rintro y _ k m ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ hhon
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, _, _, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  obtain ⟨v, o, t, rfl⟩ := eq_deliver_of_cut S rho hn he hmem (Or.inr ⟨ℓ, m, hrl, hcall⟩)
  rw [eventCuts_deliver S rho hn i v o t he] at hmem
  obtain ⟨o', e, st', ho, hce, q, hq, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
  have hcut := List.getElem_mem hq
  rw [← hc, hrl] at hcut
  have heq : e = .message m := by
    cases e with
    | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
    | message m' =>
      simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at hcut
      subst ℓ
      cases hcall
      rfl
    | block B =>
      simp only [exec, onBlock] at hcut
      split_ifs at hcut
      · simp at hcut
      · split at hcut <;> simp [acCall] at hcut
        subst ℓ
        cases hcall
    | attestation => simp [exec, onAttestation] at hcut
    | restart =>
      simp only [exec, Node.restart, acCall, List.mem_singleton, Cut.ac.injEq] at hcut
      subst ℓ
      cases hcall
  subst e
  have ho' : o' = voteObj m := by
    rcases canonEvent_eq_some hce with ⟨_, h, _⟩ | ⟨m', h, ho⟩ | ⟨_, h, _⟩
    · cases h
    · cases h; exact ho
    · cases h
  subst o'
  rw [mem_honestKeys_iff] at hhon
  obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _ (contains_of_mem_delivered ho)
    (rho.key m.val) rfl (by simpa only [rho.faultyAt_eq_zero hf] using hhon)
  obtain ⟨q, hq, hem⟩ := released_vote_cut S rho hn hf hv hs hhon hb
  have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
    cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
  exact ⟨q, by omega, by simpa only [ownKey_key] using hem⟩

end Consensus.Goldilocks.Simulation

end
