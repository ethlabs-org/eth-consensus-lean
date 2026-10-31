module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Release
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable

set_option linter.style.longFile 1600

public section

/-! # Goldilocks Refinement: the simulating trace is a run, and the engine agrees with it

The steps of `EngineSimulatesNode` over the trace `simTrace` and the cut map `cutMap` built from
a valid engine run (`Trace`): one theorem per field of `GoldilocksRun` (the trace is a run of the
Goldilocks protocol at the engine's digest, for the honest keys) and one per field of
`Simulates` (the engine's events are the trace's groups, the engine's node states are the trace's
states, the engine releases and relays what the trace signs, emits and admits). The engine-side
facts they rest on are the steps of `Steps` and the engine-state facts of `Relay`; the shape's
pure facts those of `Shape`; where each cut of the trace comes from, `Cuts`.

Each theorem is a named step; the `sorry` ones are open. `Simulation` assembles them. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `LocalRun` -/

/-- Each honest node starts from the initial node state. -/
theorem simTrace_init :
    ∀ y ∈ honestKeys S rho, (simTrace S rho hn).init y = Node.init _ :=
  fun y _ => simTrace_init_eq S rho hn y

/-! ### The engine's schedule and the trace's cuts -/

omit [DecidableEq V] in
private theorem ownKey_key (y : Fin (Fintype.card V)) : rho.ownKey (rho.key y) = y :=
  rho.key.symm_apply_apply y

omit [DecidableEq V] in
private theorem ownKey_key' (v : V) : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v

omit [DecidableEq V] in
private theorem key_of_ownKey {v : V} {y : Fin (Fintype.card V)} (h : rho.ownKey v = y) :
    v = rho.key y := by
  rw [← h]; exact (rho.key.apply_symm_apply v).symm

private theorem event_awake (hv : rho.ExecutionValid) {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
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
    0 ≤ (simTrace S rho hn).time k ∧ (simTrace S rho hn).time k ≤ rho.horizon := by
  cases hk : (allCuts S rho hn)[k]? with
  | none =>
    rw [(simTrace_of_getElem?_none S rho hn hk).2]
    exact ⟨hv.horizon_nonneg, le_rfl⟩
  | some r =>
    have hl : (simTrace S rho hn).label k ≠ none := by rw [simTrace_label, hk]; simp
    obtain ⟨-, i, ev, -, he, -, -, -, -, ht, -⟩ := simTrace_cut S rho hn hl
    rw [ht]
    exact hv.in_horizon ev (List.mem_of_getElem? he)

private theorem awake_iff' (y : Fin (Fintype.card V)) (t : Time) :
    (simTrace S rho hn).awake y t ↔ E.awake (rho.key y) t = true ∧ 0 ≤ t ∧
      ∃ k, (simTrace S rho hn).label k ≠ none ∧ t ≤ (simTrace S rho hn).time k := by
  rw [simTrace_awake_iff, awakeAt_iff]
  simp only [cutLabel_eq, cutTime_eq, simTrace_label, simTrace_time]

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
      exact ⟨w, h1, by push_cast at h2 ⊢; linarith, h3⟩
    · refine ⟨u + (n + 1 : Nat), by push_cast; linarith, le_rfl, ht, ?_⟩
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
    · rcases keyLe_of_index_lt S rho hv he he' h with h | h
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
  · rcases keyLe_of_index_lt S rho hv he he' h with h | h
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
  refine (awake_iff' S rho hn y _).mpr ⟨?_, (time_bounds S rho hn hv i).1, i, hl, le_rfl⟩
  rw [ht, ← hkey]
  exact event_awake S rho hv he

/-- The first call of an honest node after it was asleep is a restart. -/
theorem simTrace_restart_of_sleep (hv : rho.ExecutionValid) :
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
    exact hsleep ((awake_iff' S rho hn y u).mpr ⟨by simpa using h, hu0, i, hl, hut.le⟩)
  obtain ⟨w, huw, hwt', hw1, hw2⟩ :=
    exists_wake (E.awake (rho.key y)) hwu hwt (by rw [← ht]; exact hut.le)
  have hth := (hv.in_horizon ev (List.mem_of_getElem? he)).2
  obtain ⟨ir, hir⟩ :=
    List.mem_iff_getElem?.mp
      (hv.wake_restart _ hy w (by linarith) (by linarith) ⟨hw1, hw2⟩)
  obtain ⟨hR, hRt, hsucc⟩ := restart_at S rho hn hir
  rw [ownKey_key] at hR
  have hge : i ≤ cutMap S rho hn ir := by
    by_contra h
    have := hprev _ (by omega) ⟨_, hR.choose_spec.1⟩
    rw [hRt] at this
    linarith
  have hir₀ : ir = i₀ := by
    rcases lt_trichotomy ir i₀ with h | h | h
    · have := cutMap_mono S rho hn (show ir + 1 ≤ i₀ from h)
      omega
    · exact h
    · rcases keyLe_of_index_lt S rho hv he hir h with h' | ⟨h', h''⟩
      · have : ev.time < w := h'
        linarith
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
theorem simTrace_restart_at_wake (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ u v : Time, 0 ≤ u → u < v → ¬ (simTrace S rho hn).awake y u →
      (simTrace S rho hn).awake y v →
        ∃ k, (simTrace S rho hn).RestartAt y k ∧ u < (simTrace S rho hn).time k ∧
          (simTrace S rho hn).time k ≤ v := by
  intro y hy u v hu0 huv hsu hav
  obtain ⟨hwv, -, k, hk, hvk⟩ := (awake_iff' S rho hn y v).mp hav
  have hwu : E.awake (rho.key y) u = false := by
    by_contra h
    exact hsu ((awake_iff' S rho hn y u).mpr ⟨by simpa using h, hu0, k, hk, by linarith⟩)
  obtain ⟨w, huw, hwv', hw1, hw2⟩ := exists_wake _ hwu hwv huv.le
  have hvh : v ≤ rho.horizon := hvk.trans (time_bounds S rho hn hv k).2
  obtain ⟨ir, hir⟩ :=
    List.mem_iff_getElem?.mp
      (hv.wake_restart _ hy w (by linarith) (by linarith) ⟨hw1, hw2⟩)
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
  refine ⟨t - 1, Int.le_sub_one_of_lt ht0, by linarith, fun h => ?_, fun j hj hcj => ?_⟩
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
      · rcases keyLe_of_index_lt S rho hv he₁ he hlt with h' | ⟨-, h''⟩
        · have : ev₁.time < t := h'
          linarith
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

/-- A block of an honest proposer that an honest node processes is the proposer's own block,
processed by the proposer at or before (the engine's `Credentials`: a delivered block object
signed by an honest key was released by that key's node). -/
theorem simTrace_block_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i B, (simTrace S rho hn).BlockCallAt y i B →
      B.proposer ∈ honestKeys S rho → ∃ j ≤ i, (simTrace S rho hn).OwnBlockAt B.proposer j B := by
  sorry

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

/-- An attestation of an honest signer that an honest node processes was signed by that signer
at an earlier cut. -/
theorem simTrace_att_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i a,
      ((simTrace S rho hn).AttCallAt y i a ∨
        ∃ B, (simTrace S rho hn).BlockCallAt y i B ∧ a ∈ B.fgPayload) →
      a.val ∈ honestKeys S rho → ∃ j < i, (simTrace S rho hn).SignAt a.val j a := by
  sorry

/-- An AC message of an honest signer that an honest node receives was emitted by that signer's
node at an earlier cut. -/
theorem simTrace_msg_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i (m : Vote (Fintype.card V)),
      (simTrace S rho hn).MsgCallAt y i m → m.val ∈ honestKeys S rho →
        ∃ j < i, (simTrace S rho hn).EmitAt m.val j m := by
  sorry

/-! ## `GoldilocksRun` -/

omit [DecidableEq V] in
/-- The genesis block's root is the digest of its content: `dgOf` at `none` is the genesis
root. -/
theorem simTrace_genesis_root_ok :
    ((S.params (pubOf E) hn).toParams.genesisBlock
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload).RootOk
        (digestOf S rho) := by
  rfl

/-- A vote of an honest validator carried by a block that an honest node processes was emitted
by that validator's node at an earlier cut. -/
theorem simTrace_carried_vote_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i B, (simTrace S rho hn).BlockCallAt y i B →
      ∀ v ∈ blockVotes B, v.val ∈ honestKeys S rho →
        ∃ j < i, (simTrace S rho hn).EmitAt v.val j v := by
  sorry

/-! ## Blocks of cuts

The trace's state across a block of cuts: unchanged across other nodes' cuts, the handler's
state across a group, `deliverState` across a delivery's groups; and a block with the engine's
ids is a `GroupAt` / `DeliverSeq` of the trace. -/

section

variable {P : Params} {A : NodeAC P}

/-- The `k`-th post-state of a cut list is the fold of its first `k + 1` cuts. -/
theorem cutPosts_getElem (self : Fin P.n) (t : Time) (cs : List (Cut A)) (st : NodeState A)
    (k : Nat) (hk : k < (cutPosts self t cs st).length) :
    (cutPosts self t cs st)[k] = (cs.take (k + 1)).foldl (cutPost self t) st := by
  induction cs generalizing st k with
  | nil => simp [cutPosts_nil] at hk
  | cons c cs ih =>
    rw [List.getElem_of_eq (cutPosts_cons self t c cs st) hk]
    cases k with
    | zero => simp
    | succ k =>
      rw [cutPosts_cons, List.length_cons] at hk
      rw [List.getElem_cons_succ, ih _ _ (by omega), List.take_succ_cons, List.foldl_cons]

end

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (proposer : Nat → Fin sp.n)
  (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)

/-- The post-state of cut `k` of a group: the handler's `k`-th post-state. -/
theorem getElem_groupRecs_post (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) (k : Nat)
    (hk : k < (groupRecs proposer dg self st t id e).length) :
    (groupRecs proposer dg self st t id e)[k].post =
      (cutPosts self t (exec proposer dg self st t e).2 st)[k]'(by
        rw [length_cutPosts]; rwa [length_groupRecs] at hk) := by
  rw [List.getElem_of_eq (groupRecs_eq proposer dg self st t id e) hk, List.getElem_mapIdx,
    List.getElem_zip]

/-- A tick makes a cut (the AC's tick). -/
theorem exec_tick_ne_nil (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (exec proposer dg self st t (.tick x)).2 ≠ [] := by
  simp [Node.exec, onTick, runSteps, tickSteps, Node.tickStep]

/-- A restart makes a cut (`ac_restart`). -/
theorem exec_restart_ne_nil (st : NodeState (goldilocksNode sp ro)) (t : Time) :
    (exec proposer dg self st t .restart).2 ≠ [] := by
  simp [Node.exec, Node.restart]

end

/-- The trace's state is unchanged over a block of cuts of other nodes. -/
private theorem state_of_block_ne {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat} (len : Nat)
    (hne : ∀ k < len, ∀ r, (allCuts S rho hn)[j0 + k]? = some r → r.node ≠ y) :
    (simTrace S rho hn).state y (j0 + len) = (simTrace S rho hn).state y j0 := by
  induction len with
  | zero => rfl
  | succ k ih =>
    change (simTrace S rho hn).state y (j0 + k).succ = _
    rw [Trace.state.eq_2, ite_eq_right, ih (fun k' hk' => hne k' (by omega))]
    rintro ⟨hnode, hlab⟩
    rw [simTrace_node] at hnode
    cases hr : (allCuts S rho hn)[j0 + k]? with
    | none => rw [simTrace_label, hr] at hlab; exact hlab rfl
    | some r =>
      rw [hr] at hnode
      exact hne k (by omega) r hr hnode

/-- The trace's state across a group block at `j0`: the handler's state, by the cut law's
successors. -/
private theorem state_of_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) :
    (simTrace S rho hn).state y (j0 + (groupRecs proposer dg y st t id e).length) =
      (exec proposer dg y st t e).1 := by
  have key : ∀ k ≤ (exec proposer dg y st t e).2.length,
      (simTrace S rho hn).state y (j0 + k) =
        ((exec proposer dg y st t e).2.take k).foldl (cutPost y t) st := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      have hk' : k < (groupRecs proposer dg y st t id e).length := by
        rw [length_groupRecs]; omega
      have hr := hcut k hk'
      rw [List.getElem?_eq_getElem hk'] at hr
      obtain ⟨hnode, -, -, -, -⟩ := getElem_groupRecs proposer dg y st t id e k hk'
      change (simTrace S rho hn).state y (j0 + k).succ = _
      rw [Trace.state.eq_2, ite_eq_left, simTrace_post, hr, Option.elim_some,
        getElem_groupRecs_post, cutPosts_getElem]
      rw [simTrace_node, hr, Option.elim_some, hnode, simTrace_label, hr]
      simp
  rw [length_groupRecs, key _ le_rfl, List.take_length, foldl_cutPost_exec]

/-- The trace's state across a delivery block at `j0`: `deliverState`. -/
private theorem state_of_deliverRecs
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? = (deliverRecs proposer dg hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    (simTrace S rho hn).state y (j0 + (deliverRecs proposer dg hs y t i os st sub).length) =
      deliverState proposer dg hs y t os st := by
  induction os with
  | nil => intro j0 sub st _ h0; rw [deliverRecs_nil, List.length_nil, deliverState_nil]; exact h0
  | cons o os ih =>
    intro j0 sub st hcut h0
    cases he : canonEvent (S.params (pubOf E) hn) (S.ro _) hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hcut ⊢
      rw [deliverState_cons_none _ _ _ _ _ _ _ _ he]
      exact ih j0 (sub + 1) st hcut h0
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hcut ⊢
      rw [deliverState_cons_some _ _ _ _ _ _ _ _ _ he, List.length_append]
      have h1 : (simTrace S rho hn).state y
          (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) =
            (exec proposer dg y st t e).1 :=
        state_of_group S rho hn proposer dg (fun k hk => by
          rw [hcut k (by rw [List.length_append]; omega), List.getElem?_append_left hk]) h0
      rw [← Nat.add_assoc]
      refine ih (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (sub + 1) _
        (fun k hk => ?_) h1
      rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
        List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The event id of an existing cut is its record's. -/
private theorem event_of_getElem? {k : Nat} {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : (allCuts S rho hn)[k]? = some r) : (simTrace S rho hn).event k = r.event := by
  rw [simTrace_event, hr]; rfl

/-- A cut with an event id of engine event `i` lies in the range of event `i`. -/
private theorem range_of_event {i : Nat} (hi : i < rho.events.length) {k s : Nat}
    (h : (simTrace S rho hn).event k = Nat.pair i s) :
    cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) := by
  cases hr : (allCuts S rho hn)[k]? with
  | none =>
    rw [simTrace_event, hr, Option.elim_none, Nat.pair_eq_pair] at h
    omega
  | some r =>
    rw [event_of_getElem? S rho hn hr] at h
    obtain ⟨i', ev, he, h1, h2, h3⟩ := exists_event_of_getElem? S rho hn hr
    obtain ⟨-, -, s', hs'⟩ := mem_eventCuts S rho hn he (List.mem_of_getElem? h3)
    rw [hs', Nat.pair_eq_pair] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨h1, h2⟩

/-- A block of group cuts at `j0` whose event id is unique to the block is a group of the
trace; its length is the handler's cut count on the trace's state. -/
private theorem groupAt_of_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) (hne : (exec proposer dg y st t e).2 ≠ [])
    (huniq : ∀ k, (simTrace S rho hn).event k = id →
      j0 ≤ k ∧ k < j0 + (groupRecs proposer dg y st t id e).length) :
    (simTrace S rho hn).GroupAt proposer dg y j0 t e ∧
      (groupRecs proposer dg y st t id e).length =
        (exec proposer dg y ((simTrace S rho hn).state y j0) t e).2.length := by
  subst h0
  set st := (simTrace S rho hn).state y j0 with hst
  have hlen := length_groupRecs proposer dg y st t id e
  have hfact : ∀ k (hk : k < (exec proposer dg y st t e).2.length),
      (simTrace S rho hn).node (j0 + k) = y ∧ (simTrace S rho hn).time (j0 + k) = t ∧
        (simTrace S rho hn).event (j0 + k) = id ∧ (simTrace S rho hn).pos (j0 + k) = k ∧
        (simTrace S rho hn).label (j0 + k) = some (exec proposer dg y st t e).2[k] := by
    intro k hk
    have hk' : k < (groupRecs proposer dg y st t id e).length := by omega
    have hr := hcut k hk'
    rw [List.getElem?_eq_getElem hk'] at hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := getElem_groupRecs proposer dg y st t id e k hk'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [simTrace_node, hr, Option.elim_some, h1]
    · rw [simTrace_time, hr, Option.elim_some, h2]
    · rw [event_of_getElem? S rho hn hr, h3]
    · rw [simTrace_pos, hr, Option.elim_some, h4]
    · rw [simTrace_label, hr, Option.map_some, h5]
  have h0' : (simTrace S rho hn).event j0 = id := by
    have := (hfact 0 (List.length_pos_of_ne_nil hne)).2.2.1
    rwa [Nat.add_zero] at this
  refine ⟨⟨hne, ?_, ?_⟩, hlen⟩
  · intro k hk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hfact k hk
    exact ⟨h1, h2, h3.trans h0'.symm, h4, h5⟩
  · intro k hk
    rw [← hlen]
    exact huniq k (hk.trans h0')

/-- A delivery block at `j0` whose sub-event ids from `sub` on are unique to the block is a
`DeliverSeq` of the trace. -/
private theorem deliverSeq_of_recs
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? = (deliverRecs proposer dg hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    (∀ k s, (simTrace S rho hn).event k = Nat.pair i s → sub ≤ s →
      j0 ≤ k ∧ k < j0 + (deliverRecs proposer dg hs y t i os st sub).length) →
    DeliverSeq proposer (simTrace S rho hn) dg hs y t os j0
      (j0 + (deliverRecs proposer dg hs y t i os st sub).length) := by
  induction os with
  | nil =>
    intro j0 sub st _ _ _
    rw [deliverRecs_nil, List.length_nil, Nat.add_zero]
    exact .nil j0
  | cons o os ih =>
    intro j0 sub st hcut h0 huniq
    cases he : canonEvent (S.params (pubOf E) hn) (S.ro _) hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hcut huniq ⊢
      exact .drop he (ih j0 (sub + 1) st hcut h0 fun k s hk hs => huniq k s hk (by omega))
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hcut huniq ⊢
      rcases eq_or_ne (exec proposer dg y st t e).2 [] with hnil | hnil
      · have hg : groupRecs proposer dg y st t (Nat.pair i sub) e = [] :=
          List.length_eq_zero_iff.mp (by rw [length_groupRecs, hnil, List.length_nil])
        have hst : (exec proposer dg y st t e).1 = st := by
          have := foldl_cutPost_exec proposer dg y st t e
          rwa [hnil, List.foldl_nil, eq_comm] at this
        rw [hg, List.nil_append, hst] at hcut huniq ⊢
        exact .noCut e he (by rw [h0]; exact hnil)
          (ih j0 (sub + 1) st hcut h0 fun k s hk hs => huniq k s hk (by omega))
      · have hlen := length_groupRecs proposer dg y st t (Nat.pair i sub) e
        have hcutg : ∀ k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
            (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t (Nat.pair i sub) e)[k]? :=
          fun k hk => by
            rw [hcut k (by rw [List.length_append]; omega), List.getElem?_append_left hk]
        -- a cut with an id of the rest is past the group; one with the group's id is in it
        have hrest : ∀ k, (groupRecs proposer dg y st t (Nat.pair i sub) e).length ≤ k →
            k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length +
              (deliverRecs proposer dg hs y t i os (exec proposer dg y st t e).1 (sub + 1)).length →
            ∃ s, sub + 1 ≤ s ∧ (simTrace S rho hn).event (j0 + k) = Nat.pair i s := by
          intro k hk1 hk2
          have hr := hcut k (by rw [List.length_append]; omega)
          have hlt : k - (groupRecs proposer dg y st t (Nat.pair i sub) e).length <
              (deliverRecs proposer dg hs y t i os
                (exec proposer dg y st t e).1 (sub + 1)).length := by omega
          rw [List.getElem?_append_right hk1, List.getElem?_eq_getElem hlt] at hr
          obtain ⟨-, -, s, hs1, hs2⟩ := mem_deliverRecs proposer dg y hs t i (List.getElem_mem hlt)
          exact ⟨s, hs1, by rw [event_of_getElem? S rho hn hr, hs2]⟩
        have hgrp : ∀ k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
            (simTrace S rho hn).event (j0 + k) = Nat.pair i sub := by
          intro k hk
          have hr := hcutg k hk
          rw [List.getElem?_eq_getElem hk] at hr
          rw [event_of_getElem? S rho hn hr]
          exact (getElem_groupRecs proposer dg y st t (Nat.pair i sub) e k hk).2.2.1
        obtain ⟨hG, hGlen⟩ := groupAt_of_group S rho hn proposer dg hcutg h0 hnil fun k hk => by
          obtain ⟨h1, h2⟩ := huniq k sub hk le_rfl
          rw [List.length_append] at h2
          refine ⟨h1, ?_⟩
          by_contra h3
          obtain ⟨s, hs1, hs2⟩ := hrest (k - j0) (by omega) (by omega)
          rw [Nat.add_sub_cancel' h1, hk, Nat.pair_eq_pair] at hs2
          omega
        refine .event e he hG ?_
        rw [← hGlen, List.length_append, ← Nat.add_assoc]
        refine ih (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (sub + 1) _
          (fun k hk => ?_) (state_of_group S rho hn proposer dg hcutg h0) (fun k s hk hs => ?_)
        · rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
            List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        · obtain ⟨h1, h2⟩ := huniq k s hk (by omega)
          rw [List.length_append, ← Nat.add_assoc] at h2
          refine ⟨?_, h2⟩
          by_contra h3
          have := hgrp (k - j0) (by omega)
          rw [Nat.add_sub_cancel' h1, hk, Nat.pair_eq_pair] at this
          omega

/-! ## `Simulates`: the engine agrees with the trace -/

/-- Every labelled node cut lies in the range of some engine event. -/
theorem simTrace_covered :
    ∀ k, (simTrace S rho hn).label k ≠ none →
      ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) := by
  intro k hk
  rw [simTrace_label] at hk
  have hlt : k < (allCuts S rho hn).length := by
    by_contra h
    rw [List.getElem?_eq_none_iff.mpr (by omega)] at hk
    exact hk rfl
  obtain ⟨i, hi, h1, h2, -⟩ := allCuts_getElem? S rho hn k hlt
  exact ⟨i, hi, h1, h2⟩

/-- The node state inside the shape's state is the trace's state at the mapped cut (by induction
on the events, from `node_of_tick_public`, `node_of_tick_other`, `node_of_deliver`,
`node_of_restart` and `state_of_other`). -/
theorem simTrace_state (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
      (stateAt S rho hn v i).node =
        (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  intro v hv' i
  induction i with
  | zero =>
    intro _
    rw [cutMap_zero]
    exact (congrArg (·.node) (stateAt_zero S rho hn v)).trans
      (simTrace_init_eq S rho hn (rho.ownKey v)).symm
  | succ i ih =>
    intro hi
    have hi' : i < rho.events.length := by omega
    have ih := ih (by omega)
    have he : rho.events[i]? = some rho.events[i] := List.getElem?_eq_getElem hi'
    rw [cutMap_succ]
    by_cases hne : rho.events[i].node ≠ v
    · rw [state_of_other S rho hn v i _ he hne]
      refine ih.trans (state_of_block_ne S rho hn _ (fun k hk r hr => ?_)).symm
      rw [allCuts_getElem?_add S rho hn i k hi' hk] at hr
      obtain ⟨hnode, -, -⟩ := mem_eventCuts S rho hn he (List.mem_of_getElem? hr)
      rw [hnode]
      exact fun h => hne (rho.key.symm.injective h)
    rw [not_not] at hne
    have hcut : ∀ k < (eventCuts S rho hn i).length,
        (allCuts S rho hn)[cutMap S rho hn i + k]? = (eventCuts S rho hn i)[k]? :=
      fun k hk => allCuts_getElem?_add S rho hn i k hi' hk
    cases hev : rho.events[i] with
    | tick w t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
      · rw [eventCuts_tick_public S rho hn i w t he hp] at hcut ⊢
        rw [node_of_tick_public S rho hn hv w hv' i t he hp]
        exact (state_of_group S rho hn _ _ hcut ih.symm).symm
      · rw [eventCuts_tick_other S rho hn i w t he hp, List.length_nil, Nat.add_zero,
          node_of_tick_other S rho hn hv w hv' i t he hp]
        exact ih
    | deliver w o t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      rw [eventCuts_deliver S rho hn i w o t he] at hcut ⊢
      rw [node_of_deliver S rho hn hv w hv' i o t he]
      exact (state_of_deliverRecs S rho hn _ _ _ _ _ _ _ hcut ih.symm).symm
    | restart w t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      rw [eventCuts_restart S rho hn i w t he] at hcut ⊢
      rw [node_of_restart S rho hn hv w hv' i t he]
      exact (state_of_group S rho hn _ _ hcut ih.symm).symm

/-- An engine tick of an honest node at a public time is the node's tick with the engine's input,
one group. -/
theorem simTrace_tick_public_group (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      (S.params (pubOf E) hn).toParams.IsPublic t →
        (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
            (rho.ownKey v) (cutMap S rho hn i) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
          cutMap S rho hn (i + 1) = cutMap S rho hn i +
            (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
  intro v hv' i t he hp
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_tick_public S rho hn i v t he hp]
  have h0 := (simTrace_state S rho hn hv v hv' i hi.le).symm
  have hne := exec_tick_ne_nil (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
    (encodeTxs (Model.mempool rho.inbox v t))
  have hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length,
      (allCuts S rho hn)[cutMap S rho hn i + k]? =
        (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))))[k]? := fun k hk => by
    rw [← eventCuts_tick_public S rho hn i v t he hp] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  have huniq : ∀ k, (simTrace S rho hn).event k = Nat.pair i 0 → cutMap S rho hn i ≤ k ∧
      k < cutMap S rho hn i + (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length := fun k hk => by
    have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_tick_public S rho hn i v t he hp] at this
  obtain ⟨hG, hlen⟩ :=
    groupAt_of_group S rho hn (runProposer S rho hn) (digestOf S rho) hcut h0 hne huniq
  exact ⟨hG, congrArg (cutMap S rho hn i + ·) hlen⟩

/-- An honest node awake at a public time (from `0` on) ticks there. -/
theorem simTrace_tick_of_awake (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, 0 ≤ t → (S.params (pubOf E) hn).toParams.IsPublic t →
      (simTrace S rho hn).awake y t →
      ∃ j, (simTrace S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t := by
  intro y hy t ht0 hp hw
  obtain ⟨hwE, -, k, -, htk⟩ := (awake_iff' S rho hn y t).mp hw
  have hth : t ≤ rho.horizon := htk.trans (time_bounds S rho hn hv k).2
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp (hv.tick_total _ hy t ht0 hth hwE)
  obtain ⟨hg, -⟩ := simTrace_tick_public_group S rho hn hv _ hy i t he hp
  rw [ownKey_key] at hg
  exact ⟨_, _, hg⟩

/-- An engine tick at a non-public time has no cut. -/
theorem simTrace_tick_other (_hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      ¬ (S.params (pubOf E) hn).toParams.IsPublic t →
        cutMap S rho hn (i + 1) = cutMap S rho hn i := by
  intro v _ i t he hp
  rw [cutMap_succ, eventCuts_tick_other S rho hn i v t he hp, List.length_nil, Nat.add_zero]

/-- An engine delivery to an honest node is the groups of the canonical objects it delivers. -/
theorem simTrace_deliver (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i o t, rho.events[i]? = some (.deliver v o t) →
      DeliverSeq (runProposer S rho hn) (simTrace S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
  intro v hv' i o t he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_deliver S rho hn i v o t he]
  refine deliverSeq_of_recs S rho hn (runProposer S rho hn) (digestOf S rho)
    _ _ _ 0 _ (fun k hk => ?_)
    (simTrace_state S rho hn hv v hv' i hi.le).symm (fun k s hk _ => ?_)
  · rw [← eventCuts_deliver S rho hn i v o t he] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  · have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_deliver S rho hn i v o t he] at this

/-- An engine restart of an honest node is the node's restart group. -/
theorem simTrace_restart (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.restart v t) →
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
        cutMap S rho hn (i + 1) = cutMap S rho hn i +
          (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  intro v hv' i t he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_restart S rho hn i v t he]
  have h0 := (simTrace_state S rho hn hv v hv' i hi.le).symm
  have hne := exec_restart_ne_nil (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
  have hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) .restart).length,
      (allCuts S rho hn)[cutMap S rho hn i + k]? =
        (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart)[k]? := fun k hk => by
    rw [← eventCuts_restart S rho hn i v t he] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  have huniq : ∀ k, (simTrace S rho hn).event k = Nat.pair i 0 → cutMap S rho hn i ≤ k ∧
      k < cutMap S rho hn i + (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart).length := fun k hk => by
    have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_restart S rho hn i v t he] at this
  obtain ⟨hG, hlen⟩ :=
    groupAt_of_group S rho hn (runProposer S rho hn) (digestOf S rho) hcut h0 hne huniq
  exact ⟨hG, congrArg (cutMap S rho hn i + ·) hlen⟩

/-- An honest node awake in the trace is awake in the environment, within `[0, horizon]`: the
trace's horizon is within the engine's, as every cut's time is an event's. -/
theorem simTrace_awake_of (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon := by
  intro y _ t hw
  obtain ⟨hwE, ht0, k, -, htk⟩ := (awake_iff' S rho hn y t).mp hw
  exact ⟨hwE, ht0, htk.trans (time_bounds S rho hn hv k).2⟩

/-- An honest node's signings in the simulating trace are pairwise not slashable (`non_framing`
over the trace, a Goldilocks run). -/
private theorem simTrace_nonFraming
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn))
    {v : V} (hv' : v ∈ rho.honest) :
    ∀ k k' a b, (simTrace S rho hn).SignAt (rho.ownKey v) k a →
      (simTrace S rho hn).SignAt (rho.ownKey v) k' b → ¬ FG.slashable a b :=
  Regimes.non_framing _ _ _ _ _ _ hrun (rho.ownKey v)
    (by change rho.key (rho.ownKey v) ∈ rho.honest; rw [ownKey_key']; exact hv')

/-- The engine's Goldilocks state at a delivery: at the delivery's time, with the own key. -/
private theorem deliver_state (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v i).now = t ∧ (stateAt S rho hn v i).self = rho.ownKey v :=
  ⟨(now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he),
    stateAt_self S rho hn v i⟩

/-- A cut of a delivery to an honest node: its delivered object is queued by the delivery's
`process` (`process_relay`) and relayed by the delivery's gossip at its own time
(`deliver_relays`), as a carried object of a released relay wrapper. -/
theorem relays_of_cut (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {k : Nat}
    (hnode : (simTrace S rho hn).node k = y) (hl : (simTrace S rho hn).label k ≠ none)
    (hdel : ∀ r : CutRec (S.params (pubOf E) hn) (S.ro _), (allCuts S rho hn)[k]? = some r →
      (r.pos = 0 ∧ ∃ ℓ, r.label = .fg ℓ) ∨ ∃ ℓ m, r.label = .ac ℓ ∧ ℓ.call = .message m) :
    ∃ r : CutRec (S.params (pubOf E) hn) (S.ro _),
      (simTrace S rho hn).label k = some r.label ∧ (simTrace S rho hn).post k = r.post ∧
      ∀ x, ((∃ B, r.label = .fg (.block B true) ∧ x = blockObj (S.params (pubOf E) hn) B) ∨
          (∃ ℓ m, r.label = .ac ℓ ∧ ℓ.call = .message m ∧ m ∈ r.post.ac.pool m.slot ∧
            x = voteObj m) ∨
          (∃ a, r.label = .fg (.attestation a) ∧ x = attObj a)) →
        ∃ cs, x ∈ cs ∧ rho.releases (rho.key y) (.mk .none (.data .relay) cs)
          ((simTrace S rho hn).time k) := by
  obtain ⟨r, i, ev, hr, he, -, -, hidx, hn', ht, -, hlab⟩ := simTrace_cut S rho hn hl
  have hmem := List.mem_of_getElem? hidx
  obtain ⟨v, o, t, rfl⟩ := eq_deliver_of_cut S rho hn he hmem (hdel r hr)
  simp only [Model.Event.node, Model.Event.time] at hn' ht
  have hkey : v = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  subst hkey
  refine ⟨r, hlab, by rw [simTrace_post, hr]; rfl, fun x hx => ?_⟩
  rw [ht]
  rw [eventCuts_deliver S rho hn i _ o t he] at hmem
  obtain ⟨hnow, hself⟩ := deliver_state S rho hn hv he
  obtain ⟨h1, h2, h3⟩ := (process_relay (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash o) t i
    (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn _ i) 0 hnow).2.2.2 r
    (by rw [hself]; exact hmem)
  have hq : x ∈
      (process (stateAt S rho hn (rho.key y) i) o (Model.digests rho.hash o)).relayBuf := by
    rcases hx with ⟨B, hB, rfl⟩ | ⟨ℓ, m, hℓ, hc, hp, rfl⟩ | ⟨a, ha, rfl⟩
    · exact h1 B hB
    · exact h2 ℓ m hℓ hc hp
    · exact h3 a ha
  obtain ⟨cs, hxcs, hrel⟩ := deliver_relays S rho hn he hq
  exact ⟨cs, hxcs, i, Or.inr ⟨o, he⟩, hrel⟩

/-- The engine releases an honest node's own block at the tick that proposes it (the proposal
duty's candidate is `blockObj` of the block, `releasable` by `proposal_releasable`, passed by
`protects_blockObj`). -/
theorem simTrace_block_released (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn)) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).OwnBlockAt y k B →
      rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B)
        ((simTrace S rho hn).time k) := by
  rintro y _ k B ⟨⟨acc, hnode, hlab⟩, hpos⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, hp', hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hpos' : r.pos ≠ 0 := hp' ▸ hpos
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, (tick_releases S rho hn hv
      (hv.honest_only _ (List.mem_of_getElem? he)) he hp
      (simTrace_nonFraming S rho hn hrun (hv.honest_only _ (List.mem_of_getElem? he)))
      r hmem).1 B acc hrl hpos'⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', hce, kk, hk, hlabk, hposk⟩ :=
      mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    exact hpos' (hposk.trans
      (pos_of_block_cut _ _ _ _ _ (canonEvent_ne_tick hce) hk (hlabk.symm.trans hrl)))
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, hposk, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    exact hpos' (hposk.trans (pos_of_block_cut _ _ _ _ _ (e := .restart) (fun x h => by cases h)
      hk' (hlabk.symm.trans hrl)))

/-- The engine releases an honest node's vote at its emission time: the tick's trailing polls
or the delivery's poll. A restart at its own time emits no vote. -/
theorem simTrace_vote_released (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn)) :
    ∀ y ∈ honestKeys S rho, ∀ k m, (simTrace S rho hn).EmitAt y k m →
      ReleasedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  rintro y _ k m ⟨ℓ, ⟨hnode, hlab⟩, em, hem, rfl⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, (tick_releases S rho hn hv
      (hv.honest_only _ (List.mem_of_getElem? he)) he hp
      (simTrace_nonFraming S rho hn hrun (hv.honest_only _ (List.mem_of_getElem? he)))
      r hmem).2.1 ℓ hrl em hem⟩
  | deliver v o t =>
    -- open: the vote goes out at the delivery's own poll step (`deliverOrder := [.poll]`);
    -- restated with the release fields (#107 PR 2)
    sorry
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    have hcut := List.getElem_mem hk'
    rw [← hlabk, hrl] at hcut
    have hval := emits_val_of_mem_exec _ _ _ _ _ _ hcut em hem
    have hb : Body.vote (encodeVote em.msg) ∈ (stateAt S rho hn v (i + 1)).outbox := by
      rw [stateAt_succ_restart S rho hn he]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨_, hcut, by simpa using ⟨em, hem, rfl⟩⟩)
    have hobj : @voteObj (pubOf E).n em.msg = Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (Body.vote (encodeVote em.msg))) [] := by
      unfold voteObj
      rw [show em.msg.val = rho.ownKey v from hval]
    rw [hobj]
    exact releasedFrom_of_pending S rho hn hv he hb

/-- The engine releases an honest node's attestation at its signing time (queued by `fgUpdate`,
released by the tick's last poll steps; `tick_releases`, `Release`). -/
theorem simTrace_att_released (hv : rho.ExecutionValid)
    (hrun : GoldilocksRun (runProposer S rho hn)
      (digestOf S rho) (honestKeys S rho) (simTrace S rho hn)) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).SignAt y k a →
      ReleasedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  rintro y _ k a ⟨src, hnode, hlab⟩
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, -, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.attest src (some a)) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    exact ⟨i, Or.inl he, (tick_releases S rho hn hv
      (hv.honest_only _ (List.mem_of_getElem? he)) he hp
      (simTrace_nonFraming S rho hn hrun (hv.honest_only _ (List.mem_of_getElem? he)))
      r hmem).2.2 src a hrl⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', hce, kk, hk, hlabk, -⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := List.getElem_mem hk
    rw [← hlabk, hrl] at hcut
    obtain ⟨x, rfl⟩ := Compose.signed_only_in_ticks _ _ _ st' t e src a hcut
    exact canonEvent_ne_tick hce x rfl
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, -, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    have hcut := List.getElem_mem hk'
    rw [← hlabk, hrl] at hcut
    obtain ⟨x, hx⟩ := Compose.signed_only_in_ticks _ _ _ _ t .restart src a hcut
    cases hx

/-- An honest node relays a block it accepts from the wire, at the delivery's own time
(`relays_of_cut`). -/
theorem simTrace_block_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).AcceptAt y k B →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B)
          ((simTrace S rho hn).time k) := by
  rintro y _ k B ⟨hnode, hlab⟩ hpos
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, hrl, -, hrel⟩ := relays_of_cut S rho hn hv hnode hl fun r hr => Or.inl
    ⟨by rw [simTrace_pos, hr] at hpos; exact hpos, _,
      Option.some.inj ((by rw [simTrace_label, hr]; rfl : _ = some r.label).symm.trans hlab)⟩
  obtain ⟨cs, hx, hcs⟩ := hrel _ (Or.inl ⟨B, Option.some.inj (hrl.symm.trans hlab), rfl⟩)
  exact ⟨cs, hx, hcs⟩

/-- An honest node relays a vote it admits from the wire. -/
theorem simTrace_vote_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k m, (simTrace S rho hn).MsgCallAt y k m →
      m ∈ ((simTrace S rho hn).post k).ac.pool m.slot →
        RelayedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  rintro y _ k m ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ hpool
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, hrl, hpost, hrel⟩ := relays_of_cut S rho hn hv hnode hl fun r hr => Or.inr
    ⟨ℓ, m, Option.some.inj ((by rw [simTrace_label, hr]; rfl : _ = some r.label).symm.trans hlab),
      hcall⟩
  obtain ⟨cs, hx, hcs⟩ := hrel _ (Or.inr (Or.inl ⟨ℓ, m, Option.some.inj (hrl.symm.trans hlab),
    hcall, hpost ▸ hpool, rfl⟩))
  exact ⟨cs, hx, hcs⟩

/-- An honest node relays an attestation it receives from the wire. -/
theorem simTrace_att_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).AttCallAt y k a →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  rintro y _ k a ⟨hnode, hlab⟩ hpos
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, hrl, -, hrel⟩ := relays_of_cut S rho hn hv hnode hl fun r hr => Or.inl
    ⟨by rw [simTrace_pos, hr] at hpos; exact hpos, _,
      Option.some.inj ((by rw [simTrace_label, hr]; rfl : _ = some r.label).symm.trans hlab)⟩
  obtain ⟨cs, hx, hcs⟩ := hrel _ (Or.inr (Or.inr ⟨a, Option.some.inj (hrl.symm.trans hlab), rfl⟩))
  exact ⟨cs, hx, hcs⟩

/-! ## `LocalRun`: groups, the cut law and the wire checks

A labelled cut of an honest node lies in a block of records of one handler call (`groupRecs`)
that starts at the trace's state (`recBlock_of_cut`), and in a group of the trace
(`group_of_cut`): an engine tick at a public time and a restart are one group, a delivery is a
`DeliverSeq` of groups of canonical objects. The cut law at such a cut is the handler's cut chain
(C0.5); a delivered event passes the wire checks because it is `canonEvent` of a delivered object
(the checks `decodeBlock` and `decodeAttObj` make, and the engine's digests), and the first cut of
a handler names its event (the engine-free facts: `deliverSeq_cover`, `decodeBlock_wire`,
`exec_head_fg`, `cutStep_of_cutChain`, `Relay`). -/

omit [DecidableEq V] in
/-- A canonical event of an object an engine delivery delivers passes the wire checks: a block
decodes with the engine's digests of the delivery, which map its header to the engine's hash of
it, the root `digestOf` names. -/
private theorem wireOK_of_delivered (o : (Model.protoOf (compiled (family S)) E).Object)
    {o' : Wire (S.params (pubOf E) hn).n} (ho : o' ∈ delivered (S.params (pubOf E) hn) o)
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (he : canonEvent (S.params (pubOf E) hn) (S.ro _) (Model.digests rho.hash o) o' = some e) :
    WireOK (digestOf S rho) e := by
  rcases canonEvent_eq_some he with ⟨B, rfl, rfl⟩ | ⟨m, rfl, -⟩ | ⟨a, rfl, -⟩
  · obtain ⟨hroot, hpar, hwf, hval⟩ := decodeBlock_wire (decodeBlock_of_canonEvent he)
    have hh : rootOf (Model.digests rho.hash o) (headerOf _ B) =
        some (rho.hash (headerOf _ B)) := by
      apply rootOf_digests_of_mem
      exact List.mem_filterMap.2 ⟨blockObj _ B, mem_delivered ho, rfl⟩
    have hrt := hroot.symm.trans hh
    rw [Option.some.injEq] at hrt
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hpar
    refine ⟨?_, hwf, hval⟩
    change B.root = dgOf rho.hash S.genesisRoot B.parent B.slot B.input B.fgPayload B.acPayload
    rw [hrt]
    simp only [headerOf, hr]
    rfl
  · trivial
  · exact wellFormed_of_canonEvent he

/-- Across a block of group records starting at the trace's state, the trace's state is the
fold of the handler's first cuts. -/
private theorem state_in_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) :
    ∀ k ≤ (exec proposer dg y st t e).2.length,
      (simTrace S rho hn).state y (j0 + k) =
        ((exec proposer dg y st t e).2.take k).foldl (cutPost y t) st := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have hk' : k < (groupRecs proposer dg y st t id e).length := by
      rw [length_groupRecs]; omega
    have hr := hcut k hk'
    rw [List.getElem?_eq_getElem hk'] at hr
    obtain ⟨hnode, -, -, -, -⟩ := getElem_groupRecs proposer dg y st t id e k hk'
    change (simTrace S rho hn).state y (j0 + k).succ = _
    rw [Trace.state.eq_2, ite_eq_left, simTrace_post, hr, Option.elim_some,
      getElem_groupRecs_post, cutPosts_getElem]
    rw [simTrace_node, hr, Option.elim_some, hnode, simTrace_label, hr]
    simp

/-- A cut of a delivery's records lies in the records of one handler call, starting at the
trace's state. -/
private theorem recBlock_of_deliverRecs
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? = (deliverRecs proposer dg hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    ∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      ∃ j1 st' id e, (∀ m < (groupRecs proposer dg y st' t id e).length,
        (allCuts S rho hn)[j1 + m]? = (groupRecs proposer dg y st' t id e)[m]?) ∧
        (simTrace S rho hn).state y j1 = st' ∧ j1 ≤ j0 + k ∧
        j0 + k < j1 + (groupRecs proposer dg y st' t id e).length := by
  induction os with
  | nil => intro j0 sub st _ _ k hk; simp [deliverRecs_nil] at hk
  | cons o os ih =>
    intro j0 sub st hcut h0 k hk
    cases he : canonEvent (S.params (pubOf E) hn) (S.ro _) hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hcut hk
      exact ih j0 (sub + 1) st hcut h0 k hk
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hcut hk
      rw [List.length_append] at hk
      have hcutg : ∀ m < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
          (allCuts S rho hn)[j0 + m]? = (groupRecs proposer dg y st t (Nat.pair i sub) e)[m]? :=
        fun m hm => by
          rw [hcut m (by rw [List.length_append]; omega), List.getElem?_append_left hm]
      by_cases hkg : k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length
      · exact ⟨j0, st, _, e, hcutg, h0, by omega, by omega⟩
      · obtain ⟨j1, st', id, e', h2, h3, h4, h5⟩ :=
          ih (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (sub + 1) _
            (fun m hm => by
              rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
                List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left])
            (state_of_group S rho hn proposer dg hcutg h0)
            (k - (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (by omega)
        exact ⟨j1, st', id, e', h2, h3, by omega, by omega⟩

omit [DecidableEq V] in
/-- The engine event of a labelled cut of an honest key is an event of an honest node. -/
private theorem honest_of_cut {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (h : rho.ownKey ev.node = y) : ev.node ∈ rho.honest := by
  rw [key_of_ownKey S rho h]; exact hy

/-- A labelled cut of an honest node lies in the records of one handler call, starting at the
trace's state. -/
private theorem recBlock_of_cut (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    (hy : y ∈ honestKeys S rho) {k : Nat} (hnode : (simTrace S rho hn).node k = y)
    (hl : (simTrace S rho hn).label k ≠ none) :
    ∃ j1 st t id e, (∀ m < (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length,
        (allCuts S rho hn)[j1 + m]? =
          (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e)[m]?) ∧
      (simTrace S rho hn).state y j1 = st ∧ j1 ≤ k ∧
      k < j1 + (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length := by
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ := simTrace_cut S rho hn hl
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hv' := honest_of_cut S rho hy (hn'.symm.trans hnode)
  have hcut : ∀ m < (eventCuts S rho hn i).length,
      (allCuts S rho hn)[cutMap S rho hn i + m]? = (eventCuts S rho hn i)[m]? :=
    fun m hm => allCuts_getElem?_add S rho hn i m hi hm
  have hlen := cutMap_succ S rho hn i
  have h0 := (simTrace_state S rho hn hv ev.node hv' i hi.le).symm
  have hy' := hn'.symm.trans hnode
  cases ev with
  | tick v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · rw [eventCuts_tick_public S rho hn i v t he hp] at hcut hlen
      exact ⟨_, _, t, _, _, hcut, h0, h1, by omega⟩
    · rw [eventCuts_tick_other S rho hn i v t he hp, List.length_nil] at hlen
      omega
  | deliver v o t =>
    change rho.ownKey v = y at hy'
    subst hy'
    rw [eventCuts_deliver S rho hn i v o t he] at hcut hlen
    obtain ⟨j1, st', id, e, h3, h4, h5, h6⟩ := recBlock_of_deliverRecs S rho hn _ _ _ _ _ 0 _
      hcut h0 (k - cutMap S rho hn i) (by omega)
    exact ⟨j1, st', t, id, e, h3, h4, by omega, by omega⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    rw [eventCuts_restart S rho hn i v t he] at hcut hlen
    exact ⟨_, _, t, _, _, hcut, h0, h1, by omega⟩

/-- A labelled cut of an honest node lies in a group of the trace whose event passes the wire
checks. -/
private theorem group_of_cut (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    (hy : y ∈ honestKeys S rho) {k : Nat} (hnode : (simTrace S rho hn).node k = y)
    (hl : (simTrace S rho hn).label k ≠ none) :
    ∃ j0 t e,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j0 t e ∧ j0 ≤ k ∧
      k < j0 + (Node.exec (runProposer S rho hn) (digestOf S rho)
        y ((simTrace S rho hn).state y j0) t e).2.length ∧
      WireOK (digestOf S rho) e := by
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ := simTrace_cut S rho hn hl
  have hv' := honest_of_cut S rho hy (hn'.symm.trans hnode)
  have hy' := hn'.symm.trans hnode
  cases ev with
  | tick v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨hg, hlen⟩ := simTrace_tick_public_group S rho hn hv v hv' i t he hp
      exact ⟨_, t, _, hg, h1, by omega, trivial⟩
    · have := simTrace_tick_other S rho hn hv v hv' i t he hp
      omega
  | deliver v o t =>
    change rho.ownKey v = y at hy'
    subst hy'
    obtain ⟨-, hcov⟩ := deliverSeq_cover (simTrace_deliver S rho hn hv v hv' i o t he)
    obtain ⟨j0, e, o', ho, hce, hg, h3, h4⟩ := hcov k h1 h2
    exact ⟨j0, t, e, hg, h3, h4, wireOK_of_delivered S rho hn o ho hce⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    obtain ⟨hg, hlen⟩ := simTrace_restart S rho hn hv v hv' i t he
    exact ⟨_, t, _, hg, h1, by omega, trivial⟩

/-- Every labelled cut of an honest node lies in the group of a top-level event. -/
theorem simTrace_grouped (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      ∃ j e, (simTrace S rho hn).InGroup (runProposer S rho hn)
        (digestOf S rho) y j i ((simTrace S rho hn).time i) e := by
  rintro y hy i c ⟨hnode, hlab⟩
  obtain ⟨j0, t, e, hg, h1, h2, -⟩ := group_of_cut S rho hn hv hy hnode (by rw [hlab]; simp)
  have ht : (simTrace S rho hn).time i = t := by
    have := (hg.2.1 (i - j0) (by omega)).2.1
    rwa [Nat.add_sub_cancel' h1] at this
  rw [ht]
  exact ⟨j0, e, hg, h1, h2⟩

/-- Every labelled cut of an honest node obeys the cut law: the handler's cut chain (C0.5). -/
theorem simTrace_cutLaw (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      CutStep y ((simTrace S rho hn).time i) ((simTrace S rho hn).state y i) c
        ((simTrace S rho hn).post i) := by
  rintro y hy i c ⟨hnode, hlab⟩
  obtain ⟨j1, st, t, id, e, hcut, h0, h1, h2⟩ :=
    recBlock_of_cut S rho hn hv hy hnode (by rw [hlab]; simp)
  obtain ⟨m, rfl⟩ : ∃ m, i = j1 + m := ⟨i - j1, by omega⟩
  have hm : m < (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length := by omega
  have hm' : m < (exec (runProposer S rho hn) (digestOf S rho) y st t e).2.length := by
    have := length_groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e
    omega
  have hr := hcut m hm
  rw [List.getElem?_eq_getElem hm] at hr
  obtain ⟨-, htime, -, -, hlabel⟩ := getElem_groupRecs _ _ y st t id e m hm
  rw [simTrace_label, hr, Option.map_some, hlabel, Option.some.injEq] at hlab
  subst hlab
  rw [simTrace_time, hr, Option.elim_some, htime, simTrace_post, hr, Option.elim_some,
    getElem_groupRecs_post (runProposer S rho hn) (digestOf S rho) y st t id e m hm]
  have hch :
      CutChain y t st (exec (runProposer S rho hn) (digestOf S rho) y st t e).2
        (exec (runProposer S rho hn) (digestOf S rho) y st t e).1 :=
    Compose.exec_is_cut_chain (P := (S.params (pubOf E) hn).toParams)
      (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (runProposer S rho hn) (digestOf S rho) y st t e
  have key := cutStep_of_cutChain hch m hm'
  have e1 := cutPosts_getElem y t (exec (runProposer S rho hn) (digestOf S rho) y st t e).2 st m
    (by have := length_cutPosts y t (exec (runProposer S rho hn) (digestOf S rho) y st t e).2 st
        omega)
  rw [state_in_group S rho hn _ _ hcut h0 m hm'.le, e1]
  exact key

/-- A group of an honest node passes the wire checks: its first cut is a cut of an engine event's
group, which starts there, and names the same event (up to a tick's input). -/
theorem simTrace_wire (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t e,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e →
      WireOK (digestOf S rho) e := by
  intro y hy j t e hg
  obtain ⟨hne, hcuts, huniq⟩ := hg
  obtain ⟨hn0, -, -, -, hl0⟩ := hcuts 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hn0 hl0
  obtain ⟨j0, t0, e0, ⟨hne0, hc0, -⟩, h1, h2, hw0⟩ :=
    group_of_cut S rho hn hv hy hn0 (by rw [hl0]; simp)
  have hj : j0 = j := by
    have hev := (hc0 (j - j0) (by omega)).2.2.1
    rw [Nat.add_sub_cancel' h1] at hev
    have := (huniq j0 hev.symm).1
    omega
  subst hj
  have hl1 := (hc0 0 (List.length_pos_of_ne_nil hne0)).2.2.2.2
  rw [Nat.add_zero, hl0, Option.some.injEq] at hl1
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨c0, cs0, hcs0⟩ := List.exists_cons_of_ne_nil hne0
  have hc : c = c0 := by
    rw [List.getElem_of_eq hcs, List.getElem_of_eq hcs0] at hl1
    exact hl1
  subst hc
  cases e with
  | tick _ => trivial
  | restart => trivial
  | message _ => trivial
  | block B =>
    obtain ⟨acc, rfl⟩ := exec_block_head _ _ _ _ _ B hcs
    rcases exec_head_fg _ _ _ _ _ e0 hcs0 with ⟨B', acc', rfl, h⟩ | ⟨a, -, h⟩
    · cases h; exact hw0
    · cases h
  | attestation a =>
    have : c = .fg (.attestation a) := by
      have := hcs.symm
      simp only [Node.exec, onAttestation, List.cons.injEq] at this
      exact this.1
    subst this
    rcases exec_head_fg _ _ _ _ _ e0 hcs0 with ⟨B', acc', -, h⟩ | ⟨a', rfl, h⟩
    · cases h
    · cases h; exact hw0

/-! ## The trace is a Goldilocks run -/

/-- **The simulating trace is a Goldilocks run** at the engine's digest, for the honest keys. -/
theorem simTrace_goldilocksRun (hv : rho.ExecutionValid) :
    GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeys S rho) (simTrace S rho hn) where
  init := simTrace_init S rho hn
  grouped := simTrace_grouped S rho hn hv
  cutLaw := simTrace_cutLaw S rho hn hv
  wire := simTrace_wire S rho hn hv
  proposerCredential := simTrace_proposerCredential S rho hn hv
  time_nonneg := simTrace_time_nonneg S rho hn hv
  time_mono := simTrace_time_mono S rho hn hv
  finite := simTrace_finite S rho hn hv
  phase_order := simTrace_phase_order S rho hn hv
  tick_public := simTrace_tick_public S rho hn hv
  tick_unique := simTrace_tick_unique S rho hn hv
  tick_of_awake := simTrace_tick_of_awake S rho hn hv
  awake_in_horizon := simTrace_awake_in_horizon S rho hn
  awake_of_call := simTrace_awake_of_call S rho hn hv
  restart_of_sleep := simTrace_restart_of_sleep S rho hn hv
  restart_at_wake := simTrace_restart_at_wake S rho hn hv
  sleep_of_restart := simTrace_sleep_of_restart S rho hn hv
  block_unforgeable := simTrace_block_unforgeable S rho hn hv
  att_unforgeable := simTrace_att_unforgeable S rho hn hv
  msg_unforgeable := simTrace_msg_unforgeable S rho hn hv
  genesis_root_ok := simTrace_genesis_root_ok S rho hn
  carried_vote_unforgeable := simTrace_carried_vote_unforgeable S rho hn hv

end Consensus.Goldilocks.Refinement

end
