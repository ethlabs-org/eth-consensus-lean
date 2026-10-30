module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Cuts

public section

/-! # Goldilocks Refinement: the simulating trace is a run, and the engine agrees with it

The steps of `EngineSimulatesNode` over the trace `simTrace` and the cut map `cutMap` built from
a valid engine run (`Trace`): one theorem per field of `GoldilocksRun` (the trace is a run of the
Goldilocks protocol at the engine's digest, for the honest keys) and one per field of
`Simulates` (the engine's events are the trace's groups, the engine's node states are the trace's
states, the engine releases and relays what the trace signs, emits and admits). The engine-side
facts they rest on are the steps of `Steps`; the shape's pure facts those of `Shape`; where each
cut of the trace comes from, `Cuts`.

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

/-- Every labelled cut of an honest node lies in the group of a top-level event. -/
theorem simTrace_grouped (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      ∃ j e, (simTrace S rho hn).InGroup (digestOf S rho) y j i ((simTrace S rho hn).time i) e := by
  sorry

/-- Every labelled cut of an honest node obeys the cut law. -/
theorem simTrace_cutLaw (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      CutStep y ((simTrace S rho hn).time i) ((simTrace S rho hn).state y i) c
        ((simTrace S rho hn).post i) := by
  sorry

/-- A delivery to an honest node passes the wire checks. -/
theorem simTrace_wire (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t e, (simTrace S rho hn).GroupAt (digestOf S rho) y j t e →
      WireOK (digestOf S rho) e := by
  sorry

/-! ### The engine's schedule and the trace's cuts -/

omit [DecidableEq V] in
private theorem ownKey_key (y : Fin (Fintype.card V)) : rho.ownKey (rho.key y) = y :=
  rho.key.symm_apply_apply y

omit [DecidableEq V] in
private theorem key_of_ownKey {v : V} {y : Fin (Fintype.card V)} (h : rho.ownKey v = y) :
    v = rho.key y := by
  rw [← h]; exact (rho.key.apply_symm_apply v).symm

private theorem keyLe_of_lt (hv : rho.ExecutionValid) {i i' : Nat}
    {ev ev' : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) (he' : rho.events[i']? = some ev') (h : i < i') :
    ev.keyLe ev' := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp he'
  exact List.pairwise_iff_getElem.mp hv.sorted i i' hi hi' h

private theorem index_inj (hv : rho.ExecutionValid) {i i' : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) (he' : rho.events[i']? = some ev) : i = i' := by
  obtain ⟨hi, h1⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hi', h2⟩ := List.getElem?_eq_some_iff.mp he'
  exact (hv.nodup.getElem_inj_iff).mp (h1.trans h2.symm)

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
    (hg : (simTrace S rho hn).GroupAt (digestOf S rho) y j t e) :
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
      (simTrace S rho hn).GroupAt (digestOf S rho) y j t e →
      (simTrace S rho hn).GroupAt (digestOf S rho) y' j' t e' → j < j' →
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
    ∀ y ∈ honestKeys S rho, ∀ j t, (simTrace S rho hn).TickAt (digestOf S rho) y j t →
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
    ∀ y ∈ honestKeys S rho, ∀ j j' t, (simTrace S rho hn).TickAt (digestOf S rho) y j t →
      (simTrace S rho hn).TickAt (digestOf S rho) y j' t → j = j' := by
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
      have := index_inj S rho hv he he'
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
    · rcases keyLe_of_lt S rho hv he hir h with h' | ⟨h', h''⟩
      · have : ev.time < w := h'
        linarith
      · cases ev with
        | restart v s =>
          simp only [Model.Event.node, Model.Event.time] at hkey h'
          subst hkey h'
          exact absurd (index_inj S rho hv he hir) (by omega)
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
      · rcases keyLe_of_lt S rho hv he₁ he hlt with h' | ⟨-, h''⟩
        · have : ev₁.time < t := h'
          linarith
        · cases ev₁ with
          | restart v' s =>
            simp only [Model.Event.node, Model.Event.time] at hkey₁ heq
            subst hkey₁ heq
            exact absurd (index_inj S rho hv he₁ he) (by omega)
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
  sorry

/-- A vote of an honest validator carried by a block that an honest node processes was emitted
by that validator's node at an earlier cut. -/
theorem simTrace_carried_vote_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i B, (simTrace S rho hn).BlockCallAt y i B →
      ∀ v ∈ blockVotes B, v.val ∈ honestKeys S rho →
        ∃ j < i, (simTrace S rho hn).EmitAt v.val j v := by
  sorry

/-! ## `Simulates`: the engine agrees with the trace -/

/-- Every labelled node cut lies in the range of some engine event. -/
theorem simTrace_covered :
    ∀ k, (simTrace S rho hn).label k ≠ none →
      ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) := by
  sorry

/-- The node state inside the shape's state is the trace's state at the mapped cut (by induction
on the events, from `node_of_tick_public`, `node_of_tick_other`, `node_of_deliver`,
`node_of_restart` and `state_of_other`). -/
theorem simTrace_state (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
      (stateAt S rho hn v i).node =
        (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  sorry

/-- An engine tick of an honest node at a public time is the node's tick with the engine's input,
one group. -/
theorem simTrace_tick_public_group (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      (S.params (pubOf E) hn).toParams.IsPublic t →
        (simTrace S rho hn).GroupAt (digestOf S rho) (rho.ownKey v) (cutMap S rho hn i) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
          cutMap S rho hn (i + 1) = cutMap S rho hn i + (Node.exec (digestOf S rho) (rho.ownKey v)
            ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
  sorry

/-- An honest node awake at a public time (from `0` on) ticks there. -/
theorem simTrace_tick_of_awake (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, 0 ≤ t → (S.params (pubOf E) hn).toParams.IsPublic t →
      (simTrace S rho hn).awake y t → ∃ j, (simTrace S rho hn).TickAt (digestOf S rho) y j t := by
  intro y hy t ht0 hp hw
  obtain ⟨hwE, -, k, -, htk⟩ := (awake_iff' S rho hn y t).mp hw
  have hth : t ≤ rho.horizon := htk.trans (time_bounds S rho hn hv k).2
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp (hv.tick_total _ hy t ht0 hth hwE)
  obtain ⟨hg, -⟩ := simTrace_tick_public_group S rho hn hv _ hy i t he hp
  rw [ownKey_key] at hg
  exact ⟨_, _, hg⟩

/-- An engine tick at a non-public time has no cut. -/
theorem simTrace_tick_other (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      ¬ (S.params (pubOf E) hn).toParams.IsPublic t →
        cutMap S rho hn (i + 1) = cutMap S rho hn i := by
  sorry

/-- An engine delivery to an honest node is the groups of the canonical objects it delivers. -/
theorem simTrace_deliver (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i o t, rho.events[i]? = some (.deliver v o t) →
      DeliverSeq (simTrace S rho hn) (digestOf S rho) (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
  sorry

/-- An engine restart of an honest node is the node's restart group. -/
theorem simTrace_restart (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.restart v t) →
      (simTrace S rho hn).GroupAt (digestOf S rho) (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
        cutMap S rho hn (i + 1) = cutMap S rho hn i + (Node.exec (digestOf S rho) (rho.ownKey v)
          ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  sorry

/-- An honest node awake in the trace is awake in the environment, within `[0, horizon]`: the
trace's horizon is within the engine's, as every cut's time is an event's. -/
theorem simTrace_awake_of (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon := by
  sorry

/-- The engine releases an honest node's own block at the tick that proposes it (the proposal
duty's candidate is `blockObj` of the block, `releasable` by `proposal_releasable`, passed by
`protects_blockObj`). -/
theorem simTrace_block_released (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).OwnBlockAt y k B →
      rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B)
        ((simTrace S rho hn).time k) := by
  sorry

/-- The engine releases an honest node's vote from its emission on (the vote is queued in the
outbox and released by a poll step of the next tick at which the node is awake; `outbox_le_two`
gives that two poll steps suffice). -/
theorem simTrace_vote_released (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k m, (simTrace S rho hn).EmitAt y k m →
      ReleasedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  sorry

/-- The engine releases an honest node's attestation from its signing on (queued by `fgUpdate`,
released by the tick's last poll steps; `protects_own_att` passes it). -/
theorem simTrace_att_released (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).SignAt y k a →
      ReleasedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  sorry

/-- An honest node relays a block it accepts from the wire. -/
theorem simTrace_block_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).AcceptAt y k B →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B)
          ((simTrace S rho hn).time k) := by
  sorry

/-- An honest node relays a vote it admits from the wire. -/
theorem simTrace_vote_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k m, (simTrace S rho hn).MsgCallAt y k m →
      m ∈ ((simTrace S rho hn).post k).ac.pool m.slot →
        RelayedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  sorry

/-- An honest node relays an attestation it receives from the wire. -/
theorem simTrace_att_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).AttCallAt y k a →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  sorry

/-! ## The trace is a Goldilocks run -/

/-- **The simulating trace is a Goldilocks run** at the engine's digest, for the honest keys:
the fields above. -/
theorem simTrace_goldilocksRun (hv : rho.ExecutionValid) :
    GoldilocksRun (digestOf S rho) (honestKeys S rho) (simTrace S rho hn) where
  init := simTrace_init S rho hn
  grouped := simTrace_grouped S rho hn hv
  cutLaw := simTrace_cutLaw S rho hn hv
  wire := simTrace_wire S rho hn hv
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
