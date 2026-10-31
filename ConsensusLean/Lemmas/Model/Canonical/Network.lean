module
public import ConsensusLean.Lemmas.Model.Canonical.Schedule
public import ConsensusLean.Lemmas.Model.Canonical.Unforgeable

public section

/-! The canonical network is causal, eager from its GST `g` and quiet before
it. Prefix invariance identifies
the release that supplied each delivery; event uniqueness identifies every
release in the prefix through the delivery start time. -/
namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}
namespace Run
variable (rho : Run F E)

theorem stages_prefix (g : Time) {m n : Nat} (hmn : m ≤ n) :
    ∃ tail, rho.stages g n = rho.stages g m ++ tail := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    exact ⟨[], (List.append_nil _).symm⟩
  | succ n ih =>
    by_cases hm : m ≤ n
    · obtain ⟨tail, ht⟩ := ih hm
      refine ⟨tail ++ rho.layer g (rho.stages g n) (n : Time), ?_⟩
      rw [stages_succ, ht, List.append_assoc]
    · have : m = n + 1 := by omega
      subst m
      exact ⟨[], (List.append_nil _).symm⟩

theorem front_prefix (g : Time) {k n : Nat} (hk : k < n) :
    ∃ tail, rho.stages g n = rho.front (rho.stages g k) (k : Time) ++ tail := by
  obtain ⟨tail, ht⟩ := rho.stages_prefix g (show k + 1 ≤ n by omega)
  refine ⟨rho.deliveryEvents g (rho.front (rho.stages g k) (k : Time)) (k : Time) ++ tail, ?_⟩
  rw [ht, stages_succ, layer_eq, front_eq]
  simp only [List.append_assoc]

theorem tick_mem_stages (g : Time) {n : Nat} {v : V} {t : Time}
    (hv : v ∈ rho.honest) (ha : E.awake v t = true)
    (h0 : 0 ≤ t) (hn : t.toNat < n) : Event.tick v t ∈ rho.stages g n := by
  apply (rho.mem_stages g n _).mpr
  refine ⟨t.toNat, hn, ?_⟩
  rw [Int.toNat_of_nonneg h0]
  simp only [layer_eq, List.mem_append]
  exact Or.inl (Or.inr ((rho.mem_tickEvents t _).mpr ⟨v, hv, ha, rfl⟩))

theorem canonical_causal (g : Time) : (rho.withEvents (rho.canonicalEvents g)).Causal := by
  rw [causal_iff]
  intro i w o t hi
  rw [withEvents_events] at hi
  have hm := List.mem_of_getElem? hi
  rw [canonicalEvents_eq] at hm
  obtain ⟨k, hk, he⟩ := (rho.mem_stages g _ _).mp hm
  have htk : t = (k : Time) := rho.layer_time g _ _ he
  subst t
  have hp : o ∈ rho.pool (rho.front (rho.stages g k) (k : Time)) := by
    simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at he
    rcases he with (⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩) | ⟨_, v, _, _, p, hp, h⟩
    · cases h
    · cases h
    · cases h; exact hp
  obtain ⟨tail, htail⟩ := rho.front_prefix g hk
  obtain ⟨v, t', j, hj, ho⟩ := (rho.mem_pool _ _).mp hp
  obtain ⟨e, hje, _, _⟩ := hj.exists_event
  rw [withEvents_events] at hje
  have hjl : j < (rho.front (rho.stages g k) (k : Time)).length :=
    (List.getElem?_eq_some_iff.mp hje).1
  have hni : ¬ Event.deliver w o (k : Time) ∈ rho.front (rho.stages g k) (k : Time) := by
    intro h
    simp only [front_eq, List.mem_append] at h
    rcases h with (h | h) | h
    · have hb := (rho.stages_time g k h).2
      exact lt_irrefl _ hb
    · simp at h
    · simp at h
  have hile : (rho.front (rho.stages g k) (k : Time)).length ≤ i := by
    by_contra h
    have hil : i < (rho.front (rho.stages g k) (k : Time)).length := by omega
    apply hni
    apply List.mem_of_getElem?
    rw [show (rho.front (rho.stages g k) (k : Time))[i]? =
      (rho.canonicalEvents g)[i]? by rw [(rho.canonicalEvents_eq g).trans htail,
        List.getElem?_append_left hil]]
    exact hi
  refine ⟨j, v, t', lt_of_lt_of_le hjl hile, ?_, ?_⟩
  · rw [(rho.canonicalEvents_eq g).trans htail]
    exact rho.sendsAt_append _ tail hj
  · change (rho.withEvents (rho.canonicalEvents g)).releasesAt j |> fun l => o ∈ l
    rw [(rho.canonicalEvents_eq g).trans htail, rho.releasesAt_append _ _ hjl]
    exact ho

/-- A canonical event whose time is below `a` lies in the stages before `a`. -/
theorem mem_stages_of_time_lt (g : Time) {n : Nat} {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.stages g n) {a : Time} (ha : e.time < a) : e ∈ rho.stages g a.toNat := by
  obtain ⟨k, _, hk⟩ := (rho.mem_stages g n e).mp he
  have htk : e.time = (k : Time) := rho.layer_time g _ _ hk
  refine (rho.mem_stages g _ e).mpr ⟨k, ?_, hk⟩
  rw [htk] at ha
  have h := (Int.toNat_lt_toNat (lt_of_le_of_lt (Int.natCast_nonneg k) ha)).mpr ha
  simpa using h

/-- From GST `g` on, every honest release at `t` is received by every awake
honest node at every time `a` with `max t g < a ≤ horizon`. The bound is strict
because a delivery at `a` can release at `a`, after the schedule's deliveries
at `a` were fixed; such a release is served from `a + 1` on. -/
theorem canonical_eagerFrom (g : Time) (h0 : 0 ≤ rho.horizon) :
    ∀ v ∈ rho.honest, ∀ o t, (rho.withEvents (rho.canonicalEvents g)).releases v o t →
      ∀ w ∈ rho.honest, ∀ a, max t g < a → a ≤ rho.horizon →
        E.awake w a = true → (rho.withEvents (rho.canonicalEvents g)).receives w o a := by
  intro v hv o t hr w hw a hmax hah haa
  have hta : t < a := lt_of_le_of_lt (le_max_left t g) hmax
  have hga : g ≤ a := le_of_lt (lt_of_le_of_lt (le_max_right t g) hmax)
  change a ≤ rho.horizon at hah
  have hr0 := hr
  rw [canonicalEvents_eq] at hr0
  obtain ⟨i, hi, _⟩ := hr
  obtain ⟨e, hie, _, het⟩ := hi.exists_event
  have htm := List.mem_of_getElem? hie
  rw [withEvents_events] at htm
  have ht0 : 0 ≤ t := het ▸ (rho.canonical_in_horizon g h0 htm).1
  have ha0 : 0 ≤ a := le_trans ht0 (le_of_lt hta)
  have han : a.toNat < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hah
    omega
  obtain ⟨tail, htail⟩ := rho.front_prefix g han
  have hr' :
      (rho.withEvents (rho.front (rho.stages g a.toNat) (a.toNat : Time))).releases v o t := by
    apply rho.releases_restrict _ tail
    · rw [← htail]; exact rho.stages_nodup g _
    · intro e' he' _ het'
      rw [← htail] at he'
      rw [front_eq]
      apply List.mem_append_left
      apply List.mem_append_left
      exact rho.mem_stages_of_time_lt g he' (het' ▸ hta)
    · rw [← htail]
      exact hr0
  have hpool := (rho.mem_pool _ o).mpr ⟨v, t, hr'⟩
  have hdel : Event.deliver w o a ∈ (rho.canonicalEvents g) := by
    apply rho.canonical_layer g a ha0 hah
    simp only [layer_eq, List.mem_append]
    apply Or.inr
    apply (rho.mem_deliveryEvents g _ a _).mpr
    exact ⟨hga, w, hw, haa, o, by simpa only [Int.toNat_of_nonneg ha0] using hpool, rfl⟩
  rw [← withEvents_events rho (rho.canonicalEvents g)] at hdel
  exact List.mem_iff_getElem?.mp hdel

/-- No delivery before GST `g`. -/
theorem canonical_quiet (g : Time) :
    ∀ w o t, (rho.withEvents (rho.canonicalEvents g)).receives w o t → g ≤ t := by
  intro w o t ⟨i, hi⟩
  rw [withEvents_events, canonicalEvents_eq] at hi
  obtain ⟨k, _, he⟩ := (rho.mem_stages g _ _).mp (List.mem_of_getElem? hi)
  simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_deliveryEvents] at he
  rcases he with (⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩) | ⟨hg, v, _, _, p, _, h⟩
  · cases h
  · cases h
  · cases h; exact hg

end Run
end Consensus.Model
end
