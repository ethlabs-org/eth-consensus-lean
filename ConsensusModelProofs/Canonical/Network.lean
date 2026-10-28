module
public import ConsensusModelProofs.Canonical.Schedule
public import ConsensusModelProofs.Canonical.Unforgeable

@[expose] public section

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
    exact ⟨[], rfl⟩
  | succ n ih =>
    by_cases hm : m ≤ n
    · obtain ⟨tail, ht⟩ := ih hm
      refine ⟨tail ++ rho.layer g (rho.stages g n) (n : Time), ?_⟩
      rw [stages, ht, List.append_assoc]
    · have : m = n + 1 := by omega
      subst m
      exact ⟨[], (List.append_nil _).symm⟩

theorem front_prefix (g : Time) {k n : Nat} (hk : k < n) :
    ∃ tail, rho.stages g n = rho.front (rho.stages g k) (k : Time) ++ tail := by
  obtain ⟨tail, ht⟩ := rho.stages_prefix g (show k + 1 ≤ n by omega)
  refine ⟨rho.deliveryEvents g (rho.front (rho.stages g k) (k : Time)) (k : Time) ++ tail, ?_⟩
  rw [ht, stages, layer, front]
  simp only [List.append_assoc]

theorem tick_mem_stages (g : Time) {n : Nat} {v : V} {t : Time}
    (hv : v ∈ rho.honest) (ha : E.awake v t = true)
    (h0 : 0 ≤ t) (hn : t.toNat < n) : Event.tick v t ∈ rho.stages g n := by
  apply (rho.mem_stages g n _).mpr
  refine ⟨t.toNat, hn, ?_⟩
  rw [Int.toNat_of_nonneg h0]
  simp only [layer, List.mem_append]
  exact Or.inl (Or.inr ((rho.mem_tickEvents t _).mpr ⟨v, hv, ha, rfl⟩))

theorem canonical_causal (g : Time) : (rho.withEvents (rho.canonicalEvents g)).Causal := by
  intro i w o t hi
  have hm := List.mem_of_getElem? hi
  obtain ⟨k, hk, he⟩ := (rho.mem_stages g _ _).mp hm
  have htk : t = (k : Time) := rho.layer_time g _ _ he
  subst t
  have hp : o ∈ rho.pool (rho.front (rho.stages g k) (k : Time)) := by
    simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at he
    rcases he with (⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩) | ⟨_, v, _, _, p, hp, h⟩
    · cases h
    · cases h
    · cases h; exact hp
  obtain ⟨tail, htail⟩ := rho.front_prefix g hk
  obtain ⟨v, t', j, hj, ho⟩ := (rho.mem_pool _ _).mp hp
  have hjl : j < (rho.front (rho.stages g k) (k : Time)).length :=
    (List.getElem?_eq_some_iff.mp hj).1
  have hni : ¬ Event.deliver w o (k : Time) ∈ rho.front (rho.stages g k) (k : Time) := by
    intro h
    simp only [front, List.mem_append] at h
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
      (rho.canonicalEvents g)[i]? by rw [show (rho.canonicalEvents g) = _ from htail,
        List.getElem?_append_left hil]]
    exact hi
  refine ⟨j, v, t', lt_of_lt_of_le hjl hile, ?_, ?_⟩
  · change (rho.canonicalEvents g)[j]? = _
    rw [show (rho.canonicalEvents g) = _ from htail, List.getElem?_append_left hjl]
    exact hj
  · change (rho.withEvents (rho.canonicalEvents g)).releasesAt j |> fun l => o ∈ l
    rw [show (rho.canonicalEvents g) = _ from htail, rho.releasesAt_append _ _ hjl]
    exact ho

/-- From GST `g` on, every honest release at `t` is received by every awake
honest node at every time `a` with `max t g ≤ a ≤ horizon`. -/
theorem canonical_eagerFrom (g : Time) (h0 : 0 ≤ rho.horizon) :
    ∀ v ∈ rho.honest, ∀ o t, (rho.withEvents (rho.canonicalEvents g)).releases v o t →
      ∀ w ∈ rho.honest, ∀ a, max t g ≤ a → a ≤ rho.horizon →
        E.awake w a = true → (rho.withEvents (rho.canonicalEvents g)).receives w o a := by
  intro v hv o t hr w hw a hmax hah haa
  have hta : t ≤ a := le_trans (le_max_left t g) hmax
  have hga : g ≤ a := le_trans (le_max_right t g) hmax
  change a ≤ rho.horizon at hah
  have hr0 := hr
  have hs := rho.canonical_schedule g h0
  obtain ⟨i, hi, _⟩ := hr
  have htm := List.mem_of_getElem? hi
  have ht0 := (hs.in_horizon _ htm).1
  have hwa := (rho.canonical_sleep g).tick_awake v t htm
  have ha0 : 0 ≤ a := le_trans ht0 hta
  have han : a.toNat < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hah
    omega
  obtain ⟨tail, htail⟩ := rho.front_prefix g han
  have htfront : Event.tick v t ∈ rho.front (rho.stages g a.toNat) (a.toNat : Time) := by
    by_cases heq : t = a
    · subst t
      apply List.mem_append_right
      exact (rho.mem_tickEvents _ _).mpr
        ⟨v, hv, by simpa only [Int.toNat_of_nonneg ha0] using hwa,
          by rw [Int.toNat_of_nonneg ha0]⟩
    · have hlt : t < a := lt_of_le_of_ne hta heq
      apply List.mem_append_left
      apply List.mem_append_left
      apply rho.tick_mem_stages g hv hwa ht0
      exact (Int.toNat_lt_toNat (lt_of_le_of_lt ht0 hlt)).mpr hlt
  have hr' :
      (rho.withEvents (rho.front (rho.stages g a.toNat) (a.toNat : Time))).releases v o t := by
    apply rho.releases_restrict _ tail
    · rw [← htail]; exact rho.stages_nodup g _
    · exact htfront
    · rw [← htail]
      exact hr0
  have hpool := (rho.mem_pool _ o).mpr ⟨v, t, hr'⟩
  have hdel : Event.deliver w o a ∈ (rho.canonicalEvents g) := by
    apply rho.canonical_layer g a ha0 hah
    simp only [layer, List.mem_append]
    apply Or.inr
    apply (rho.mem_deliveryEvents g _ a _).mpr
    exact ⟨hga, w, hw, haa, o, by simpa only [Int.toNat_of_nonneg ha0] using hpool, rfl⟩
  exact List.mem_iff_getElem?.mp hdel

/-- The eager schedule (`g = 0`). -/
theorem canonical_eager (h0 : 0 ≤ rho.horizon) :
    (rho.withEvents (rho.canonicalEvents 0)).EagerDelivery := by
  intro v hv o t hr w hw a hta hah haa
  have hs := rho.canonical_schedule 0 h0
  obtain ⟨i, hi, _⟩ := hr
  have ht0 := (hs.in_horizon _ (List.mem_of_getElem? hi)).1
  exact rho.canonical_eagerFrom 0 h0 v hv o t ⟨i, hi, by assumption⟩ w hw a
    (max_le hta (le_trans ht0 hta)) hah haa

/-- No delivery before GST `g`. -/
theorem canonical_quiet (g : Time) :
    ∀ w o t, (rho.withEvents (rho.canonicalEvents g)).receives w o t → g ≤ t := by
  intro w o t ⟨i, hi⟩
  obtain ⟨k, _, he⟩ := (rho.mem_stages g _ _).mp (List.mem_of_getElem? hi)
  simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_deliveryEvents] at he
  rcases he with (⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩) | ⟨hg, v, _, _, p, _, h⟩
  · cases h
  · cases h
  · cases h; exact hg

end Run
end Consensus.Model
end
