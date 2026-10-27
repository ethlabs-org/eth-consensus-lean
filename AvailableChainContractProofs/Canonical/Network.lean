module
public import AvailableChainContractProofs.Canonical.Schedule
public import AvailableChainContractProofs.Canonical.Unforgeable

@[expose] public section

/-! The canonical network is causal and eager. Prefix invariance identifies
the release that supplied each delivery; event uniqueness identifies every
release in the prefix through the delivery start time. -/
namespace AvailableChain.Contract
open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}
namespace Run
variable (rho : Run F E)

theorem stages_prefix {m n : Nat} (hmn : m ≤ n) :
    ∃ tail, rho.stages n = rho.stages m ++ tail := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    exact ⟨[], rfl⟩
  | succ n ih =>
    by_cases hm : m ≤ n
    · obtain ⟨tail, ht⟩ := ih hm
      refine ⟨tail ++ rho.layer (rho.stages n) (n : Time), ?_⟩
      rw [stages, ht, List.append_assoc]
    · have : m = n + 1 := by omega
      subst m
      exact ⟨[], (List.append_nil _).symm⟩

theorem front_prefix {k n : Nat} (hk : k < n) :
    ∃ tail, rho.stages n = rho.front (rho.stages k) (k : Time) ++ tail := by
  obtain ⟨tail, ht⟩ := rho.stages_prefix (show k + 1 ≤ n by omega)
  refine ⟨rho.deliveryEvents (rho.front (rho.stages k) (k : Time)) (k : Time) ++ tail, ?_⟩
  rw [ht, stages, layer, front]
  simp only [List.append_assoc]

theorem tick_mem_stages {n : Nat} {v : V} {t : Time}
    (hv : v ∈ rho.honest) (ht : PublicTime E t) (ha : E.awake v t = true)
    (h0 : 0 ≤ t) (hn : t.toNat < n) : Event.tick v t ∈ rho.stages n := by
  apply (rho.mem_stages n _).mpr
  refine ⟨t.toNat, hn, ?_⟩
  rw [Int.toNat_of_nonneg h0]
  simp only [layer, List.mem_append]
  exact Or.inl (Or.inr ((rho.mem_tickEvents t _).mpr ⟨v, hv, ht, ha, rfl⟩))

theorem canonical_causal : (rho.withEvents rho.canonicalEvents).Causal := by
  intro i w o t hi
  have hm := List.mem_of_getElem? hi
  obtain ⟨k, hk, he⟩ := (rho.mem_stages _ _).mp hm
  have htk : t = (k : Time) := rho.layer_time _ _ he
  subst t
  have hp : o ∈ rho.pool (rho.front (rho.stages k) (k : Time)) := by
    simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at he
    rcases he with (⟨v, _, _, _, h⟩ | ⟨v, _, _, _, h⟩) | ⟨v, _, _, p, hp, h⟩
    · cases h
    · cases h
    · cases h; exact hp
  obtain ⟨tail, htail⟩ := rho.front_prefix hk
  obtain ⟨v, t', j, hj, ho⟩ := (rho.mem_pool _ _).mp hp
  have hjl : j < (rho.front (rho.stages k) (k : Time)).length :=
    (List.getElem?_eq_some_iff.mp hj).1
  have hni : ¬ Event.deliver w o (k : Time) ∈ rho.front (rho.stages k) (k : Time) := by
    intro h
    simp only [front, List.mem_append] at h
    rcases h with (h | h) | h
    · have hb := (rho.stages_time k h).2
      exact lt_irrefl _ hb
    · simp at h
    · simp at h
  have hile : (rho.front (rho.stages k) (k : Time)).length ≤ i := by
    by_contra h
    have hil : i < (rho.front (rho.stages k) (k : Time)).length := by omega
    apply hni
    apply List.mem_of_getElem?
    rw [show (rho.front (rho.stages k) (k : Time))[i]? =
      (rho.canonicalEvents)[i]? by rw [show rho.canonicalEvents = _ from htail,
        List.getElem?_append_left hil]]
    exact hi
  refine ⟨j, v, t', lt_of_lt_of_le hjl hile, ?_, ?_⟩
  · change rho.canonicalEvents[j]? = _
    rw [show rho.canonicalEvents = _ from htail, List.getElem?_append_left hjl]
    exact hj
  · change (rho.withEvents rho.canonicalEvents).releasesAt j |> fun l => o ∈ l
    rw [show rho.canonicalEvents = _ from htail, rho.releasesAt_append _ _ hjl]
    exact ho

theorem canonical_eager (h0 : 0 ≤ rho.horizon) :
    (rho.withEvents rho.canonicalEvents).EagerDelivery := by
  intro v hv o t hr w hw a hta hah haa
  change a ≤ rho.horizon at hah
  have hr0 := hr
  have hs := rho.canonical_schedule h0
  obtain ⟨i, hi, _⟩ := hr
  have htm := List.mem_of_getElem? hi
  have ht0 := (hs.in_horizon _ htm).1
  have hp := hs.tick_public v t htm
  have hwa := rho.canonical_sleep.tick_awake v t htm
  have ha0 : 0 ≤ a := le_trans ht0 hta
  have han : a.toNat < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hah
    omega
  obtain ⟨tail, htail⟩ := rho.front_prefix han
  have htfront : Event.tick v t ∈ rho.front (rho.stages a.toNat) (a.toNat : Time) := by
    by_cases heq : t = a
    · subst t
      apply List.mem_append_right
      exact (rho.mem_tickEvents _ _).mpr
        ⟨v, hv, by simpa only [Int.toNat_of_nonneg ha0] using hp,
          by simpa only [Int.toNat_of_nonneg ha0] using hwa, by rw [Int.toNat_of_nonneg ha0]⟩
    · have hlt : t < a := lt_of_le_of_ne hta heq
      apply List.mem_append_left
      apply List.mem_append_left
      apply rho.tick_mem_stages hv hp hwa ht0
      exact (Int.toNat_lt_toNat (lt_of_le_of_lt ht0 hlt)).mpr hlt
  have hr' : (rho.withEvents (rho.front (rho.stages a.toNat) (a.toNat : Time))).releases v o t := by
    apply rho.releases_restrict _ tail
    · rw [← htail]; exact rho.stages_nodup _
    · exact htfront
    · rw [← htail]
      exact hr0
  have hpool := (rho.mem_pool _ o).mpr ⟨v, t, hr'⟩
  have hdel : Event.deliver w o a ∈ rho.canonicalEvents := by
    apply rho.canonical_layer a ha0 hah
    simp only [layer, List.mem_append]
    apply Or.inr
    apply (rho.mem_deliveryEvents _ a _).mpr
    exact ⟨w, hw, haa, o, by simpa only [Int.toNat_of_nonneg ha0] using hpool, rfl⟩
  exact List.mem_iff_getElem?.mp hdel

end Run
end AvailableChain.Contract
end
