module
public import ConsensusLean.Lemmas.Model.Canonical.Events

public section

/-! The canonical scheduler and its schedule/sleep proofs. Each integer time
has three phases: wake restarts, ticks, then eager deliveries. Each
phase uses the fixed order from the honest finset and the released pool.
The scheduler is parameterised by a GST `g`: the delivery layer is empty at
times `< g` (no message is received before `g`), and from `g` on every
released object is delivered to every awake honest node. `g ≤ 0` is the
eager schedule; `g` past the horizon gives a silent network. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run
variable (rho : Run F E)

noncomputable def wakeEvents (t : Time) : List (Event V (protoOf F E).Object) := by
  classical
  exact (((Finset.univ \ rho.faultyAt t).filter (fun v => 0 < t ∧ Wakes E v t)).toList).map
    (fun v => .restart v t)

noncomputable def tickEvents (t : Time) : List (Event V (protoOf F E).Object) := by
  classical
  exact (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).map
    (fun v => .tick v t)

noncomputable def deliveryEvents (g : Time) (es : List (Event V (protoOf F E).Object))
    (t : Time) : List (Event V (protoOf F E).Object) := by
  classical
  exact if g ≤ t then (((Finset.univ \ rho.faultyAt t).filter
    (fun v => E.awake v t = true)).toList).flatMap
    (fun v => (rho.pool es).map (fun o => .deliver v o t)) else []

noncomputable def front (es : List (Event V (protoOf F E).Object)) (t : Time) :=
  es ++ rho.wakeEvents t ++ rho.tickEvents t

theorem wakeEvents_eq (t : Time) : rho.wakeEvents t = (by
    classical
    exact (((Finset.univ \ rho.faultyAt t).filter (fun v => 0 < t ∧ Wakes E v t)).toList).map
      (fun v => .restart v t)) := by rfl

theorem tickEvents_eq (t : Time) : rho.tickEvents t =
    (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).map
      (fun v => .tick v t) := by rfl

theorem deliveryEvents_eq (g : Time) (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.deliveryEvents g es t = if g ≤ t then
      (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).flatMap
        (fun v => (rho.pool es).map (fun o => .deliver v o t)) else [] := by rfl

noncomputable def layer (g : Time) (es : List (Event V (protoOf F E).Object)) (t : Time) :=
  rho.wakeEvents t ++ rho.tickEvents t ++ rho.deliveryEvents g (rho.front es t) t

/-- The first `n` integer times, starting at zero. -/
noncomputable def stages (g : Time) : Nat → List (Event V (protoOf F E).Object)
  | 0 => []
  | n + 1 => stages g n ++ rho.layer g (stages g n) (n : Time)

theorem front_eq (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.front es t = es ++ rho.wakeEvents t ++ rho.tickEvents t := by rfl

theorem layer_eq (g : Time) (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.layer g es t =
      rho.wakeEvents t ++ rho.tickEvents t ++ rho.deliveryEvents g (rho.front es t) t := by rfl

@[simp] theorem stages_zero (g : Time) : rho.stages g 0 = [] := by rfl

theorem stages_succ (g : Time) (n : Nat) :
    rho.stages g (n + 1) = rho.stages g n ++ rho.layer g (rho.stages g n) (n : Time) := by rfl

@[simp] theorem mem_wakeEvents (t : Time) (e : Event V (protoOf F E).Object) :
    e ∈ rho.wakeEvents t ↔
      ∃ v, v ∉ rho.faultyAt t ∧ 0 < t ∧ Wakes E v t ∧ e = .restart v t := by
  classical
  delta wakeEvents
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, ⟨hv, ht, hw⟩, rfl⟩
    exact ⟨v, hv, ht, hw, rfl⟩
  · rintro ⟨v, hv, ht, hw, rfl⟩
    exact ⟨v, ⟨hv, ht, hw⟩, rfl⟩

@[simp] theorem mem_tickEvents (t : Time) (e : Event V (protoOf F E).Object) :
    e ∈ rho.tickEvents t ↔
      ∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧ e = .tick v t := by
  classical
  delta tickEvents
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, ⟨hv, hw⟩, rfl⟩
    exact ⟨v, hv, hw, rfl⟩
  · rintro ⟨v, hv, hw, rfl⟩
    exact ⟨v, ⟨hv, hw⟩, rfl⟩

@[simp] theorem mem_deliveryEvents (g : Time) (es : List (Event V (protoOf F E).Object))
    (t : Time) (e : Event V (protoOf F E).Object) :
    e ∈ rho.deliveryEvents g es t ↔
      g ≤ t ∧ ∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧
        ∃ o ∈ rho.pool es, e = .deliver v o t := by
  classical
  delta deliveryEvents
  split_ifs with hg
  · simp only [List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_filter,
      Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, ⟨hv, hw⟩, o, ho, rfl⟩
      exact ⟨hg, v, hv, hw, o, ho, rfl⟩
    · rintro ⟨-, v, hv, hw, o, ho, rfl⟩
      exact ⟨v, ⟨hv, hw⟩, o, ho, rfl⟩
  · simp [hg]

theorem layer_time (g : Time) (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.layer g es t) : e.time = t := by
  simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_deliveryEvents] at he
  rcases he with (⟨v, _, _, _, rfl⟩ | ⟨v, _, _, rfl⟩) | ⟨_, v, _, _, o, _, rfl⟩ <;> rfl

theorem layer_honest (g : Time) (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.layer g es t) :
    e.node ∉ rho.faultyAt e.time := by
  simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_deliveryEvents] at he
  rcases he with (⟨v, hv, _, _, rfl⟩ | ⟨v, hv, _, rfl⟩) | ⟨_, v, hv, _, o, _, rfl⟩ <;>
    exact hv

theorem layer_sorted (g : Time) (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.layer g es t).Pairwise Event.keyLe := by
  classical
  have hw : ∀ e ∈ rho.wakeEvents t, e.time = t ∧ e.phase = 0 := by
    intro e he
    obtain ⟨v, _, _, _, rfl⟩ := (rho.mem_wakeEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have ht : ∀ e ∈ rho.tickEvents t, e.time = t ∧ e.phase = 1 := by
    intro e he
    obtain ⟨v, _, _, rfl⟩ := (rho.mem_tickEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have hd : ∀ e ∈ rho.deliveryEvents g (rho.front es t) t, e.time = t ∧ e.phase = 2 := by
    intro e he
    obtain ⟨_, v, _, _, o, _, rfl⟩ := (rho.mem_deliveryEvents g _ t e).mp he
    exact ⟨rfl, rfl⟩
  have block {l : List (Event V (protoOf F E).Object)} {k : Nat}
      (h : ∀ e ∈ l, e.time = t ∧ e.phase = k) : l.Pairwise Event.keyLe := by
    apply List.pairwise_of_forall_mem_list
    intro e he f hf
    exact Or.inr ⟨(h e he).1.trans (h f hf).1.symm, by rw [(h e he).2, (h f hf).2]⟩
  simp only [layer_eq, List.pairwise_append]
  refine ⟨⟨block hw, block ht, ?_⟩, block hd, ?_⟩
  · intro e he f hf
    exact Or.inr ⟨(hw e he).1.trans (ht f hf).1.symm, by rw [(hw e he).2, (ht f hf).2]; decide⟩
  · intro e he f hf
    have hf' := hd f hf
    rcases List.mem_append.mp he with he | he
    · exact Or.inr ⟨(hw e he).1.trans hf'.1.symm, by rw [(hw e he).2, hf'.2]; decide⟩
    · exact Or.inr ⟨(ht e he).1.trans hf'.1.symm, by rw [(ht e he).2, hf'.2]; decide⟩

theorem layer_nodup (g : Time) (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.layer g es t).Nodup := by
  classical
  have hw : (rho.wakeEvents t).Nodup := by
    apply List.Nodup.map _ (Finset.nodup_toList _)
    intro a b h
    exact Event.restart.inj h |>.1
  have ht : (rho.tickEvents t).Nodup := by
    apply List.Nodup.map _ (Finset.nodup_toList _)
    intro a b h
    exact Event.tick.inj h |>.1
  have hd : (rho.deliveryEvents g (rho.front es t) t).Nodup := by
    delta deliveryEvents
    split_ifs
    swap
    · exact List.nodup_nil
    rw [List.nodup_flatMap]
    constructor
    · intro v hv
      exact (rho.nodup_pool _).map (fun a b h => Event.deliver.inj h |>.2.1)
    · apply (Finset.nodup_toList _).imp
      intro v w hne
      change List.Disjoint _ _
      rw [List.disjoint_left]
      intro e he hf
      obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
      obtain ⟨p, _, hp⟩ := List.mem_map.mp hf
      exact hne (Event.deliver.inj hp |>.1).symm
  simp only [layer_eq, List.nodup_append]
  refine ⟨⟨hw, ht, ?_⟩, hd, ?_⟩
  · intro e he f hf hef
    subst f
    obtain ⟨v, _, _, _, rfl⟩ := (rho.mem_wakeEvents t e).mp he
    simp at hf
  · intro e he f hf hef
    subst f
    obtain ⟨_, v, _, _, o, _, rfl⟩ := (rho.mem_deliveryEvents g _ t e).mp hf
    simp at he

theorem stages_time (g : Time) (n : Nat) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.stages g n) : 0 ≤ e.time ∧ e.time < (n : Time) := by
  induction n with
  | zero => simp at he
  | succ n ih =>
    rcases List.mem_append.mp he with he | he
    · have := ih he
      constructor
      · exact this.1
      · exact lt_trans this.2 (by exact_mod_cast Nat.lt_succ_self n)
    · rw [rho.layer_time g _ _ he]
      exact ⟨Int.natCast_nonneg n, by exact_mod_cast Nat.lt_succ_self n⟩

theorem stages_sorted (g : Time) (n : Nat) : (rho.stages g n).Pairwise Event.keyLe := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [stages_succ, List.pairwise_append]
    refine ⟨ih, rho.layer_sorted g _ _, ?_⟩
    intro e he f hf
    exact Or.inl (by rw [rho.layer_time g _ _ hf]; exact (rho.stages_time g n he).2)

theorem stages_nodup (g : Time) (n : Nat) : (rho.stages g n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [stages_succ, List.nodup_append]
    refine ⟨ih, rho.layer_nodup g _ _, ?_⟩
    intro e he f hf hef
    subst f
    have := (rho.stages_time g n he).2
    rw [rho.layer_time g _ _ hf] at this
    exact lt_irrefl _ this

theorem mem_stages (g : Time) (n : Nat) (e : Event V (protoOf F E).Object) :
    e ∈ rho.stages g n ↔ ∃ k < n, e ∈ rho.layer g (rho.stages g k) (k : Time) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [stages_succ, List.mem_append, ih]
    constructor
    · rintro (⟨k, hk, he⟩ | he)
      · exact ⟨k, by omega, he⟩
      · exact ⟨n, by omega, he⟩
    · rintro ⟨k, hk, he⟩
      by_cases hkn : k < n
      · exact Or.inl ⟨k, hkn, he⟩
      · have : k = n := by omega
        subst k
        exact Or.inr he

/-- The run through the inclusive horizon, with GST `g`. -/
noncomputable def canonicalEvents (g : Time) := rho.stages g (rho.horizon.toNat + 1)

theorem canonicalEvents_eq (g : Time) :
    rho.canonicalEvents g = rho.stages g (rho.horizon.toNat + 1) := by rfl

theorem canonical_in_horizon (g : Time) (h0 : 0 ≤ rho.horizon)
    {e : Event V (protoOf F E).Object} (he : e ∈ (rho.canonicalEvents g)) :
    0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  have h := rho.stages_time g _ he
  have hn : (rho.horizon.toNat : Int) = rho.horizon := Int.toNat_of_nonneg h0
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) ≤ rho.horizon
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) < ((rho.horizon.toNat + 1 : Nat) : Int) at h
  push_cast at h
  dsimp [Time] at *
  omega

theorem canonical_layer (g : Time) (t : Time) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon)
    {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.layer g (rho.stages g t.toNat) t) : e ∈ (rho.canonicalEvents g) := by
  apply (rho.mem_stages g _ e).mpr
  refine ⟨t.toNat, ?_, ?_⟩
  · have := Int.toNat_le_toNat hh
    omega
  · simpa only [Int.toNat_of_nonneg h0] using he

theorem canonical_tick_awake (g : Time) :
    ∀ v t, Event.tick v t ∈ rho.canonicalEvents g → E.awake v t = true := by
  intro v t he
  obtain ⟨k, _, hk⟩ := (rho.mem_stages g _ _).mp he
  simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_deliveryEvents] at hk
  rcases hk with (⟨w, _, _, _, h⟩ | ⟨w, _, ha, h⟩) | ⟨_, w, _, _, o, _, h⟩
  · cases h
  · cases h; exact ha
  · cases h

/-- The canonical schedule meets every schedule and sleep condition; with the
three bindings it is a valid execution. -/
theorem canonical_valid_of (g : Time) (h0 : 0 ≤ rho.horizon)
    (hu : (rho.withEvents (rho.canonicalEvents g)).Unforgeable)
    (hsel : (rho.withEvents (rho.canonicalEvents g)).SelValid)
    (hc : (rho.withEvents (rho.canonicalEvents g)).Credentials) :
    (rho.withEvents (rho.canonicalEvents g)).ExecutionValid := by
  rw [withEvents_eq] at hu hsel hc ⊢
  have event_layer {e : Event V (protoOf F E).Object} (he : e ∈ (rho.canonicalEvents g)) :
      ∃ k, e ∈ rho.layer g (rho.stages g k) (k : Time) := by
    obtain ⟨k, _, hk⟩ := (rho.mem_stages g _ e).mp he
    exact ⟨k, hk⟩
  refine ⟨h0, rho.stages_sorted g _, rho.stages_nodup g _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hu, hsel,
    hc⟩
  · exact fun e he => rho.canonical_in_horizon g h0 he
  · intro e he
    obtain ⟨k, _, hk⟩ := (rho.mem_stages g _ e).mp he
    exact rho.layer_honest g _ _ hk
  · intro v t ht0 hh hv ha
    apply rho.canonical_layer g t ht0 hh
    simp only [layer_eq, List.mem_append]
    exact Or.inl (Or.inr ((rho.mem_tickEvents t _).mpr ⟨v, hv, ha, rfl⟩))
  · exact rho.canonical_tick_awake g
  · intro v o t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at hk
    rcases hk with (⟨w, _, _, _, h⟩ | ⟨w, _, _, h⟩) | ⟨_, w, _, ha, p, _, h⟩
    · cases h
    · cases h
    · cases h; exact ha
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at hk
    rcases hk with (⟨w, _, hp, ha, h⟩ | ⟨w, _, _, h⟩) | ⟨_, w, _, _, o, _, h⟩
    · cases h; exact ⟨hp, ha⟩
    · cases h
    · cases h
  · intro v t hp hh hv hw
    apply rho.canonical_layer g t hp.le hh
    simp only [layer_eq, List.mem_append]
    exact Or.inl (Or.inl ((rho.mem_wakeEvents t _).mpr ⟨v, hv, hp, hw, rfl⟩))

end Run
end Consensus.Model
end
