module
public import ConsensusModelProofs.Canonical.Events

@[expose] public section

/-! The canonical scheduler and its schedule/sleep proofs. Each integer time
has three phases: wake restarts, public ticks, then eager deliveries. Each
phase uses the fixed order from the honest finset and the released pool. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run
variable (rho : Run F E)

noncomputable def wakeEvents (t : Time) : List (Event V (protoOf F E).Object) := by
  classical
  exact ((rho.honest.filter (fun v => 0 < t ∧ Wakes E v t)).toList).map
    (fun v => .restart v t)

noncomputable def tickEvents (t : Time) : List (Event V (protoOf F E).Object) := by
  classical
  exact ((rho.honest.filter (fun v => PublicTime E t ∧ E.awake v t = true)).toList).map
    (fun v => .tick v t)

noncomputable def deliveryEvents (es : List (Event V (protoOf F E).Object)) (t : Time) :
    List (Event V (protoOf F E).Object) := by
  classical
  exact ((rho.honest.filter (fun v => E.awake v t = true)).toList).flatMap
    (fun v => (rho.pool es).map (fun o => .deliver v o t))

noncomputable def front (es : List (Event V (protoOf F E).Object)) (t : Time) :=
  es ++ rho.wakeEvents t ++ rho.tickEvents t

noncomputable def layer (es : List (Event V (protoOf F E).Object)) (t : Time) :=
  rho.wakeEvents t ++ rho.tickEvents t ++ rho.deliveryEvents (rho.front es t) t

/-- The first `n` integer times, starting at zero. -/
noncomputable def stages : Nat → List (Event V (protoOf F E).Object)
  | 0 => []
  | n + 1 => stages n ++ rho.layer (stages n) (n : Time)

omit [DecidableEq V] in
@[simp] theorem mem_wakeEvents (t : Time) (e : Event V (protoOf F E).Object) :
    e ∈ rho.wakeEvents t ↔
      ∃ v ∈ rho.honest, 0 < t ∧ Wakes E v t ∧ e = .restart v t := by
  classical
  simp only [wakeEvents, List.mem_map, Finset.mem_toList, Finset.mem_filter]
  aesop

omit [DecidableEq V] in
@[simp] theorem mem_tickEvents (t : Time) (e : Event V (protoOf F E).Object) :
    e ∈ rho.tickEvents t ↔
      ∃ v ∈ rho.honest, PublicTime E t ∧ E.awake v t = true ∧ e = .tick v t := by
  classical
  simp only [tickEvents, List.mem_map, Finset.mem_toList, Finset.mem_filter]
  aesop

@[simp] theorem mem_deliveryEvents (es : List (Event V (protoOf F E).Object))
    (t : Time) (e : Event V (protoOf F E).Object) :
    e ∈ rho.deliveryEvents es t ↔
      ∃ v ∈ rho.honest, E.awake v t = true ∧
        ∃ o ∈ rho.pool es, e = .deliver v o t := by
  classical
  simp only [deliveryEvents, List.mem_flatMap, List.mem_map, Finset.mem_toList,
    Finset.mem_filter]
  aesop

theorem layer_time (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.layer es t) : e.time = t := by
  simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_deliveryEvents] at he
  rcases he with (⟨v, _, _, _, rfl⟩ | ⟨v, _, _, _, rfl⟩) | ⟨v, _, _, o, _, rfl⟩ <;> rfl

theorem layer_honest (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.layer es t) : e.node ∈ rho.honest := by
  simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_deliveryEvents] at he
  rcases he with (⟨v, hv, _, _, rfl⟩ | ⟨v, hv, _, _, rfl⟩) | ⟨v, hv, _, o, _, rfl⟩ <;>
    exact hv

theorem layer_sorted (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.layer es t).Pairwise Event.keyLe := by
  classical
  have hw : ∀ e ∈ rho.wakeEvents t, e.time = t ∧ e.phase = 0 := by
    intro e he
    obtain ⟨v, _, _, _, rfl⟩ := (rho.mem_wakeEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have ht : ∀ e ∈ rho.tickEvents t, e.time = t ∧ e.phase = 1 := by
    intro e he
    obtain ⟨v, _, _, _, rfl⟩ := (rho.mem_tickEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have hd : ∀ e ∈ rho.deliveryEvents (rho.front es t) t, e.time = t ∧ e.phase = 2 := by
    intro e he
    obtain ⟨v, _, _, o, _, rfl⟩ := (rho.mem_deliveryEvents _ t e).mp he
    exact ⟨rfl, rfl⟩
  have block {l : List (Event V (protoOf F E).Object)} {k : Nat}
      (h : ∀ e ∈ l, e.time = t ∧ e.phase = k) : l.Pairwise Event.keyLe := by
    apply List.pairwise_of_forall_mem_list
    intro e he f hf
    exact Or.inr ⟨(h e he).1.trans (h f hf).1.symm, by rw [(h e he).2, (h f hf).2]⟩
  simp only [layer, List.pairwise_append]
  refine ⟨⟨block hw, block ht, ?_⟩, block hd, ?_⟩
  · intro e he f hf
    exact Or.inr ⟨(hw e he).1.trans (ht f hf).1.symm, by rw [(hw e he).2, (ht f hf).2]; decide⟩
  · intro e he f hf
    have hf' := hd f hf
    rcases List.mem_append.mp he with he | he
    · exact Or.inr ⟨(hw e he).1.trans hf'.1.symm, by rw [(hw e he).2, hf'.2]; decide⟩
    · exact Or.inr ⟨(ht e he).1.trans hf'.1.symm, by rw [(ht e he).2, hf'.2]; decide⟩

theorem layer_nodup (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.layer es t).Nodup := by
  classical
  have hw : (rho.wakeEvents t).Nodup := by
    apply List.Nodup.map _ (Finset.nodup_toList _)
    intro a b h
    exact Event.restart.inj h |>.1
  have ht : (rho.tickEvents t).Nodup := by
    apply List.Nodup.map _ (Finset.nodup_toList _)
    intro a b h
    exact Event.tick.inj h |>.1
  have hd : (rho.deliveryEvents (rho.front es t) t).Nodup := by
    unfold deliveryEvents
    rw [List.nodup_flatMap]
    constructor
    · intro v hv
      exact (List.nodup_dedup _).map (fun a b h => Event.deliver.inj h |>.2.1)
    · apply (Finset.nodup_toList _).imp
      intro v w hne
      change List.Disjoint _ _
      rw [List.disjoint_left]
      intro e he hf
      obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
      obtain ⟨p, _, hp⟩ := List.mem_map.mp hf
      exact hne (Event.deliver.inj hp |>.1).symm
  simp only [layer, List.nodup_append]
  refine ⟨⟨hw, ht, ?_⟩, hd, ?_⟩
  · intro e he f hf hef
    subst f
    obtain ⟨v, _, _, _, rfl⟩ := (rho.mem_wakeEvents t e).mp he
    simp at hf
  · intro e he f hf hef
    subst f
    obtain ⟨v, _, _, o, _, rfl⟩ := (rho.mem_deliveryEvents _ t e).mp hf
    simp at he

theorem stages_time (n : Nat) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.stages n) : 0 ≤ e.time ∧ e.time < (n : Time) := by
  induction n with
  | zero => simp [stages] at he
  | succ n ih =>
    rcases List.mem_append.mp he with he | he
    · have := ih he
      constructor
      · exact this.1
      · exact lt_trans this.2 (by exact_mod_cast Nat.lt_succ_self n)
    · rw [rho.layer_time _ _ he]
      exact ⟨Int.natCast_nonneg n, by exact_mod_cast Nat.lt_succ_self n⟩

theorem stages_sorted (n : Nat) : (rho.stages n).Pairwise Event.keyLe := by
  induction n with
  | zero => simp [stages]
  | succ n ih =>
    rw [stages, List.pairwise_append]
    refine ⟨ih, rho.layer_sorted _ _, ?_⟩
    intro e he f hf
    exact Or.inl (by rw [rho.layer_time _ _ hf]; exact (rho.stages_time n he).2)

theorem stages_nodup (n : Nat) : (rho.stages n).Nodup := by
  induction n with
  | zero => simp [stages]
  | succ n ih =>
    rw [stages, List.nodup_append]
    refine ⟨ih, rho.layer_nodup _ _, ?_⟩
    intro e he f hf hef
    subst f
    have := (rho.stages_time n he).2
    rw [rho.layer_time _ _ hf] at this
    exact lt_irrefl _ this

theorem mem_stages (n : Nat) (e : Event V (protoOf F E).Object) :
    e ∈ rho.stages n ↔ ∃ k < n, e ∈ rho.layer (rho.stages k) (k : Time) := by
  induction n with
  | zero => simp [stages]
  | succ n ih =>
    simp only [stages, List.mem_append, ih]
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

/-- The run through the inclusive horizon. -/
noncomputable def canonicalEvents := rho.stages (rho.horizon.toNat + 1)

theorem canonical_in_horizon (h0 : 0 ≤ rho.horizon)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.canonicalEvents) :
    0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  have h := rho.stages_time _ he
  have hn : (rho.horizon.toNat : Int) = rho.horizon := Int.toNat_of_nonneg h0
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) ≤ rho.horizon
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) < ((rho.horizon.toNat + 1 : Nat) : Int) at h
  push_cast at h
  dsimp [Time] at *
  omega

theorem canonical_layer (t : Time) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon)
    {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.layer (rho.stages t.toNat) t) : e ∈ rho.canonicalEvents := by
  apply (rho.mem_stages _ e).mpr
  refine ⟨t.toNat, ?_, ?_⟩
  · have := Int.toNat_le_toNat hh
    omega
  · simpa only [Int.toNat_of_nonneg h0] using he

theorem canonical_schedule (h0 : 0 ≤ rho.horizon) :
    (rho.withEvents rho.canonicalEvents).ScheduleWellFormed := by
  refine ⟨h0, rho.stages_sorted _, rho.stages_nodup _, ?_, ?_, ?_, ?_⟩
  · exact fun e he => rho.canonical_in_horizon h0 he
  · intro e he
    obtain ⟨k, _, hk⟩ := (rho.mem_stages _ e).mp he
    exact rho.layer_honest _ _ hk
  · intro v t he
    obtain ⟨k, _, hk⟩ := (rho.mem_stages _ _).mp he
    simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at hk
    rcases hk with (⟨w, _, _, _, h⟩ | ⟨w, _, hp, _, h⟩) | ⟨w, _, _, o, _, h⟩
    · cases h
    · cases h; exact hp
    · cases h
  · intro v hv t ht hh ha
    have ht0 : 0 ≤ t := by
      obtain ⟨k, rfl⟩ := ht
      exact mul_nonneg (Int.natCast_nonneg k) E.Δ_pos.le
    apply rho.canonical_layer t ht0 hh
    simp only [layer, List.mem_append]
    exact Or.inl (Or.inr ((rho.mem_tickEvents t _).mpr ⟨v, hv, ht, ha, rfl⟩))

theorem canonical_sleep : (rho.withEvents rho.canonicalEvents).SleepWellFormed := by
  have event_layer {e : Event V (protoOf F E).Object} (he : e ∈ rho.canonicalEvents) :
      ∃ k, e ∈ rho.layer (rho.stages k) (k : Time) := by
    obtain ⟨k, _, hk⟩ := (rho.mem_stages _ e).mp he
    exact ⟨k, hk⟩
  constructor
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at hk
    rcases hk with (⟨w, _, _, _, h⟩ | ⟨w, _, _, ha, h⟩) | ⟨w, _, _, o, _, h⟩
    · cases h
    · cases h; exact ha
    · cases h
  · intro v o t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at hk
    rcases hk with (⟨w, _, _, _, h⟩ | ⟨w, _, _, _, h⟩) | ⟨w, _, ha, p, _, h⟩
    · cases h
    · cases h
    · cases h; exact ha
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    simp only [layer, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at hk
    rcases hk with (⟨w, _, hp, ha, h⟩ | ⟨w, _, _, _, h⟩) | ⟨w, _, _, o, _, h⟩
    · cases h; exact ⟨hp, ha⟩
    · cases h
    · cases h
  · intro v hv t hp hh hw
    apply rho.canonical_layer t hp.le hh
    simp only [layer, List.mem_append]
    exact Or.inl (Or.inl ((rho.mem_wakeEvents t _).mpr ⟨v, hv, hp, hw, rfl⟩))

end Run
end Consensus.Model
end
