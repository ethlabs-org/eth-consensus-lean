module
public import ConsensusLean.Lemmas.Model.Canonical.Inject

public section

/-! # The canonical schedule with injected objects and a delivery filter (L1)

Additive to `Lemmas/Model/Canonical/Inject`, which it imports and leaves unchanged: the same
schedule with a per-recipient delivery filter on the due releases (`injf`: injected, filtered). At
every integer time through the horizon: wake restarts, then ticks, then, for every awake honest
recipient `v`, the deliveries of the injected objects `inj t v` followed by the objects released so
far by the events `e` whose batch is due (`Run.duePool`, `e.time + delay e ≤ t`) that the filter
serves `v` (`pol es v o t`, which may read the schedule so far; each recipient's batch
deduplicated). With a filter that serves
everything it is `Run.injectEvents` (`injfEvents_eq_injectEvents`).

* `injfEvents_source`: every delivery is an injection or the release of an earlier event
  whose batch is due.
* `injfEvents_receives`: a due release is received by every awake honest node the filter
  serves it to.
* `injfEvents_valid`: the schedule is a valid execution when every injected object is
  signed only by keys compromised at its delivery time and only by selected keys.
* `injfEvents_psync`: with a filter that serves everything and every delay below both
  network bounds the log is synchronous (`PSync 0`).
* `injfStages_congr`: two filtered schedules whose injections and filters agree before
  `s` have the same stages up to `s`.
* `injfEvents_eq_injectEvents` (with `injfDeliveries_eq_injectDeliveries`,
  `injfLayer_eq_injectLayer`, `injfStages_eq_injectStages`, `injfRun_eq_injectRun`): with a filter
  that serves everything the schedule is `Run.injectEvents`.

`Canonical/Inject`'s closure lemmas (`Run.closed_of_sources`, `Run.seen_closed_of_sources`),
`Run.duePool` (read through `Run.duePool_eq`) and `Run.time_le_of_lt` are used as they are. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run

variable (rho : Run F E)

/-! ### The schedule -/

variable (delay : Event V (protoOf F E).Object → Time)
  (inj : Time → V → List (protoOf F E).Object)
  (pol : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool)

/-- The deliveries at `t` after the prefix `es`: to every awake honest node `v`, the injections of
`t` and the due releases that the delivery filter serves it (`pol es v o t`). -/
noncomputable def injfDeliveries (es : List (Event V (protoOf F E).Object)) (t : Time) :
    List (Event V (protoOf F E).Object) := by
  classical
  exact (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).flatMap
    (fun v => (inj t v ++ (rho.duePool delay es t).filter (fun o => pol es v o t)).dedup.map
      (fun o => .deliver v o t))

theorem mem_injfDeliveries (es : List (Event V (protoOf F E).Object)) (t : Time)
    (e : Event V (protoOf F E).Object) :
    e ∈ rho.injfDeliveries delay inj pol es t ↔ ∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧
      ∃ o, (o ∈ inj t v ∨ (o ∈ rho.duePool delay es t ∧ pol es v o t = true)) ∧
        e = .deliver v o t := by
  classical
  unfold injfDeliveries
  simp only [List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_univ, true_and, List.mem_dedup, List.mem_append, List.mem_filter]
  constructor
  · rintro ⟨v, ⟨hv, hw⟩, o, ho, rfl⟩
    exact ⟨v, hv, hw, o, ho, rfl⟩
  · rintro ⟨v, hv, hw, o, ho, rfl⟩
    exact ⟨v, ⟨hv, hw⟩, o, ho, rfl⟩

theorem injfDeliveries_eq (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.injfDeliveries delay inj pol es t = (by
      classical
      exact (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).flatMap
        (fun v => (inj t v ++ (rho.duePool delay es t).filter (fun o => pol es v o t)).dedup.map
          (fun o => .deliver v o t))) := by rfl

theorem injfDeliveries_nodup (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.injfDeliveries delay inj pol es t).Nodup := by
  classical
  unfold injfDeliveries
  rw [List.nodup_flatMap]
  constructor
  · intro v _
    exact (List.nodup_dedup _).map (fun a b h => Event.deliver.inj h |>.2.1)
  · apply (Finset.nodup_toList _).imp
    intro v w hne
    change List.Disjoint _ _
    rw [List.disjoint_left]
    intro e he hf
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp he
    obtain ⟨p, _, hp⟩ := List.mem_map.mp hf
    exact hne (Event.deliver.inj hp |>.1).symm

/-- The layer of time `t` after the prefix `es`. -/
noncomputable def injfLayer (es : List (Event V (protoOf F E).Object)) (t : Time) :
    List (Event V (protoOf F E).Object) :=
  rho.wakeEvents t ++ rho.tickEvents t ++ rho.injfDeliveries delay inj pol (rho.front es t) t

/-- The first `n` integer times. -/
noncomputable def injfStages : Nat → List (Event V (protoOf F E).Object)
  | 0 => []
  | n + 1 => injfStages n ++ rho.injfLayer delay inj pol (injfStages n) (n : Time)

/-- The schedule through the inclusive horizon. -/
noncomputable def injfEvents : List (Event V (protoOf F E).Object) :=
  rho.injfStages delay inj pol (rho.horizon.toNat + 1)

theorem injfLayer_eq (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.injfLayer delay inj pol es t = rho.wakeEvents t ++ rho.tickEvents t ++
      rho.injfDeliveries delay inj pol (rho.front es t) t := by rfl

theorem injfStages_zero : rho.injfStages delay inj pol 0 = [] := by rfl

theorem injfStages_succ (n : Nat) : rho.injfStages delay inj pol (n + 1) =
    rho.injfStages delay inj pol n ++
      rho.injfLayer delay inj pol (rho.injfStages delay inj pol n) (n : Time) := by rfl

theorem injfEvents_eq :
    rho.injfEvents delay inj pol = rho.injfStages delay inj pol (rho.horizon.toNat + 1) := by
  rfl

theorem mem_injfLayer (es : List (Event V (protoOf F E).Object)) (t : Time)
    (e : Event V (protoOf F E).Object) : e ∈ rho.injfLayer delay inj pol es t ↔
      (∃ v, v ∉ rho.faultyAt t ∧ 0 < t ∧ Wakes E v t ∧ e = .restart v t) ∨
      (∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧ e = .tick v t) ∨
      ∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧
        ∃ o, (o ∈ inj t v ∨ (o ∈ rho.duePool delay (rho.front es t) t ∧
          pol (rho.front es t) v o t = true)) ∧ e = .deliver v o t := by
  simp only [injfLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_injfDeliveries, or_assoc]

theorem injfLayer_time (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.injfLayer delay inj pol es t) :
    e.time = t := by
  rcases (rho.mem_injfLayer delay inj pol es t e).mp he with
    ⟨v, _, _, _, rfl⟩ | ⟨v, _, _, rfl⟩ | ⟨v, _, _, o, _, rfl⟩ <;> rfl

theorem injfLayer_honest (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.injfLayer delay inj pol es t) :
    e.node ∉ rho.faultyAt e.time := by
  rcases (rho.mem_injfLayer delay inj pol es t e).mp he with
    ⟨v, hv, _, _, rfl⟩ | ⟨v, hv, _, rfl⟩ | ⟨v, hv, _, o, _, rfl⟩ <;> exact hv

theorem injfLayer_sorted (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.injfLayer delay inj pol es t).Pairwise Event.keyLe := by
  classical
  have hw : ∀ e ∈ rho.wakeEvents t, e.time = t ∧ e.phase = 0 := by
    intro e he
    obtain ⟨v, _, _, _, rfl⟩ := (rho.mem_wakeEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have ht : ∀ e ∈ rho.tickEvents t, e.time = t ∧ e.phase = 1 := by
    intro e he
    obtain ⟨v, _, _, rfl⟩ := (rho.mem_tickEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have hd : ∀ e ∈ rho.injfDeliveries delay inj pol (rho.front es t) t,
      e.time = t ∧ e.phase = 2 := by
    intro e he
    obtain ⟨v, _, _, o, _, rfl⟩ := (rho.mem_injfDeliveries delay inj pol _ t e).mp he
    exact ⟨rfl, rfl⟩
  have block {l : List (Event V (protoOf F E).Object)} {k : Nat}
      (h : ∀ e ∈ l, e.time = t ∧ e.phase = k) : l.Pairwise Event.keyLe := by
    apply List.pairwise_of_forall_mem_list
    intro e he f hf
    exact Or.inr ⟨(h e he).1.trans (h f hf).1.symm, by rw [(h e he).2, (h f hf).2]⟩
  simp only [injfLayer_eq, List.pairwise_append]
  refine ⟨⟨block hw, block ht, ?_⟩, block hd, ?_⟩
  · intro e he f hf
    exact Or.inr ⟨(hw e he).1.trans (ht f hf).1.symm, by rw [(hw e he).2, (ht f hf).2]; decide⟩
  · intro e he f hf
    have hf' := hd f hf
    rcases List.mem_append.mp he with he | he
    · exact Or.inr ⟨(hw e he).1.trans hf'.1.symm, by rw [(hw e he).2, hf'.2]; decide⟩
    · exact Or.inr ⟨(ht e he).1.trans hf'.1.symm, by rw [(ht e he).2, hf'.2]; decide⟩

theorem injfLayer_nodup (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.injfLayer delay inj pol es t).Nodup := by
  classical
  have hwt : (rho.wakeEvents t ++ rho.tickEvents t).Nodup := by
    have h := rho.layer_nodup 0 es t
    rw [layer_eq] at h
    exact (List.nodup_append.mp h).1
  rw [injfLayer_eq, List.nodup_append]
  refine ⟨hwt, rho.injfDeliveries_nodup delay inj pol _ t, ?_⟩
  · intro e he f hf hef
    subst f
    obtain ⟨v, _, _, o, _, rfl⟩ := (rho.mem_injfDeliveries delay inj pol _ t e).mp hf
    simp at he

theorem injfStages_time (n : Nat) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injfStages delay inj pol n) : 0 ≤ e.time ∧ e.time < (n : Time) := by
  induction n with
  | zero => simp [injfStages] at he
  | succ n ih =>
    rw [injfStages_succ] at he
    rcases List.mem_append.mp he with he | he
    · have := ih he
      exact ⟨this.1, lt_trans this.2 (by exact_mod_cast Nat.lt_succ_self n)⟩
    · rw [rho.injfLayer_time delay inj pol _ _ he]
      exact ⟨Int.natCast_nonneg n, by exact_mod_cast Nat.lt_succ_self n⟩

theorem injfStages_sorted (n : Nat) :
    (rho.injfStages delay inj pol n).Pairwise Event.keyLe := by
  induction n with
  | zero => simp [injfStages]
  | succ n ih =>
    rw [injfStages_succ, List.pairwise_append]
    refine ⟨ih, rho.injfLayer_sorted delay inj pol _ _, ?_⟩
    intro e he f hf
    exact Or.inl (by
      rw [rho.injfLayer_time delay inj pol _ _ hf]
      exact (rho.injfStages_time delay inj pol n he).2)

theorem injfStages_nodup (n : Nat) : (rho.injfStages delay inj pol n).Nodup := by
  induction n with
  | zero => simp [injfStages]
  | succ n ih =>
    rw [injfStages_succ, List.nodup_append]
    refine ⟨ih, rho.injfLayer_nodup delay inj pol _ _, ?_⟩
    intro e he f hf hef
    subst f
    have := (rho.injfStages_time delay inj pol n he).2
    rw [rho.injfLayer_time delay inj pol _ _ hf] at this
    exact lt_irrefl _ this

theorem mem_injfStages (n : Nat) (e : Event V (protoOf F E).Object) :
    e ∈ rho.injfStages delay inj pol n ↔
      ∃ k < n, e ∈ rho.injfLayer delay inj pol (rho.injfStages delay inj pol k) (k : Time) := by
  induction n with
  | zero => simp [injfStages]
  | succ n ih =>
    simp only [injfStages_succ, List.mem_append, ih]
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

theorem injfStages_prefix {m n : Nat} (hmn : m ≤ n) :
    ∃ tail, rho.injfStages delay inj pol n = rho.injfStages delay inj pol m ++ tail := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    exact ⟨[], (List.append_nil _).symm⟩
  | succ n ih =>
    by_cases hm : m ≤ n
    · obtain ⟨tail, ht⟩ := ih hm
      refine ⟨tail ++ rho.injfLayer delay inj pol (rho.injfStages delay inj pol n) (n : Time),
        ?_⟩
      rw [injfStages_succ, ht, List.append_assoc]
    · have : m = n + 1 := by omega
      subst m
      exact ⟨[], (List.append_nil _).symm⟩

theorem injfFront_prefix {k n : Nat} (hk : k < n) :
    ∃ tail, rho.injfStages delay inj pol n =
      rho.front (rho.injfStages delay inj pol k) (k : Time) ++ tail := by
  obtain ⟨tail, ht⟩ := rho.injfStages_prefix delay inj pol (show k + 1 ≤ n by omega)
  refine ⟨rho.injfDeliveries delay inj pol
    (rho.front (rho.injfStages delay inj pol k) (k : Time))
    (k : Time) ++ tail, ?_⟩
  rw [ht, injfStages_succ, injfLayer_eq, front_eq]
  simp only [List.append_assoc]

/-- A scheduled event whose time is below `a` lies in the stages before `a`. -/
theorem mem_injfStages_of_time_lt {n : Nat} {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injfStages delay inj pol n) {a : Time} (ha : e.time < a) :
    e ∈ rho.injfStages delay inj pol a.toNat := by
  obtain ⟨k, _, hk⟩ := (rho.mem_injfStages delay inj pol n e).mp he
  have htk : e.time = (k : Time) := rho.injfLayer_time delay inj pol _ _ hk
  refine (rho.mem_injfStages delay inj pol _ e).mpr ⟨k, ?_, hk⟩
  rw [htk] at ha
  have h := (Int.toNat_lt_toNat (lt_of_le_of_lt (Int.natCast_nonneg k) ha)).mpr ha
  simpa using h

theorem injfEvents_in_horizon (h0 : 0 ≤ rho.horizon) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injfEvents delay inj pol) : 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  have h := rho.injfStages_time delay inj pol _ he
  have hn : (rho.horizon.toNat : Int) = rho.horizon := Int.toNat_of_nonneg h0
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) ≤ rho.horizon
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) < ((rho.horizon.toNat + 1 : Nat) : Int) at h
  push_cast at h
  dsimp [Time] at *
  omega

theorem injfEvents_layer (t : Time) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon)
    {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injfLayer delay inj pol (rho.injfStages delay inj pol t.toNat) t) :
    e ∈ rho.injfEvents delay inj pol := by
  apply (rho.mem_injfStages delay inj pol _ e).mpr
  refine ⟨t.toNat, ?_, ?_⟩
  · have := Int.toNat_le_toNat hh
    omega
  · simpa only [Int.toNat_of_nonneg h0] using he

/-- **Agreeing schedulers have the same stages**: injections that agree at the times below `N`,
and filters that agree there on the front of the stages so far, give the same first `N` stages. -/
theorem injfStages_congr {inj' : Time → V → List (protoOf F E).Object}
    {pol' : List (Event V (protoOf F E).Object) → V → (protoOf F E).Object → Time → Bool}
    {N : Nat} (hinj : ∀ n < N, inj (n : Time) = inj' (n : Time))
    (hpol : ∀ n < N, ∀ v o,
      pol (rho.front (rho.injfStages delay inj pol n) (n : Time)) v o (n : Time) =
        pol' (rho.front (rho.injfStages delay inj pol n) (n : Time)) v o (n : Time)) :
    ∀ n ≤ N, rho.injfStages delay inj pol n = rho.injfStages delay inj' pol' n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hf : ∀ v, (rho.duePool delay (rho.front (rho.injfStages delay inj pol n) (n : Time))
        (n : Time)).filter (fun o => pol (rho.front (rho.injfStages delay inj pol n) (n : Time))
          v o (n : Time)) =
        (rho.duePool delay (rho.front (rho.injfStages delay inj pol n) (n : Time))
          (n : Time)).filter (fun o => pol' (rho.front (rho.injfStages delay inj pol n)
            (n : Time)) v o (n : Time)) := fun v =>
      List.filter_congr fun o _ => by rw [hpol n (by omega) v o]
    rw [injfStages_succ, injfStages_succ, ← ih (by omega), injfLayer_eq, injfLayer_eq]
    congr 2
    unfold injfDeliveries
    simp only [hinj n (by omega), hf]

/-- The scheduled run. -/
noncomputable abbrev injfRun : Run F E := rho.withEvents (rho.injfEvents delay inj pol)

/-- **Every delivery is an injection or a due release of an earlier event.** -/
theorem injfEvents_source {i : Nat} {w : V} {o : (protoOf F E).Object} {t : Time}
    (hi : (rho.injfRun delay inj pol).events[i]? = some (.deliver w o t)) :
    o ∈ inj t w ∨ ∃ j < i, ∃ e, (rho.injfRun delay inj pol).events[j]? = some e ∧
      e.time + delay e ≤ t ∧ o ∈ (rho.injfRun delay inj pol).releasesAt j := by
  rw [withEvents_events] at hi
  have hm := List.mem_of_getElem? hi
  rw [injfEvents_eq] at hm
  obtain ⟨k, hk, he⟩ := (rho.mem_injfStages delay inj pol _ _).mp hm
  have htk : t = (k : Time) := rho.injfLayer_time delay inj pol _ _ he
  subst t
  have hp : o ∈ inj (k : Time) w ∨
      o ∈ rho.duePool delay (rho.front (rho.injfStages delay inj pol k) (k : Time))
        (k : Time) := by
    rcases (rho.mem_injfLayer delay inj pol _ _ _).mp he with
      ⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩ | ⟨v, _, _, p, hp, h⟩
    · cases h
    · cases h
    · cases h; exact hp.imp id And.left
  rcases hp with hp | hp
  · exact Or.inl hp
  right
  obtain ⟨tail, htail⟩ := rho.injfFront_prefix delay inj pol hk
  obtain ⟨j, e, hje, hjt, ho⟩ := (rho.mem_duePool delay _ _ o).mp hp
  have hjl : j < (rho.front (rho.injfStages delay inj pol k) (k : Time)).length :=
    (List.getElem?_eq_some_iff.mp hje).1
  have hni :
      ¬ Event.deliver w o (k : Time) ∈ rho.front (rho.injfStages delay inj pol k) (k : Time) := by
    intro h
    simp only [front_eq, List.mem_append] at h
    rcases h with (h | h) | h
    · exact lt_irrefl _ (rho.injfStages_time delay inj pol k h).2
    · simp at h
    · simp at h
  have hile : (rho.front (rho.injfStages delay inj pol k) (k : Time)).length ≤ i := by
    by_contra h
    have hil : i < (rho.front (rho.injfStages delay inj pol k) (k : Time)).length := by omega
    apply hni
    apply List.mem_of_getElem?
    rw [show (rho.front (rho.injfStages delay inj pol k) (k : Time))[i]? =
      (rho.injfEvents delay inj pol)[i]? by rw [(rho.injfEvents_eq delay inj pol).trans htail,
        List.getElem?_append_left hil]]
    exact hi
  refine ⟨j, lt_of_lt_of_le hjl hile, e, ?_, hjt, ?_⟩
  · rw [withEvents_events, (rho.injfEvents_eq delay inj pol).trans htail,
      List.getElem?_append_left hjl]
    exact hje
  · change o ∈ (rho.withEvents (rho.injfEvents delay inj pol)).releasesAt j
    rw [(rho.injfEvents_eq delay inj pol).trans htail, rho.releasesAt_append _ _ hjl]
    exact ho

/-- A release whose batch is due at `t` and whose event lies in the front of `t` (strictly
before `t`, or a tick of `t`) is received at `t` by every awake honest node that the delivery filter
serves it to. -/
theorem injfEvents_receives (h0 : 0 ≤ rho.horizon) {j : Nat}
    {e : Event V (protoOf F E).Object}
    (hj : (rho.injfRun delay inj pol).events[j]? = some e) {o : (protoOf F E).Object}
    (ho : o ∈ (rho.injfRun delay inj pol).releasesAt j) {t : Time} (hdue : e.time + delay e ≤ t)
    (hfront : e.time < t ∨ ∃ v, e = .tick v t) (hth : t ≤ rho.horizon) {w : V}
    (hw : w ∉ rho.faultyAt t) (haw : E.awake w t = true)
    (hpol : pol (rho.front (rho.injfStages delay inj pol t.toNat) (t.toNat : Time)) w o t =
      true) :
    (rho.injfRun delay inj pol).receives w o t := by
  rw [withEvents_events] at hj
  have hem := List.mem_of_getElem? hj
  have ht0 : 0 ≤ t := by
    have := (rho.injfEvents_in_horizon delay inj pol h0 hem).1
    rcases hfront with h | ⟨v, rfl⟩
    · exact this.trans h.le
    · exact this
  have han : t.toNat < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hth
    omega
  obtain ⟨tail, htail⟩ := rho.injfFront_prefix delay inj pol han
  let fr := rho.front (rho.injfStages delay inj pol t.toNat) (t.toNat : Time)
  have hfr : e ∈ fr := by
    simp only [fr, front_eq, List.mem_append]
    rcases hfront with h | ⟨v, rfl⟩
    · exact Or.inl (Or.inl (rho.mem_injfStages_of_time_lt delay inj pol hem h))
    · right
      rw [Int.toNat_of_nonneg ht0]
      have hv := (rho.injfStages_time delay inj pol _ hem)
      have hvalid := rho.injfLayer_honest delay inj pol
      obtain ⟨k, _, hk⟩ := (rho.mem_injfStages delay inj pol _ _).mp hem
      have htk := rho.injfLayer_time delay inj pol _ _ hk
      rcases (rho.mem_injfLayer delay inj pol _ _ _).mp hk with
        ⟨u, _, _, _, h⟩ | ⟨u, hu, hua, h⟩ | ⟨u, _, _, p, _, h⟩
      · cases h
      · cases h
        exact (rho.mem_tickEvents _ _).mpr ⟨v, by simpa [htk] using hu, by simpa [htk] using hua,
          by simp⟩
      · cases h
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hfr
  have hj'l : j' < fr.length := (List.getElem?_eq_some_iff.mp hj').1
  have hfull : rho.injfEvents delay inj pol = fr ++ tail :=
    (rho.injfEvents_eq delay inj pol).trans htail
  have hjj : j' = j := by
    have hn : (rho.injfEvents delay inj pol).Nodup := rho.injfStages_nodup delay inj pol _
    exact (hn.getElem?_inj (by rw [hfull, List.length_append]; omega)).mp
      ((show (rho.injfEvents delay inj pol)[j']? = fr[j']? by
        rw [hfull, List.getElem?_append_left hj'l]).trans (hj'.trans hj.symm))
  subst j'
  have hpool : o ∈ rho.duePool delay fr (t.toNat : Time) := by
    rw [mem_duePool]
    refine ⟨j, e, hj', by rwa [Int.toNat_of_nonneg ht0], ?_⟩
    have := rho.releasesAt_append fr tail hj'l
    rw [← hfull] at this
    rw [← this]
    exact ho
  have hdel : Event.deliver w o t ∈ rho.injfEvents delay inj pol := by
    apply rho.injfEvents_layer delay inj pol t ht0 hth
    rw [mem_injfLayer]
    refine Or.inr (Or.inr ⟨w, hw, haw, o, Or.inr ⟨?_, ?_⟩, rfl⟩)
    · simpa only [fr, Int.toNat_of_nonneg ht0] using hpool
    · simpa only [Int.toNat_of_nonneg ht0] using hpol
  rw [← withEvents_events rho (rho.injfEvents delay inj pol)] at hdel
  exact List.mem_iff_getElem?.mp hdel

/-! ### A filter that serves everything gives `Canonical/Inject`'s schedule -/

section ServeAll

variable {delay inj pol}

/-- **Serving everything, the filtered deliveries are the unfiltered ones**: with a filter that
returns `true` everywhere, `injfDeliveries` is `Run.injectDeliveries`. -/
theorem injfDeliveries_eq_injectDeliveries (hpol : ∀ es v o t, pol es v o t = true)
    (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.injfDeliveries delay inj pol es t = rho.injectDeliveries delay inj es t := by
  rw [injfDeliveries_eq, injectDeliveries_eq]
  congr 1
  funext v
  rw [List.filter_eq_self.mpr fun o _ => hpol es v o t]

/-- Serving everything, the filtered layer is `Run.injectLayer`. -/
theorem injfLayer_eq_injectLayer (hpol : ∀ es v o t, pol es v o t = true)
    (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.injfLayer delay inj pol es t = rho.injectLayer delay inj es t := by
  rw [injfLayer_eq, injectLayer_eq, injfDeliveries_eq_injectDeliveries rho hpol]

/-- Serving everything, the filtered stages are `Run.injectStages`. -/
theorem injfStages_eq_injectStages (hpol : ∀ es v o t, pol es v o t = true) (n : Nat) :
    rho.injfStages delay inj pol n = rho.injectStages delay inj n := by
  induction n with
  | zero => rw [injfStages_zero, injectStages_zero]
  | succ n ih =>
    rw [injfStages_succ, injectStages_succ, ih, injfLayer_eq_injectLayer rho hpol]

/-- **Serving everything, the filtered schedule is** `Run.injectEvents`, with no
assumption on the delays or the injections. -/
theorem injfEvents_eq_injectEvents (hpol : ∀ es v o t, pol es v o t = true) :
    rho.injfEvents delay inj pol = rho.injectEvents delay inj := by
  rw [injfEvents_eq, injectEvents_eq, injfStages_eq_injectStages rho hpol]

/-- Serving everything, the filtered run is `Run.injectRun`. -/
theorem injfRun_eq_injectRun (hpol : ∀ es v o t, pol es v o t = true) :
    rho.injfRun delay inj pol = rho.injectRun delay inj := by
  simp only [injfRun, injectRun, injfEvents_eq_injectEvents rho hpol]

end ServeAll

/-! ### Validity -/

/-- **The schedule is a valid execution** when the selection is admissible and every injected
object is signed only by keys compromised at its delivery time, each selected for its role. -/
theorem injfEvents_valid (h0 : 0 ≤ rho.horizon) (hsel : rho.SelValid)
    (hdelay : ∀ e, 0 ≤ delay e)
    (hfaulty : ∀ t v o, o ∈ inj t v → ∀ d, Obj.Contains o d → ∀ u, rho.signerOf d = some u →
      u ∈ rho.faultyAt t)
    (hcred : ∀ t v o, o ∈ inj t v → ∀ d, Obj.Contains o d → ∀ k r, d.auth = .signed k r →
      k ∈ rho.sel r) :
    (rho.injfRun delay inj pol).ExecutionValid := by
  let r := rho.injfRun delay inj pol
  have hev : r.events = rho.injfEvents delay inj pol := withEvents_events _ _
  have hF : r.faultyAt = rho.faultyAt := withEvents_faultyAt _ _
  have hSel : r.sel = rho.sel := withEvents_sel _ _
  have hH : r.horizon = rho.horizon := withEvents_horizon _ _
  have hsig : r.signerOf = rho.signerOf := by
    funext d; simp only [signerOf, r, injfRun, withEvents_key]
  rw [← hF, ← hsig] at hfaulty
  rw [← hSel] at hcred
  have hs : r.events.Pairwise Event.keyLe := hev ▸ rho.injfStages_sorted delay inj pol _
  have event_layer {e : Event V (protoOf F E).Object} (he : e ∈ r.events) :
      ∃ k, e ∈ rho.injfLayer delay inj pol (rho.injfStages delay inj pol k) (k : Time) := by
    rw [hev] at he
    obtain ⟨k, _, hk⟩ := (rho.mem_injfStages delay inj pol _ e).mp he
    exact ⟨k, hk⟩
  have hunf : r.Unforgeable := by
    intro i w o t hi o' hc u hh hu
    let G : Nat → Prop := fun k => ∃ e, r.events[k]? = some e ∧ e.time ≤ t
    let P : Nat → (protoOf F E).Object → Prop := fun k d => ∀ u, r.signerOf d = some u →
      u ∉ r.faultyAt t → ∃ j t', j < k ∧ r.SendsAt u j t' ∧ d ∈ r.releasesAt j
    have hcl := r.closed_of_sources P G
      (fun hle h u hs hu => let ⟨j, t', hj, h1, h2⟩ := h u hs hu; ⟨j, t', by omega, h1, h2⟩)
      (by
        rintro k j ek ej ⟨e, he, het⟩ hjk hk hj -
        rw [he] at hk; cases hk
        exact ⟨ej, hj, (r.time_le_of_lt hs hjk he hj).trans het⟩)
      (by
        rintro k - o ho u hsg _
        cases he : r.events[k]? with
        | none => simp [releasesAt, he] at ho
        | some e =>
          cases e with
          | tick v τ =>
            simp only [releasesAt, he] at ho
            rcases r.tick_signerOf _ v τ ho with hn | hv
            · rw [hn] at hsg; cases hsg
            · obtain rfl := Option.some.inj (hsg.symm.trans hv)
              exact ⟨k, τ, Nat.lt_succ_self k, Or.inl he, by simpa only [releasesAt, he] using ho⟩
          | deliver v p τ =>
            simp only [releasesAt, he] at ho
            rcases r.deliver_signerOf _ v p τ ho with hn | hv
            · rw [hn] at hsg; cases hsg
            · obtain rfl := Option.some.inj (hsg.symm.trans hv)
              exact ⟨k, τ, Nat.lt_succ_self k, Or.inr ⟨p, he⟩,
                by simpa only [releasesAt, he] using ho⟩
          | restart v τ => simp [releasesAt, he] at ho)
      (by
        rintro k w' p τ ⟨e, he, het⟩ hk
        rw [hk] at he; cases he
        rcases rho.injfEvents_source delay inj pol hk with hp | ⟨j, hj, ej, hje, hjt, hjr⟩
        · left
          intro d hd u hsg hu'
          exact absurd (r.faultyAt_mono het (hfaulty τ w' p hp d hd u hsg)) hu'
        · exact Or.inr ⟨j, hj, ⟨ej, hje, ((le_add_of_nonneg_right (hdelay ej)).trans hjt).trans
            het⟩, hjr⟩)
    rcases rho.injfEvents_source delay inj pol hi with hp | ⟨j, hj, ej, hje, hjt, hjr⟩
    · exact absurd (hfaulty t w o hp o' hc u hh) hu
    · obtain ⟨k, t', hk, hks, hko⟩ :=
        hcl j ⟨ej, hje, (le_add_of_nonneg_right (hdelay ej)).trans hjt⟩
        o hjr o' hc u hh hu
      exact ⟨k, t', by omega, hks, hko⟩
  have hcr : r.Credentials := by
    intro i w o t hi o' hc k ρ ha
    have hcl := r.closed_of_sources (fun _ d => ∀ k ρ, d.auth = .signed k ρ → k ∈ r.sel ρ)
      (fun _ => True) (fun _ h => h) (fun _ _ _ _ _ => trivial)
      (by
        rintro k - o ho k' ρ' ha'
        cases he : r.events[k]? with
        | none => simp [releasesAt, he] at ho
        | some e =>
          cases e with
          | tick v τ =>
            simp only [releasesAt, he] at ho
            exact r.tick_selected _ v τ ho ha'
          | deliver v p τ =>
            simp only [releasesAt, he] at ho
            exact r.deliver_selected _ v p τ ho ha'
          | restart v τ => simp [releasesAt, he] at ho)
      (by
        rintro k w' p τ - hk
        rcases rho.injfEvents_source delay inj pol hk with hp | ⟨j, hj, -, -, -, hjr⟩
        · exact Or.inl fun d hd k' ρ' ha' => hcred τ w' p hp d hd k' ρ' ha'
        · exact Or.inr ⟨j, hj, trivial, hjr⟩)
    rcases rho.injfEvents_source delay inj pol hi with hp | ⟨j, -, -, -, -, hjr⟩
    · exact hcred t w o hp o' hc k ρ ha
    · exact hcl j trivial o hjr o' hc k ρ ha
  have hsel' : r.SelValid := by
    change (protoOf F E).SelAdmits r.sel
    rw [hSel]; exact hsel
  refine ⟨hH ▸ h0, hs, hev ▸ rho.injfStages_nodup delay inj pol _, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hunf,
    hsel', hcr⟩
  · exact fun e he => hH ▸ rho.injfEvents_in_horizon delay inj pol h0 (hev ▸ he)
  · intro e he
    obtain ⟨k, hk⟩ := event_layer he
    rw [hF]
    exact rho.injfLayer_honest delay inj pol _ _ hk
  · intro v t ht0 hh hv ha
    rw [hF] at hv
    rw [hH] at hh
    rw [hev]
    apply rho.injfEvents_layer delay inj pol t ht0 hh
    rw [mem_injfLayer]
    exact Or.inr (Or.inl ⟨v, hv, ha, rfl⟩)
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    rcases (rho.mem_injfLayer delay inj pol _ _ _).mp hk with
      ⟨w, _, _, _, h⟩ | ⟨w, _, ha, h⟩ | ⟨w, _, _, o, _, h⟩
    · cases h
    · cases h; exact ha
    · cases h
  · intro v o t he
    obtain ⟨k, hk⟩ := event_layer he
    rcases (rho.mem_injfLayer delay inj pol _ _ _).mp hk with
      ⟨w, _, _, _, h⟩ | ⟨w, _, _, h⟩ | ⟨w, _, ha, p, _, h⟩
    · cases h
    · cases h
    · cases h; exact ha
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    rcases (rho.mem_injfLayer delay inj pol _ _ _).mp hk with
      ⟨w, _, hp, ha, h⟩ | ⟨w, _, _, h⟩ | ⟨w, _, _, o, _, h⟩
    · cases h; exact ⟨hp, ha⟩
    · cases h
    · cases h
  · intro v t hp hh hv hw
    rw [hF] at hv
    rw [hH] at hh
    rw [hev]
    apply rho.injfEvents_layer delay inj pol t hp.le hh
    rw [mem_injfLayer]
    exact Or.inl ⟨v, hv, hp, hw, rfl⟩

/-! ### The network -/

/-- **The schedule is synchronous** (`PSync 0`) when the delivery filter serves everything, every
delay is below both network bounds, both bounds exceed one, and transactions are relayed
eagerly. -/
theorem injfEvents_psync (h0 : 0 ≤ rho.horizon) (hΔ : 1 < E.ΔAC) (hΔF : 1 < E.ΔFG)
    (hpol : ∀ es v o t, pol es v o t = true)
    (hdelay : ∀ e, 0 ≤ delay e ∧ delay e < E.ΔAC ∧ delay e < E.ΔFG)
    (htx : (rho.injfRun delay inj pol).EagerTxDelivery) :
    (rho.injfRun delay inj pol).log.PSync (rho.injfRun delay inj pol).point 0 := by
  let r := rho.injfRun delay inj pol
  have hF : r.faultyAt = rho.faultyAt := withEvents_faultyAt _ _
  have hH : r.horizon = rho.horizon := withEvents_horizon _ _
  rw [show (rho.injfRun delay inj pol).point = rho.point from withEvents_point _ _]
  have htx' := eagerTxDelivery_iff.mp htx
  rw [hF, show r.submit = rho.submit from congrArg EnvPoint.submit (withEvents_point _ _)] at htx'
  have hheld : ∀ (Δ : Time), 1 < Δ → (∀ e, delay e < Δ) → ∀ v m τ, r.releases v m τ →
      ∀ w a, τ ≤ a → max a 0 + Δ - 1 ≤ rho.horizon → w ∉ rho.faultyAt (max a 0 + Δ - 1) →
        E.awake w (max a 0 + Δ - 1) = true → r.log.Held rho.point w m (max a 0 + Δ - 1) := by
    intro Δ h1 hdΔ v m τ hr w a hτa hdh hw haw
    obtain ⟨j, hs, hm⟩ := hr
    obtain ⟨e, he, -, het⟩ := hs.exists_event
    have hτ0 : 0 ≤ τ := het ▸ (rho.injfEvents_in_horizon delay inj pol h0
      (by rw [← withEvents_events rho (rho.injfEvents delay inj pol)]
          exact List.mem_of_getElem? he)).1
    have hmax : max a 0 = a := max_eq_left (hτ0.trans hτa)
    rw [hmax] at hdh hw haw ⊢
    apply CommLog.held_of_recv
    refine rho.injfEvents_receives delay inj pol h0 he hm ?_ ?_ hdh hw haw (hpol _ _ _ _)
    · have := hdΔ e; rw [het]; dsimp only [Time] at *; omega
    · left; rw [het]; dsimp only [Time] at *; omega
  constructor
  · intro v m t hs _ _ w a hta _ hdh hw haw
    exact hheld E.ΔAC hΔ (fun e => (hdelay e).2.1) v m t hs w a hta hdh hw
      (haw _ (by have := le_max_left a 0; dsimp only [Time] at *; omega) le_rfl)
  · intro v m t hs _ _ w a hta _ hdh hw haw
    exact hheld E.ΔFG hΔF (fun e => (hdelay e).2.2) v m t hs w a hta hdh hw
      (haw _ (by have := le_max_left a 0; dsimp only [Time] at *; omega) le_rfl)
  · intro u x τ hτ hu hua hx w a hτa _ _ hw haw
    have hle : τ ≤ max a 0 + E.ΔAC - 1 := by
      have := le_max_left a 0; dsimp only [Time] at *; omega
    exact ⟨_, hτ.trans hle, le_rfl, htx' u x τ hτ hu hua hx w _ hle hw
      (haw _ (by have := le_max_left a 0; dsimp only [Time] at *; omega) le_rfl)⟩

end Run

end Consensus.Model

end
