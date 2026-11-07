module
public import ConsensusLean.Lemmas.Model.Canonical.Construction

public section

/-! # The canonical schedule with delayed batches and injected objects (L1)

A variant of the canonical schedule (`Canonical/Schedule`) for runs with an adversarial network
inside the synchrony bound and with forged deliveries. At every integer time through the horizon:
wake restarts, then ticks, then, for every awake honest recipient `v`, the deliveries of the
injected objects `inj t v` followed by the objects released so far by the events `e` whose
batch is due, `e.time + delay e ≤ t` (each recipient's batch deduplicated). With `delay = 0` and
no injection this is the eager canonical network from time `0`.

* `injectEvents_source`: every delivery is an injection or the release of an earlier event whose
  batch is due.
* `closed_of_sources`: a predicate on objects that every injection and every released root of the
  events of a "good" class satisfy, and that only good events feed, holds of everything those
  events release (and, `seen_closed_of_sources`, of everything their nodes have seen). This is the
  object-indexed provenance the proofs about such runs read.
* `injectEvents_valid`: the schedule is a valid execution when every injected object is signed only
  by keys compromised at its delivery time and only by selected keys.
* `injectEvents_psync`: with every delay below both network bounds the log is synchronous
  (`PSync 0`). -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run

variable (rho : Run F E)

/-! ### Closure through good events (any run) -/

section Closure

variable (P : Nat → (protoOf F E).Object → Prop) (G : Nat → Prop)

/-- What a node has seen at cut `c` is closed when every earlier event of the node is good and
the good events before `c` release only closed objects. -/
private theorem seen_closed_aux
    (hmono : ∀ {i i' : Nat} {d : (protoOf F E).Object}, i ≤ i' → P i d → P i' d)
    (hdel : ∀ i w o t, G i → rho.events[i]? = some (.deliver w o t) →
      (∀ d, Obj.Contains o d → P i d) ∨ ∃ j < i, G j ∧ o ∈ rho.releasesAt j)
    {c : Nat} (ih : ∀ k < c, G k → ∀ o ∈ rho.releasesAt k, ∀ d, Obj.Contains o d → P (k + 1) d)
    {v : V} (hgood : ∀ k < c, ∀ e, rho.events[k]? = some e → e.node = v → G k) :
    ∀ o ∈ (rho.stateBefore c v).seen, ∀ d, Obj.Contains o d → P c d := by
  intro o ho d hd
  obtain ⟨k, hk, ⟨t, hs, hr⟩ | ⟨t, he⟩⟩ := rho.seen_source ho
  · obtain ⟨e, he, hn, -⟩ := hs.exists_event
    exact hmono (by omega) (ih k hk (hgood k hk e he hn) o hr d hd)
  · rcases hdel k v o t (hgood k hk _ he rfl) he with h | ⟨j, hj, hG, hr⟩
    · exact hmono hk.le (h d hd)
    · exact hmono (by omega) (ih j (by omega) hG o hr d hd)

/-- **Closure through good events.** If an index-monotone predicate `P` holds of every root
released at a good event (`hroot`), and every delivery at a good event is closed or the release
of an earlier good event (`hdel`), and the earlier events of a good event's node are good
(`hnode`), then everything a good event releases is closed. -/
theorem closed_of_sources
    (hmono : ∀ {i i' : Nat} {d : (protoOf F E).Object}, i ≤ i' → P i d → P i' d)
    (hnode : ∀ {i j : Nat} {ei ej : Event V (protoOf F E).Object}, G i → j < i →
      rho.events[i]? = some ei → rho.events[j]? = some ej → ej.node = ei.node → G j)
    (hroot : ∀ i, G i → ∀ o ∈ rho.releasesAt i, P (i + 1) o)
    (hdel : ∀ i w o t, G i → rho.events[i]? = some (.deliver w o t) →
      (∀ d, Obj.Contains o d → P i d) ∨ ∃ j < i, G j ∧ o ∈ rho.releasesAt j) :
    ∀ i, G i → ∀ o ∈ rho.releasesAt i, ∀ d, Obj.Contains o d → P (i + 1) d := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hG o ho
    cases he : rho.events[i]? with
    | none => simp [releasesAt, he] at ho
    | some e =>
      have hs := rho.seen_closed_aux P G hmono hdel ih (v := e.node)
        (fun k hk e' he' hn => hnode hG hk he he' hn)
      have hr : ∀ o ∈ rho.releasesAt i, P (i + 1) o := hroot i hG
      cases e with
      | tick v t =>
        simp only [releasesAt, he] at ho hr
        obtain ⟨cs, -, h2, -⟩ := rho.tick_flat (rho.stateBefore i v) v t
        rw [h2] at ho hr
        exact (releaseAll_preserves rho.hash _ (P (i + 1)) _ _
          (fun o ho d hd => hmono (Nat.le_succ i) (hs o ho d hd)) hr).2 o ho
      | deliver v p t =>
        simp only [releasesAt, he] at ho hr
        obtain ⟨cs, -, h2, -⟩ := rho.deliver_flat (rho.stateBefore i v) v p t
        rw [h2] at ho hr
        refine (releaseAll_preserves rho.hash _ (P (i + 1)) _ _ ?_ hr).2 o ho
        intro o' ho' d hd
        rcases List.mem_append.mp ho' with ho' | ho'
        · exact hmono (Nat.le_succ i) (hs o' ho' d hd)
        · rw [List.mem_singleton.mp ho'] at hd
          rcases hdel i v p t hG he with h | ⟨j, hj, hGj, hrj⟩
          · exact hmono (Nat.le_succ i) (h d hd)
          · exact hmono (by omega) (ih j hj hGj p hrj d hd)
      | restart v t => simp [releasesAt, he] at ho

/-- The seen form of `closed_of_sources`: at a cut before which every event of `v` is good,
everything `v` has seen is closed. -/
theorem seen_closed_of_sources
    (hmono : ∀ {i i' : Nat} {d : (protoOf F E).Object}, i ≤ i' → P i d → P i' d)
    (hnode : ∀ {i j : Nat} {ei ej : Event V (protoOf F E).Object}, G i → j < i →
      rho.events[i]? = some ei → rho.events[j]? = some ej → ej.node = ei.node → G j)
    (hroot : ∀ i, G i → ∀ o ∈ rho.releasesAt i, P (i + 1) o)
    (hdel : ∀ i w o t, G i → rho.events[i]? = some (.deliver w o t) →
      (∀ d, Obj.Contains o d → P i d) ∨ ∃ j < i, G j ∧ o ∈ rho.releasesAt j)
    {c : Nat} {v : V} (hgood : ∀ k < c, ∀ e, rho.events[k]? = some e → e.node = v → G k) :
    ∀ o ∈ (rho.stateBefore c v).seen, ∀ d, Obj.Contains o d → P c d :=
  rho.seen_closed_aux P G hmono hdel
    (fun k _ hk => rho.closed_of_sources P G hmono hnode hroot hdel k hk) hgood

end Closure

/-! ### The schedule -/

variable (delay : Event V (protoOf F E).Object → Time)
  (inj : Time → V → List (protoOf F E).Object)

/-- The objects released in the prefix `es` by its events whose batch is due at `t`. -/
noncomputable def duePool (es : List (Event V (protoOf F E).Object)) (t : Time) :
    List (protoOf F E).Object := by
  classical
  exact ((List.range es.length).flatMap fun j =>
    if ∃ e, es[j]? = some e ∧ e.time + delay e ≤ t then (rho.withEvents es).releasesAt j
    else []).dedup

theorem mem_duePool (es : List (Event V (protoOf F E).Object)) (t : Time)
    (o : (protoOf F E).Object) :
    o ∈ rho.duePool delay es t ↔ ∃ j e, es[j]? = some e ∧ e.time + delay e ≤ t ∧
      o ∈ (rho.withEvents es).releasesAt j := by
  classical
  unfold duePool
  simp only [List.mem_dedup, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨j, -, ho⟩
    split_ifs at ho with h
    · obtain ⟨e, he, ht⟩ := h
      exact ⟨j, e, he, ht, ho⟩
    · simp at ho
  · rintro ⟨j, e, he, ht, ho⟩
    exact ⟨j, (List.getElem?_eq_some_iff.mp he).1, by
      simp only [show ∃ e', es[j]? = some e' ∧ e'.time + delay e' ≤ t from ⟨e, he, ht⟩,
        ↓reduceIte]
      exact ho⟩

/-- The deliveries at `t` after the prefix `es`: to every awake honest node, the injections of
`t` and the due releases. -/
noncomputable def injectDeliveries (es : List (Event V (protoOf F E).Object)) (t : Time) :
    List (Event V (protoOf F E).Object) := by
  classical
  exact (((Finset.univ \ rho.faultyAt t).filter (fun v => E.awake v t = true)).toList).flatMap
    (fun v => (inj t v ++ rho.duePool delay es t).dedup.map (fun o => .deliver v o t))

theorem mem_injectDeliveries (es : List (Event V (protoOf F E).Object)) (t : Time)
    (e : Event V (protoOf F E).Object) :
    e ∈ rho.injectDeliveries delay inj es t ↔ ∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧
      ∃ o, (o ∈ inj t v ∨ o ∈ rho.duePool delay es t) ∧ e = .deliver v o t := by
  classical
  unfold injectDeliveries
  simp only [List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_univ, true_and, List.mem_dedup, List.mem_append]
  constructor
  · rintro ⟨v, ⟨hv, hw⟩, o, ho, rfl⟩
    exact ⟨v, hv, hw, o, ho, rfl⟩
  · rintro ⟨v, hv, hw, o, ho, rfl⟩
    exact ⟨v, ⟨hv, hw⟩, o, ho, rfl⟩

theorem injectDeliveries_nodup (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.injectDeliveries delay inj es t).Nodup := by
  classical
  unfold injectDeliveries
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
noncomputable def injectLayer (es : List (Event V (protoOf F E).Object)) (t : Time) :
    List (Event V (protoOf F E).Object) :=
  rho.wakeEvents t ++ rho.tickEvents t ++ rho.injectDeliveries delay inj (rho.front es t) t

/-- The first `n` integer times. -/
noncomputable def injectStages : Nat → List (Event V (protoOf F E).Object)
  | 0 => []
  | n + 1 => injectStages n ++ rho.injectLayer delay inj (injectStages n) (n : Time)

/-- The schedule through the inclusive horizon. -/
noncomputable def injectEvents : List (Event V (protoOf F E).Object) :=
  rho.injectStages delay inj (rho.horizon.toNat + 1)

theorem injectLayer_eq (es : List (Event V (protoOf F E).Object)) (t : Time) :
    rho.injectLayer delay inj es t = rho.wakeEvents t ++ rho.tickEvents t ++
      rho.injectDeliveries delay inj (rho.front es t) t := by rfl

theorem injectStages_succ (n : Nat) : rho.injectStages delay inj (n + 1) =
    rho.injectStages delay inj n ++
      rho.injectLayer delay inj (rho.injectStages delay inj n) (n : Time) := by rfl

theorem injectEvents_eq :
    rho.injectEvents delay inj = rho.injectStages delay inj (rho.horizon.toNat + 1) := by rfl

theorem mem_injectLayer (es : List (Event V (protoOf F E).Object)) (t : Time)
    (e : Event V (protoOf F E).Object) : e ∈ rho.injectLayer delay inj es t ↔
      (∃ v, v ∉ rho.faultyAt t ∧ 0 < t ∧ Wakes E v t ∧ e = .restart v t) ∨
      (∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧ e = .tick v t) ∨
      ∃ v, v ∉ rho.faultyAt t ∧ E.awake v t = true ∧
        ∃ o, (o ∈ inj t v ∨ o ∈ rho.duePool delay (rho.front es t) t) ∧ e = .deliver v o t := by
  simp only [injectLayer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
    mem_injectDeliveries, or_assoc]

theorem injectLayer_time (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.injectLayer delay inj es t) :
    e.time = t := by
  rcases (rho.mem_injectLayer delay inj es t e).mp he with
    ⟨v, _, _, _, rfl⟩ | ⟨v, _, _, rfl⟩ | ⟨v, _, _, o, _, rfl⟩ <;> rfl

theorem injectLayer_honest (es : List (Event V (protoOf F E).Object)) (t : Time)
    {e : Event V (protoOf F E).Object} (he : e ∈ rho.injectLayer delay inj es t) :
    e.node ∉ rho.faultyAt e.time := by
  rcases (rho.mem_injectLayer delay inj es t e).mp he with
    ⟨v, hv, _, _, rfl⟩ | ⟨v, hv, _, rfl⟩ | ⟨v, hv, _, o, _, rfl⟩ <;> exact hv

theorem injectLayer_sorted (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.injectLayer delay inj es t).Pairwise Event.keyLe := by
  classical
  have hw : ∀ e ∈ rho.wakeEvents t, e.time = t ∧ e.phase = 0 := by
    intro e he
    obtain ⟨v, _, _, _, rfl⟩ := (rho.mem_wakeEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have ht : ∀ e ∈ rho.tickEvents t, e.time = t ∧ e.phase = 1 := by
    intro e he
    obtain ⟨v, _, _, rfl⟩ := (rho.mem_tickEvents t e).mp he
    exact ⟨rfl, rfl⟩
  have hd : ∀ e ∈ rho.injectDeliveries delay inj (rho.front es t) t,
      e.time = t ∧ e.phase = 2 := by
    intro e he
    obtain ⟨v, _, _, o, _, rfl⟩ := (rho.mem_injectDeliveries delay inj _ t e).mp he
    exact ⟨rfl, rfl⟩
  have block {l : List (Event V (protoOf F E).Object)} {k : Nat}
      (h : ∀ e ∈ l, e.time = t ∧ e.phase = k) : l.Pairwise Event.keyLe := by
    apply List.pairwise_of_forall_mem_list
    intro e he f hf
    exact Or.inr ⟨(h e he).1.trans (h f hf).1.symm, by rw [(h e he).2, (h f hf).2]⟩
  simp only [injectLayer_eq, List.pairwise_append]
  refine ⟨⟨block hw, block ht, ?_⟩, block hd, ?_⟩
  · intro e he f hf
    exact Or.inr ⟨(hw e he).1.trans (ht f hf).1.symm, by rw [(hw e he).2, (ht f hf).2]; decide⟩
  · intro e he f hf
    have hf' := hd f hf
    rcases List.mem_append.mp he with he | he
    · exact Or.inr ⟨(hw e he).1.trans hf'.1.symm, by rw [(hw e he).2, hf'.2]; decide⟩
    · exact Or.inr ⟨(ht e he).1.trans hf'.1.symm, by rw [(ht e he).2, hf'.2]; decide⟩

theorem injectLayer_nodup (es : List (Event V (protoOf F E).Object)) (t : Time) :
    (rho.injectLayer delay inj es t).Nodup := by
  classical
  have hwt : (rho.wakeEvents t ++ rho.tickEvents t).Nodup := by
    have h := rho.layer_nodup 0 es t
    rw [layer_eq] at h
    exact (List.nodup_append.mp h).1
  rw [injectLayer_eq, List.nodup_append]
  refine ⟨hwt, rho.injectDeliveries_nodup delay inj _ t, ?_⟩
  · intro e he f hf hef
    subst f
    obtain ⟨v, _, _, o, _, rfl⟩ := (rho.mem_injectDeliveries delay inj _ t e).mp hf
    simp at he

theorem injectStages_time (n : Nat) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injectStages delay inj n) : 0 ≤ e.time ∧ e.time < (n : Time) := by
  induction n with
  | zero => simp [injectStages] at he
  | succ n ih =>
    rw [injectStages_succ] at he
    rcases List.mem_append.mp he with he | he
    · have := ih he
      exact ⟨this.1, lt_trans this.2 (by exact_mod_cast Nat.lt_succ_self n)⟩
    · rw [rho.injectLayer_time delay inj _ _ he]
      exact ⟨Int.natCast_nonneg n, by exact_mod_cast Nat.lt_succ_self n⟩

theorem injectStages_sorted (n : Nat) :
    (rho.injectStages delay inj n).Pairwise Event.keyLe := by
  induction n with
  | zero => simp [injectStages]
  | succ n ih =>
    rw [injectStages_succ, List.pairwise_append]
    refine ⟨ih, rho.injectLayer_sorted delay inj _ _, ?_⟩
    intro e he f hf
    exact Or.inl (by
      rw [rho.injectLayer_time delay inj _ _ hf]
      exact (rho.injectStages_time delay inj n he).2)

theorem injectStages_nodup (n : Nat) : (rho.injectStages delay inj n).Nodup := by
  induction n with
  | zero => simp [injectStages]
  | succ n ih =>
    rw [injectStages_succ, List.nodup_append]
    refine ⟨ih, rho.injectLayer_nodup delay inj _ _, ?_⟩
    intro e he f hf hef
    subst f
    have := (rho.injectStages_time delay inj n he).2
    rw [rho.injectLayer_time delay inj _ _ hf] at this
    exact lt_irrefl _ this

theorem mem_injectStages (n : Nat) (e : Event V (protoOf F E).Object) :
    e ∈ rho.injectStages delay inj n ↔
      ∃ k < n, e ∈ rho.injectLayer delay inj (rho.injectStages delay inj k) (k : Time) := by
  induction n with
  | zero => simp [injectStages]
  | succ n ih =>
    simp only [injectStages_succ, List.mem_append, ih]
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

theorem injectStages_prefix {m n : Nat} (hmn : m ≤ n) :
    ∃ tail, rho.injectStages delay inj n = rho.injectStages delay inj m ++ tail := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    exact ⟨[], (List.append_nil _).symm⟩
  | succ n ih =>
    by_cases hm : m ≤ n
    · obtain ⟨tail, ht⟩ := ih hm
      refine ⟨tail ++ rho.injectLayer delay inj (rho.injectStages delay inj n) (n : Time), ?_⟩
      rw [injectStages_succ, ht, List.append_assoc]
    · have : m = n + 1 := by omega
      subst m
      exact ⟨[], (List.append_nil _).symm⟩

theorem injectFront_prefix {k n : Nat} (hk : k < n) :
    ∃ tail, rho.injectStages delay inj n =
      rho.front (rho.injectStages delay inj k) (k : Time) ++ tail := by
  obtain ⟨tail, ht⟩ := rho.injectStages_prefix delay inj (show k + 1 ≤ n by omega)
  refine ⟨rho.injectDeliveries delay inj (rho.front (rho.injectStages delay inj k) (k : Time))
    (k : Time) ++ tail, ?_⟩
  rw [ht, injectStages_succ, injectLayer_eq, front_eq]
  simp only [List.append_assoc]

/-- A scheduled event whose time is below `a` lies in the stages before `a`. -/
theorem mem_injectStages_of_time_lt {n : Nat} {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injectStages delay inj n) {a : Time} (ha : e.time < a) :
    e ∈ rho.injectStages delay inj a.toNat := by
  obtain ⟨k, _, hk⟩ := (rho.mem_injectStages delay inj n e).mp he
  have htk : e.time = (k : Time) := rho.injectLayer_time delay inj _ _ hk
  refine (rho.mem_injectStages delay inj _ e).mpr ⟨k, ?_, hk⟩
  rw [htk] at ha
  have h := (Int.toNat_lt_toNat (lt_of_le_of_lt (Int.natCast_nonneg k) ha)).mpr ha
  simpa using h

theorem injectEvents_in_horizon (h0 : 0 ≤ rho.horizon) {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injectEvents delay inj) : 0 ≤ e.time ∧ e.time ≤ rho.horizon := by
  have h := rho.injectStages_time delay inj _ he
  have hn : (rho.horizon.toNat : Int) = rho.horizon := Int.toNat_of_nonneg h0
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) ≤ rho.horizon
  change 0 ≤ (e.time : Int) ∧ (e.time : Int) < ((rho.horizon.toNat + 1 : Nat) : Int) at h
  push_cast at h
  dsimp [Time] at *
  omega

theorem injectEvents_layer (t : Time) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon)
    {e : Event V (protoOf F E).Object}
    (he : e ∈ rho.injectLayer delay inj (rho.injectStages delay inj t.toNat) t) :
    e ∈ rho.injectEvents delay inj := by
  apply (rho.mem_injectStages delay inj _ e).mpr
  refine ⟨t.toNat, ?_, ?_⟩
  · have := Int.toNat_le_toNat hh
    omega
  · simpa only [Int.toNat_of_nonneg h0] using he

/-- The scheduled run. -/
noncomputable abbrev injectRun : Run F E := rho.withEvents (rho.injectEvents delay inj)

/-- **Every delivery is an injection or a due release of an earlier event.** -/
theorem injectEvents_source {i : Nat} {w : V} {o : (protoOf F E).Object} {t : Time}
    (hi : (rho.injectRun delay inj).events[i]? = some (.deliver w o t)) :
    o ∈ inj t w ∨ ∃ j < i, ∃ e, (rho.injectRun delay inj).events[j]? = some e ∧
      e.time + delay e ≤ t ∧ o ∈ (rho.injectRun delay inj).releasesAt j := by
  rw [withEvents_events] at hi
  have hm := List.mem_of_getElem? hi
  rw [injectEvents_eq] at hm
  obtain ⟨k, hk, he⟩ := (rho.mem_injectStages delay inj _ _).mp hm
  have htk : t = (k : Time) := rho.injectLayer_time delay inj _ _ he
  subst t
  have hp : o ∈ inj (k : Time) w ∨
      o ∈ rho.duePool delay (rho.front (rho.injectStages delay inj k) (k : Time)) (k : Time) := by
    rcases (rho.mem_injectLayer delay inj _ _ _).mp he with
      ⟨v, _, _, _, h⟩ | ⟨v, _, _, h⟩ | ⟨v, _, _, p, hp, h⟩
    · cases h
    · cases h
    · cases h; exact hp
  rcases hp with hp | hp
  · exact Or.inl hp
  right
  obtain ⟨tail, htail⟩ := rho.injectFront_prefix delay inj hk
  obtain ⟨j, e, hje, hjt, ho⟩ := (rho.mem_duePool delay _ _ o).mp hp
  have hjl : j < (rho.front (rho.injectStages delay inj k) (k : Time)).length :=
    (List.getElem?_eq_some_iff.mp hje).1
  have hni :
      ¬ Event.deliver w o (k : Time) ∈ rho.front (rho.injectStages delay inj k) (k : Time) := by
    intro h
    simp only [front_eq, List.mem_append] at h
    rcases h with (h | h) | h
    · exact lt_irrefl _ (rho.injectStages_time delay inj k h).2
    · simp at h
    · simp at h
  have hile : (rho.front (rho.injectStages delay inj k) (k : Time)).length ≤ i := by
    by_contra h
    have hil : i < (rho.front (rho.injectStages delay inj k) (k : Time)).length := by omega
    apply hni
    apply List.mem_of_getElem?
    rw [show (rho.front (rho.injectStages delay inj k) (k : Time))[i]? =
      (rho.injectEvents delay inj)[i]? by rw [(rho.injectEvents_eq delay inj).trans htail,
        List.getElem?_append_left hil]]
    exact hi
  refine ⟨j, lt_of_lt_of_le hjl hile, e, ?_, hjt, ?_⟩
  · rw [withEvents_events, (rho.injectEvents_eq delay inj).trans htail,
      List.getElem?_append_left hjl]
    exact hje
  · change o ∈ (rho.withEvents (rho.injectEvents delay inj)).releasesAt j
    rw [(rho.injectEvents_eq delay inj).trans htail, rho.releasesAt_append _ _ hjl]
    exact ho

/-- A release whose batch is due at `t` and whose event lies in the front of `t` (strictly
before `t`, or a tick of `t`) is received by every awake honest node at `t`. -/
theorem injectEvents_receives (h0 : 0 ≤ rho.horizon) {j : Nat}
    {e : Event V (protoOf F E).Object}
    (hj : (rho.injectRun delay inj).events[j]? = some e) {o : (protoOf F E).Object}
    (ho : o ∈ (rho.injectRun delay inj).releasesAt j) {t : Time} (hdue : e.time + delay e ≤ t)
    (hfront : e.time < t ∨ ∃ v, e = .tick v t) (hth : t ≤ rho.horizon) {w : V}
    (hw : w ∉ rho.faultyAt t) (haw : E.awake w t = true) :
    (rho.injectRun delay inj).receives w o t := by
  rw [withEvents_events] at hj
  have hem := List.mem_of_getElem? hj
  have ht0 : 0 ≤ t := by
    have := (rho.injectEvents_in_horizon delay inj h0 hem).1
    rcases hfront with h | ⟨v, rfl⟩
    · exact this.trans h.le
    · exact this
  have han : t.toNat < rho.horizon.toNat + 1 := by
    have := Int.toNat_le_toNat hth
    omega
  obtain ⟨tail, htail⟩ := rho.injectFront_prefix delay inj han
  let fr := rho.front (rho.injectStages delay inj t.toNat) (t.toNat : Time)
  have hfr : e ∈ fr := by
    simp only [fr, front_eq, List.mem_append]
    rcases hfront with h | ⟨v, rfl⟩
    · exact Or.inl (Or.inl (rho.mem_injectStages_of_time_lt delay inj hem h))
    · right
      rw [Int.toNat_of_nonneg ht0]
      have hv := (rho.injectStages_time delay inj _ hem)
      have hvalid := rho.injectLayer_honest delay inj
      obtain ⟨k, _, hk⟩ := (rho.mem_injectStages delay inj _ _).mp hem
      have htk := rho.injectLayer_time delay inj _ _ hk
      rcases (rho.mem_injectLayer delay inj _ _ _).mp hk with
        ⟨u, _, _, _, h⟩ | ⟨u, hu, hua, h⟩ | ⟨u, _, _, p, _, h⟩
      · cases h
      · cases h
        exact (rho.mem_tickEvents _ _).mpr ⟨v, by simpa [htk] using hu, by simpa [htk] using hua,
          by simp⟩
      · cases h
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hfr
  have hj'l : j' < fr.length := (List.getElem?_eq_some_iff.mp hj').1
  have hfull : rho.injectEvents delay inj = fr ++ tail :=
    (rho.injectEvents_eq delay inj).trans htail
  have hjj : j' = j := by
    have hn : (rho.injectEvents delay inj).Nodup := rho.injectStages_nodup delay inj _
    exact (hn.getElem?_inj (by rw [hfull, List.length_append]; omega)).mp
      ((show (rho.injectEvents delay inj)[j']? = fr[j']? by
        rw [hfull, List.getElem?_append_left hj'l]).trans (hj'.trans hj.symm))
  subst j'
  have hpool : o ∈ rho.duePool delay fr (t.toNat : Time) := by
    rw [mem_duePool]
    refine ⟨j, e, hj', by rwa [Int.toNat_of_nonneg ht0], ?_⟩
    have := rho.releasesAt_append fr tail hj'l
    rw [← hfull] at this
    rw [← this]
    exact ho
  have hdel : Event.deliver w o t ∈ rho.injectEvents delay inj := by
    apply rho.injectEvents_layer delay inj t ht0 hth
    rw [mem_injectLayer]
    refine Or.inr (Or.inr ⟨w, hw, haw, o, Or.inr ?_, rfl⟩)
    simpa only [fr, Int.toNat_of_nonneg ht0] using hpool
  rw [← withEvents_events rho (rho.injectEvents delay inj)] at hdel
  exact List.mem_iff_getElem?.mp hdel

/-! ### Validity -/

omit [DecidableEq V] in
/-- Earlier events of a sorted list are at earlier times. -/
theorem time_le_of_lt (hs : rho.events.Pairwise Event.keyLe) {i j : Nat}
    {ei ej : Event V (protoOf F E).Object} (hji : j < i) (hi : rho.events[i]? = some ei)
    (hj : rho.events[j]? = some ej) : ej.time ≤ ei.time := by
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  have hk := List.pairwise_iff_getElem.mp hs j i (by omega) hil hji
  rw [List.getElem?_eq_getElem hil] at hi
  rw [List.getElem?_eq_getElem (by omega)] at hj
  cases hi; cases hj
  rcases hk with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-- **The schedule is a valid execution** when the selection is admissible and every injected
object is signed only by keys compromised at its delivery time, each selected for its role. -/
theorem injectEvents_valid (h0 : 0 ≤ rho.horizon) (hsel : rho.SelValid)
    (hdelay : ∀ e, 0 ≤ delay e)
    (hfaulty : ∀ t v o, o ∈ inj t v → ∀ d, Obj.Contains o d → ∀ u, rho.signerOf d = some u →
      u ∈ rho.faultyAt t)
    (hcred : ∀ t v o, o ∈ inj t v → ∀ d, Obj.Contains o d → ∀ k r, d.auth = .signed k r →
      k ∈ rho.sel r) :
    (rho.injectRun delay inj).ExecutionValid := by
  let r := rho.injectRun delay inj
  have hev : r.events = rho.injectEvents delay inj := withEvents_events _ _
  have hF : r.faultyAt = rho.faultyAt := withEvents_faultyAt _ _
  have hSel : r.sel = rho.sel := withEvents_sel _ _
  have hH : r.horizon = rho.horizon := withEvents_horizon _ _
  have hsig : r.signerOf = rho.signerOf := by
    funext d; simp only [signerOf, r, injectRun, withEvents_key]
  rw [← hF, ← hsig] at hfaulty
  rw [← hSel] at hcred
  have hs : r.events.Pairwise Event.keyLe := hev ▸ rho.injectStages_sorted delay inj _
  have event_layer {e : Event V (protoOf F E).Object} (he : e ∈ r.events) :
      ∃ k, e ∈ rho.injectLayer delay inj (rho.injectStages delay inj k) (k : Time) := by
    rw [hev] at he
    obtain ⟨k, _, hk⟩ := (rho.mem_injectStages delay inj _ e).mp he
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
        rcases rho.injectEvents_source delay inj hk with hp | ⟨j, hj, ej, hje, hjt, hjr⟩
        · left
          intro d hd u hsg hu'
          exact absurd (r.faultyAt_mono het (hfaulty τ w' p hp d hd u hsg)) hu'
        · exact Or.inr ⟨j, hj, ⟨ej, hje, ((le_add_of_nonneg_right (hdelay ej)).trans hjt).trans
            het⟩, hjr⟩)
    rcases rho.injectEvents_source delay inj hi with hp | ⟨j, hj, ej, hje, hjt, hjr⟩
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
        rcases rho.injectEvents_source delay inj hk with hp | ⟨j, hj, -, -, -, hjr⟩
        · exact Or.inl fun d hd k' ρ' ha' => hcred τ w' p hp d hd k' ρ' ha'
        · exact Or.inr ⟨j, hj, trivial, hjr⟩)
    rcases rho.injectEvents_source delay inj hi with hp | ⟨j, -, -, -, -, hjr⟩
    · exact hcred t w o hp o' hc k ρ ha
    · exact hcl j trivial o hjr o' hc k ρ ha
  have hsel' : r.SelValid := by
    change (protoOf F E).SelAdmits r.sel
    rw [hSel]; exact hsel
  refine ⟨hH ▸ h0, hs, hev ▸ rho.injectStages_nodup delay inj _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hunf,
    hsel', hcr⟩
  · exact fun e he => hH ▸ rho.injectEvents_in_horizon delay inj h0 (hev ▸ he)
  · intro e he
    obtain ⟨k, hk⟩ := event_layer he
    rw [hF]
    exact rho.injectLayer_honest delay inj _ _ hk
  · intro v t ht0 hh hv ha
    rw [hF] at hv
    rw [hH] at hh
    rw [hev]
    apply rho.injectEvents_layer delay inj t ht0 hh
    rw [mem_injectLayer]
    exact Or.inr (Or.inl ⟨v, hv, ha, rfl⟩)
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    rcases (rho.mem_injectLayer delay inj _ _ _).mp hk with
      ⟨w, _, _, _, h⟩ | ⟨w, _, ha, h⟩ | ⟨w, _, _, o, _, h⟩
    · cases h
    · cases h; exact ha
    · cases h
  · intro v o t he
    obtain ⟨k, hk⟩ := event_layer he
    rcases (rho.mem_injectLayer delay inj _ _ _).mp hk with
      ⟨w, _, _, _, h⟩ | ⟨w, _, _, h⟩ | ⟨w, _, ha, p, _, h⟩
    · cases h
    · cases h
    · cases h; exact ha
  · intro v t he
    obtain ⟨k, hk⟩ := event_layer he
    rcases (rho.mem_injectLayer delay inj _ _ _).mp hk with
      ⟨w, _, hp, ha, h⟩ | ⟨w, _, _, h⟩ | ⟨w, _, _, o, _, h⟩
    · cases h; exact ⟨hp, ha⟩
    · cases h
    · cases h
  · intro v t hp hh hv hw
    rw [hF] at hv
    rw [hH] at hh
    rw [hev]
    apply rho.injectEvents_layer delay inj t hp.le hh
    rw [mem_injectLayer]
    exact Or.inl ⟨v, hv, hp, hw, rfl⟩

/-! ### The network -/

/-- **The schedule is synchronous** (`PSync 0`) when every delay is below both network bounds,
both bounds exceed one, and transactions are relayed eagerly. -/
theorem injectEvents_psync (h0 : 0 ≤ rho.horizon) (hΔ : 1 < E.ΔAC) (hΔF : 1 < E.ΔFG)
    (hdelay : ∀ e, 0 ≤ delay e ∧ delay e < E.ΔAC ∧ delay e < E.ΔFG)
    (htx : (rho.injectRun delay inj).EagerTxDelivery) :
    (rho.injectRun delay inj).log.PSync (rho.injectRun delay inj).point 0 := by
  let r := rho.injectRun delay inj
  have hF : r.faultyAt = rho.faultyAt := withEvents_faultyAt _ _
  have hH : r.horizon = rho.horizon := withEvents_horizon _ _
  rw [show (rho.injectRun delay inj).point = rho.point from withEvents_point _ _]
  have htx' := eagerTxDelivery_iff.mp htx
  rw [hF, show r.submit = rho.submit from congrArg EnvPoint.submit (withEvents_point _ _)] at htx'
  have hheld : ∀ (Δ : Time), 1 < Δ → (∀ e, delay e < Δ) → ∀ v m τ, r.releases v m τ →
      ∀ w a, τ ≤ a → max a 0 + Δ - 1 ≤ rho.horizon → w ∉ rho.faultyAt (max a 0 + Δ - 1) →
        E.awake w (max a 0 + Δ - 1) = true → r.log.Held rho.point w m (max a 0 + Δ - 1) := by
    intro Δ h1 hdΔ v m τ hr w a hτa hdh hw haw
    obtain ⟨j, hs, hm⟩ := hr
    obtain ⟨e, he, -, het⟩ := hs.exists_event
    have hτ0 : 0 ≤ τ := het ▸ (rho.injectEvents_in_horizon delay inj h0
      (by rw [← withEvents_events rho (rho.injectEvents delay inj)]
          exact List.mem_of_getElem? he)).1
    have hmax : max a 0 = a := max_eq_left (hτ0.trans hτa)
    rw [hmax] at hdh hw haw ⊢
    apply CommLog.held_of_recv
    refine rho.injectEvents_receives delay inj h0 he hm ?_ ?_ hdh hw haw
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
