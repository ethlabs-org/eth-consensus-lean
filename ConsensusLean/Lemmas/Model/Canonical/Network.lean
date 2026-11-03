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

/-- Earlier entries of one recipient's delivery batch are already held at
the current entry, even when all entries have the same timestamp. -/
theorem delivery_batch_held (pre post : List (Event V (protoOf F E).Object))
    (os : List (protoOf F E).Object) (v : V) (t : Time) (p : Nat) :
    os.take p ⊆
      ((rho.withEvents (pre ++ os.map (fun o => .deliver v o t) ++ post)).stateBefore
        (pre.length + p) v).seen := by
  intro a ha
  obtain ⟨j, he⟩ := List.mem_iff_getElem?.mp ha
  have hjp : j < p := lt_of_lt_of_le (List.getElem?_eq_some_iff.mp he).1
    (List.length_take_le _ _)
  have hja : os[j]? = some a := by
    simpa only [List.getElem?_take, hjp, ↓reduceIte] using he
  have hjl := (List.getElem?_eq_some_iff.mp hja).1
  let r := rho.withEvents (pre ++ os.map (fun o => .deliver v o t) ++ post)
  have hev : r.events[pre.length + j]? = some (.deliver v a t) := by
    dsimp only [r]
    rw [withEvents_events]
    rw [List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp [List.getElem?_map, hja]
  apply r.seen_mono (show pre.length + j + 1 ≤ pre.length + p by omega) v
  rw [r.stateBefore_succ hev]
  simp only [step, Function.update_self, deliver_seen]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

/-- The eager scheduler delivers only dependency-ready objects. The pool's
first-release order and the release guard suffice; no protocol law is assumed. -/
theorem canonical_delivery_ready (g : Time) :
    ∀ i v o t, (rho.canonicalEvents g)[i]? = some (.deliver v o t) →
      (protoOf F E).dependencies.ready
        (closure ((rho.withEvents (rho.canonicalEvents g)).stateBefore i v).seen) o = true := by
  classical
  intro i v o t hi
  have hm := List.mem_of_getElem? hi
  rw [canonicalEvents_eq] at hm
  obtain ⟨k, hk, he⟩ := (rho.mem_stages g _ _).mp hm
  have ht : t = (k : Time) := rho.layer_time g _ _ he
  subst t
  have hd : g ≤ (k : Time) ∧ v ∈ rho.honest ∧ E.awake v (k : Time) = true ∧
      o ∈ rho.pool (rho.front (rho.stages g k) (k : Time)) := by
    simp only [layer_eq, List.mem_append, mem_wakeEvents, mem_tickEvents,
      mem_deliveryEvents] at he
    rcases he with (⟨w, _, _, _, h⟩ | ⟨w, _, _, h⟩) | ⟨hg, w, hw, ha, a, hp, h⟩
    · cases h
    · cases h
    · cases h; exact ⟨hg, hw, ha, hp⟩
  let front := rho.front (rho.stages g k) (k : Time)
  let os := rho.pool front
  let vs := (rho.honest.filter (fun w => E.awake w (k : Time) = true)).toList
  have hv : v ∈ vs := by simp [vs, hd.2.1, hd.2.2.1]
  obtain ⟨before, after, hvs⟩ := List.mem_iff_append.mp hv
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hd.2.2.2
  obtain ⟨tail, htail⟩ := rho.stages_prefix g (show k + 1 ≤ rho.horizon.toNat + 1 by omega)
  let pre := front ++ before.flatMap (fun w => os.map (fun a => .deliver w a (k : Time)))
  let post := after.flatMap (fun w => os.map (fun a => .deliver w a (k : Time))) ++ tail
  have hfull : rho.canonicalEvents g =
      pre ++ os.map (fun a => .deliver v a (k : Time)) ++ post := by
    rw [canonicalEvents_eq, htail, stages_succ, layer_eq]
    simp only [deliveryEvents_eq, hd.1, ↓reduceIte]
    change _ ++ (_ ++ _ ++ vs.flatMap _) ++ tail = _
    rw [hvs]
    simp [pre, post, front, front_eq, os, List.flatMap_append, List.append_assoc]
  have hp' : os[p]? = some o := hp
  have hpl := (List.getElem?_eq_some_iff.mp hp').1
  have hev : (rho.canonicalEvents g)[pre.length + p]? = some (.deliver v o (k : Time)) := by
    rw [hfull, List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp [List.getElem?_map, hp']
  have hn : (rho.canonicalEvents g).Nodup := by
    rw [canonicalEvents_eq]; exact rho.stages_nodup g _
  have hi' : i = pre.length + p :=
    (hn.getElem?_inj (List.getElem?_eq_some_iff.mp hi).1).mp
      (hi.trans hev.symm)
  obtain ⟨rest, hrest⟩ := rho.front_prefix g hk
  have hc : (rho.withEvents front).Causal := rho.causal_prefix front rest (by
    rw [← hrest, ← canonicalEvents_eq]; exact rho.canonical_causal g)
  have hr := (rho.withEvents front).pool_ready hc p o
    (by simpa only [os, pool_eq, withEvents_events, withEvents_eq] using hp')
  have hr' : (protoOf F E).dependencies.ready (closure (os.take p)) o = true := by
    simpa only [os, pool_eq, withEvents_events, withEvents_eq] using hr
  apply (protoOf F E).dependencies.mono _ _ _ ?_ hr'
  intro a ha
  obtain ⟨r, hm, hh⟩ := (mem_closure_iff _ a).mp ha
  apply (mem_closure_iff _ a).mpr
  refine ⟨r, ?_, hh⟩
  rw [hi', hfull]
  exact rho.delivery_batch_held pre post os v (k : Time) p hm

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
