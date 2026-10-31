module
public import ConsensusLean.Lemmas.Model.Canonical.Delivery
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! Structural closure facts, prefix invariance of execution, and the finite
pool of released objects used by the canonical scheduler. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

/-- A closure consists exactly of the descendants of its roots. -/
theorem mem_closure_iff {pub : Public} {Out : Type} {P : Protocol pub Out} (l : List P.Object)
    (o : P.Object) : o ∈ closure l ↔ ∃ r ∈ l, Obj.Contains r o := by
  simp only [closure, List.mem_flatMap, Obj.Contains]

namespace Run
variable (rho : Run F E)

/-- Changing the event list leaves the engine transition unchanged. -/
def withEvents (es : List (Event V (protoOf F E).Object)) : Run F E :=
  { rho with events := es }

omit [DecidableEq V] in
theorem withEvents_eq (es : List (Event V (protoOf F E).Object)) :
    rho.withEvents es = { rho with events := es } := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_events (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).events = es := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_honest (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).honest = rho.honest := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_horizon (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).horizon = rho.horizon := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_point (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).point = rho.point := by rfl

@[simp] theorem withEvents_step (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).step = rho.step := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_tick (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).tick = rho.tick := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_deliver (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).deliver = rho.deliver := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_key (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).key = rho.key := by rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_sel (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).sel = rho.sel := by rfl

theorem stateBefore_append (xs ys : List (Event V (protoOf F E).Object))
    {i : Nat} (hi : i ≤ xs.length) :
    (rho.withEvents (xs ++ ys)).stateBefore i = (rho.withEvents xs).stateBefore i := by
  change (List.take i (xs ++ ys)).foldl rho.step rho.initWorld =
    (List.take i xs).foldl rho.step rho.initWorld
  rw [List.take_append_of_le_length hi]

theorem releasesAt_append (xs ys : List (Event V (protoOf F E).Object))
    {i : Nat} (hi : i < xs.length) :
    (rho.withEvents (xs ++ ys)).releasesAt i = (rho.withEvents xs).releasesAt i := by
  unfold releasesAt
  rw [show (rho.withEvents (xs ++ ys)).events[i]? = (rho.withEvents xs).events[i]? from
    List.getElem?_append_left hi, rho.stateBefore_append xs ys hi.le]
  rfl

omit [DecidableEq V] in
/-- The event of a sending event: its index holds a tick or a delivery of the
node at the time. -/
theorem SendsAt.exists_event {v : V} {i : Nat} {t : Time} (hs : rho.SendsAt v i t) :
    ∃ e, rho.events[i]? = some e ∧ e.node = v ∧ e.time = t := by
  rcases hs with he | ⟨o, he⟩
  · exact ⟨_, he, rfl, rfl⟩
  · exact ⟨_, he, rfl, rfl⟩

omit [DecidableEq V] in
/-- A sending event in a prefix is one in the longer list. -/
theorem sendsAt_append (xs ys : List (Event V (protoOf F E).Object)) {v : V} {i : Nat}
    {t : Time} (hs : (rho.withEvents xs).SendsAt v i t) :
    (rho.withEvents (xs ++ ys)).SendsAt v i t := by
  rcases hs with he | ⟨o, he⟩
  · have hil : i < xs.length := (List.getElem?_eq_some_iff.mp he).1
    exact Or.inl ((List.getElem?_append_left hil).trans he)
  · have hil : i < xs.length := (List.getElem?_eq_some_iff.mp he).1
    exact Or.inr ⟨o, (List.getElem?_append_left hil).trans he⟩

/-- Releases at an index depend only on the prefix through that index. -/
theorem releases_prefix (xs ys : List (Event V (protoOf F E).Object))
    {v : V} {o : (protoOf F E).Object} {t : Time}
    (h : (rho.withEvents xs).releases v o t) :
    (rho.withEvents (xs ++ ys)).releases v o t := by
  obtain ⟨i, hi, ho⟩ := h
  obtain ⟨e, he, -, -⟩ := hi.exists_event
  have hil : i < xs.length := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨i, rho.sendsAt_append xs ys hi, ?_⟩
  rw [rho.releasesAt_append xs ys hil]
  exact ho

/-- Restrict a release to a prefix containing every event of the node at the
release time (so its sending event). Uniqueness of events ensures that both
runs refer to the same index. -/
theorem releases_restrict (xs ys : List (Event V (protoOf F E).Object))
    (hn : (xs ++ ys).Nodup) {v : V} {o : (protoOf F E).Object} {t : Time}
    (hin : ∀ e ∈ xs ++ ys, e.node = v → e.time = t → e ∈ xs)
    (hr : (rho.withEvents (xs ++ ys)).releases v o t) :
    (rho.withEvents xs).releases v o t := by
  obtain ⟨i, hi, ho⟩ := hr
  obtain ⟨e, he, hev, het⟩ := hi.exists_event
  rw [withEvents_events] at he
  have hex : e ∈ xs := hin e (List.mem_of_getElem? he) hev het
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hex
  have hjl : j < xs.length := (List.getElem?_eq_some_iff.mp hj).1
  have hji : j = i := (hn.getElem?_inj (by simp; omega)).mp
    ((List.getElem?_append_left hjl).trans (hj.trans he.symm))
  subst i
  refine ⟨j, ?_, by rwa [rho.releasesAt_append xs ys hjl] at ho⟩
  rcases hi with hi | ⟨p, hi⟩
  · exact Or.inl ((List.getElem?_append_left hjl).symm.trans hi)
  · exact Or.inr ⟨p, (List.getElem?_append_left hjl).symm.trans hi⟩

/-- A first-occurrence pool prefix contains the entire original prefix before
the corresponding first release. -/
theorem firstRelease_prefix {α : Type} [DecidableEq α] (xs : List α)
    (p : Nat) (o : α) (ho : xs.reverse.dedup.reverse[p]? = some o) :
    ∃ i, xs[i]? = some o ∧ xs.take i ⊆ xs.reverse.dedup.reverse.take p := by
  induction xs using List.reverseRecOn with
  | nil => simp at ho
  | append_singleton xs a ih =>
    by_cases ha : a ∈ xs
    · have he : (xs ++ [a]).reverse.dedup.reverse = xs.reverse.dedup.reverse := by
        simp [List.reverse_append, List.dedup_cons_of_mem, ha]
      rw [he] at ho ⊢
      obtain ⟨i, hi, hp⟩ := ih ho
      have hil := (List.getElem?_eq_some_iff.mp hi).1
      exact ⟨i, (List.getElem?_append_left hil).trans hi,
        by simpa only [List.take_append_of_le_length hil.le] using hp⟩
    · have he : (xs ++ [a]).reverse.dedup.reverse = xs.reverse.dedup.reverse ++ [a] := by
        simp [List.reverse_append, List.dedup_cons_of_notMem, ha]
      rw [he] at ho ⊢
      by_cases hp : p < xs.reverse.dedup.reverse.length
      · rw [List.getElem?_append_left hp] at ho
        obtain ⟨i, hi, hsub⟩ := ih ho
        have hil := (List.getElem?_eq_some_iff.mp hi).1
        exact ⟨i, (List.getElem?_append_left hil).trans hi,
          by simpa only [List.take_append_of_le_length hil.le,
            List.take_append_of_le_length hp.le] using hsub⟩
      · have hpl := (List.getElem?_eq_some_iff.mp ho).1
        have heq : p = xs.reverse.dedup.reverse.length := by
          simp only [List.length_append, List.length_singleton] at hpl
          omega
        subst p
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] at ho
        subst o
        refine ⟨xs.length, by simp, ?_⟩
        simp only [List.take_append_length]
        intro b hb
        simpa using hb

/-- The finite pool of objects released in a prefix, retaining first release order. -/
def pool (es : List (Event V (protoOf F E).Object)) : List (protoOf F E).Object :=
  ((List.range es.length).flatMap (rho.withEvents es).releasesAt).reverse.dedup.reverse

theorem pool_eq (es : List (Event V (protoOf F E).Object)) :
    rho.pool es =
      ((List.range es.length).flatMap (rho.withEvents es).releasesAt).reverse.dedup.reverse := by
  rfl

theorem nodup_pool (es : List (Event V (protoOf F E).Object)) : (rho.pool es).Nodup := by
  rw [pool_eq, List.nodup_reverse]
  exact List.nodup_dedup _

theorem mem_pool (es : List (Event V (protoOf F E).Object)) (o : (protoOf F E).Object) :
    o ∈ rho.pool es ↔ ∃ v t, (rho.withEvents es).releases v o t := by
  simp only [pool_eq, List.mem_reverse, List.mem_dedup, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, ho⟩
    have hie : es[i]? = some es[i] := List.getElem?_eq_getElem hi
    generalize he : es[i]? = e at *
    cases e with
    | none => simp [releasesAt, withEvents_eq, he] at ho
    | some e =>
      cases e with
      | tick v t => exact ⟨v, t, i, Or.inl he, ho⟩
      | deliver v p t => exact ⟨v, t, i, Or.inr ⟨p, he⟩, ho⟩
      | restart v t => simp [releasesAt, withEvents_eq, he] at ho
  · rintro ⟨v, t, i, hi, ho⟩
    obtain ⟨e, he, -, -⟩ := hi.exists_event
    exact ⟨i, (List.getElem?_eq_some_iff.mp he).1, ho⟩

end Run
end Consensus.Model
end
