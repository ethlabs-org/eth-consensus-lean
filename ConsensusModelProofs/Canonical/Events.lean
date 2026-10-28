module
public import ConsensusModelProofs.Canonical.Delivery

@[expose] public section

/-! Structural closure facts, prefix invariance of execution, and the finite
pool of released objects used by the canonical scheduler. -/

namespace Consensus.Model

namespace Obj
variable {L : Type} {seats : L → Nat} {Item Body : Type}

theorem partsList_eq (cs : List (Obj L seats Item Body)) :
    parts.partsList cs = cs.flatMap parts := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [parts.partsList, ih]

theorem parts_eq (o : Obj L seats Item Body) : o.parts = o :: o.carried.flatMap parts := by
  cases o
  simp [parts, partsList_eq, carried]

theorem carried_size_lt (o : Obj L seats Item Body) : sizeOf o.carried < sizeOf o := by
  cases o
  simp [carried]

theorem contains_of_mem_parts (o d : Obj L seats Item Body) (h : d ∈ o.parts) : Contains o d := by
  rw [parts_eq, List.mem_cons] at h
  rcases h with rfl | h
  · exact .refl _
  · obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp h
    exact .step hc (contains_of_mem_parts c d hd)
termination_by sizeOf o
decreasing_by exact lt_trans (List.sizeOf_lt_of_mem hc) (carried_size_lt _)

theorem mem_parts_of_contains {o d : Obj L seats Item Body} (h : Contains o d) : d ∈ o.parts := by
  induction h with
  | refl o => rw [parts_eq]; exact List.mem_cons_self
  | step hc _ ih =>
    rw [parts_eq]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, hc, ih⟩)

theorem mem_parts_iff (o d : Obj L seats Item Body) : d ∈ o.parts ↔ Contains o d :=
  ⟨contains_of_mem_parts o d, mem_parts_of_contains⟩

end Obj

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

/-- A closure consists exactly of the descendants of its roots. -/
theorem mem_closure_iff {pub : Public} {P : Protocol pub} (l : List P.Object) (o : P.Object) :
    o ∈ closure l ↔ ∃ r ∈ l, Obj.Contains r o := by
  simp only [closure, List.mem_flatMap, Obj.mem_parts_iff]

namespace Run
variable (rho : Run F E)

/-- Changing the event list leaves the engine transition unchanged. -/
def withEvents (es : List (Event V (protoOf F E).Object)) : Run F E :=
  { rho with events := es }

@[simp] theorem withEvents_step (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).step = rho.step := rfl

@[simp] theorem withEvents_tick (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).tick = rho.tick := rfl

omit [DecidableEq V] in
@[simp] theorem withEvents_holder (es : List (Event V (protoOf F E).Object)) :
    (rho.withEvents es).holder = rho.holder := rfl

theorem stateBefore_append (xs ys : List (Event V (protoOf F E).Object))
    {i : Nat} (hi : i ≤ xs.length) :
    (rho.withEvents (xs ++ ys)).stateBefore i = (rho.withEvents xs).stateBefore i := by
  change (List.take i (xs ++ ys)).foldl rho.step (initWorld F E) =
    (List.take i xs).foldl rho.step (initWorld F E)
  rw [List.take_append_of_le_length hi]

theorem releasesAt_append (xs ys : List (Event V (protoOf F E).Object))
    {i : Nat} (hi : i < xs.length) :
    (rho.withEvents (xs ++ ys)).releasesAt i = (rho.withEvents xs).releasesAt i := by
  unfold releasesAt
  rw [show (rho.withEvents (xs ++ ys)).events[i]? = (rho.withEvents xs).events[i]? from
    List.getElem?_append_left hi, rho.stateBefore_append xs ys hi.le]
  rfl

/-- Releases at an index depend only on the prefix through that index. -/
theorem releases_prefix (xs ys : List (Event V (protoOf F E).Object))
    {v : V} {o : (protoOf F E).Object} {t : Time}
    (h : (rho.withEvents xs).releases v o t) :
    (rho.withEvents (xs ++ ys)).releases v o t := by
  obtain ⟨i, hi, ho⟩ := h
  have hil : i < xs.length := List.getElem?_eq_some_iff.mp hi |>.1
  refine ⟨i, ?_, ?_⟩
  · exact (List.getElem?_append_left hil).trans hi
  · rw [rho.releasesAt_append xs ys hil]
    exact ho

/-- Restrict a release to a prefix containing its tick. Uniqueness of events
ensures that both runs refer to the same tick index. -/
theorem releases_restrict (xs ys : List (Event V (protoOf F E).Object))
    (hn : (xs ++ ys).Nodup) {v : V} {o : (protoOf F E).Object} {t : Time}
    (ht : Event.tick v t ∈ xs)
    (hr : (rho.withEvents (xs ++ ys)).releases v o t) :
    (rho.withEvents xs).releases v o t := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ht
  have hjl : j < xs.length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨i, hi, ho⟩ := hr
  have hji : j = i := (hn.getElem?_inj (by simp; omega)).mp
    ((List.getElem?_append_left hjl).trans (hj.trans hi.symm))
  subst i
  exact ⟨j, hj, by rwa [rho.releasesAt_append xs ys hjl] at ho⟩

/-- The finite pool of objects released in a prefix, deduplicated. -/
def pool (es : List (Event V (protoOf F E).Object)) : List (protoOf F E).Object :=
  ((List.range es.length).flatMap (rho.withEvents es).releasesAt).dedup

theorem mem_pool (es : List (Event V (protoOf F E).Object)) (o : (protoOf F E).Object) :
    o ∈ rho.pool es ↔ ∃ v t, (rho.withEvents es).releases v o t := by
  simp only [pool, List.mem_dedup, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, ho⟩
    have hie : es[i]? = some es[i] := List.getElem?_eq_getElem hi
    generalize he : es[i]? = e at *
    cases e with
    | none => simp [releasesAt, withEvents, he] at ho
    | some e =>
      cases e with
      | tick v t => exact ⟨v, t, i, he, ho⟩
      | deliver v p t => simp [releasesAt, withEvents, he] at ho
      | restart v t => simp [releasesAt, withEvents, he] at ho
  · rintro ⟨v, t, i, hi, ho⟩
    exact ⟨i, (List.getElem?_eq_some_iff.mp hi).1, ho⟩

end Run
end Consensus.Model
end
