module
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! # The objects a delivery processes

`AsChainShape.process` folds `processOne` over `delivered`, the objects `visit` reaches: the
received object, then, unless processing it refuses a block (`Refuses`: a canonical block of a
future slot or one the FG refuses), recursively what it carries. This file relates that list to
the received object's closure `parts`.

* `process_eq_visit`: the fold reaches `visit`'s state; `mem_delivered`: a delivered object is in
  the closure; `mem_delivered_self`, `visit_head`: the received object comes first.
* What is delivered: an object of the closure that carries something (`mem_delivered_of_carried`,
  with its whole visit as an infix, `delivered_infix_of_carried`), or whose parent is no canonical
  block (`mem_delivered_of_parent`); only payload objects of a refused block, which carry nothing,
  are skipped.
* `carried_subset_delivered`: what an object carries is delivered when processing it, from the
  state the objects before it leave, refuses no block.
-/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open SA (SAParams ReplayOrder)

variable {binding : VoteBinding}

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- A received object standing for a block event decodes to that block. -/
theorem decodeBlock_of_canonEvent {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {B : Blk sp}
    (h : canonEvent sp ro hs o = some (.block B)) : decodeBlock sp hs o = some B := by
  cases hb : decodeBlock sp hs o with
  | some B' => simp only [canonEvent, hb, Option.some.injEq, Event.block.injEq] at h; rw [h]
  | none =>
    cases hv : decodeVoteObj sp o <;> cases ha : decodeAttObj sp o <;>
      simp [canonEvent, hb, hv, ha] at h

/-- The objects a decoded block carries are its payload objects, which carry nothing. -/
theorem carried_of_decodeBlock {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {B : Blk sp} (h : decodeBlock sp hs o = some B) : ∀ c ∈ o.carried, c.carried = [] := by
  unfold decodeBlock at h
  split at h
  · split at h
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨⟨-, rfl, -, -⟩, -⟩ := h
      intro c hc
      simp only [Model.Obj.carried, payloadObjs, List.mem_append, List.mem_map] at hc
      rcases hc with ⟨a, -, rfl⟩ | ⟨v, -, rfl⟩ <;> rfl
    · cases h
  · cases h

/-- An object with a data body is no canonical block. -/
theorem canonEvent_data_ne_block {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {au b cs} (ho : o = .mk au (.data b) cs) (B : Blk sp) :
    canonEvent sp ro hs o ≠ some (.block B) := by
  intro h
  have h' := decodeBlock_of_canonEvent h
  subst ho
  unfold decodeBlock at h'
  split at h' <;> simp_all

section Visit

variable (hs : List (Header Info × Nat))

/-- `visit` of a canonical-form object: the object, then nothing when it refuses a block, else
`visitList` of what it carries from the state after it. -/
theorem visit_cases (st : State sp ro binding) (o : Wire sp.n binding) :
    (Refuses hs st o ∧ visit hs st o = ([o], processOne hs st o)) ∨
      (¬ Refuses hs st o ∧ visit hs st o =
        (o :: (visitList hs (processOne hs st o) o.carried).1,
          (visitList hs (processOne hs st o) o.carried).2)) := by
  obtain ⟨a, m, cs⟩ := o
  rw [visit]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- `visitList` of a list: `visit` of its head, then `visitList` of the rest. -/
theorem visitList_cons (st : State sp ro binding) (c : Wire sp.n binding)
    (cs : List (Wire sp.n binding)) :
    visitList hs st (c :: cs) =
      ((visit hs st c).1 ++ (visitList hs (visit hs st c).2 cs).1,
        (visitList hs (visit hs st c).2 cs).2) := by
  rw [visitList]

mutual
/-- Processing the visited objects in order reaches the visit's state, and every visited
object belongs to the received object's recursive closure. -/
private theorem visit_spec : ∀ (st : State sp ro binding) (o : Wire sp.n binding),
    (visit hs st o).1.foldl (processOne hs) st = (visit hs st o).2 ∧ (visit hs st o).1 ⊆ o.parts
  | st, .mk a m cs => by
    rcases visit_cases hs st (.mk a m cs) with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact ⟨rfl, fun y hy => by rw [List.mem_singleton.mp hy]; exact Model.Obj.Contains.refl _⟩
    · obtain ⟨h1, h2⟩ := visitList_spec (processOne hs st (.mk a m cs)) cs
      refine ⟨h1, List.cons_subset.mpr ⟨Model.Obj.Contains.refl _, fun x hx => ?_⟩⟩
      rw [Model.Obj.parts_eq]
      exact List.mem_cons_of_mem _
        (by simpa [Model.Obj.partsList_eq, Model.Obj.carried] using h2 hx)
/-- `visit_spec` of a list. -/
private theorem visitList_spec : ∀ (st : State sp ro binding) (cs : List (Wire sp.n binding)),
    (visitList hs st cs).1.foldl (processOne hs) st = (visitList hs st cs).2 ∧
      (visitList hs st cs).1 ⊆ Model.Obj.parts.partsList cs
  | st, [] => by simp [visitList, Model.Obj.parts.partsList]
  | st, c :: cs => by
    rw [visitList_cons]
    obtain ⟨h1, h2⟩ := visit_spec st c
    obtain ⟨h3, h4⟩ := visitList_spec (visit hs st c).2 cs
    refine ⟨by rw [List.foldl_append, h1, h3], fun y hy => ?_⟩
    simp only [Model.Obj.parts.partsList, List.mem_append]
    rcases List.mem_append.mp hy with hy | hy
    exacts [Or.inl (h2 hy), Or.inr (h4 hy)]
end

/-- A delivery processes its delivered objects in order (`process`): their fold reaches
`visit`'s state. -/
theorem process_eq_visit (st : State sp ro binding) (o : Wire sp.n binding) :
    process st o hs = (visit hs st o).2 :=
  (visit_spec hs st o).1

/-- A delivered object belongs to the received object's recursive closure. -/
theorem mem_delivered {st : State sp ro binding} {o x : Wire sp.n binding}
    (h : x ∈ delivered hs st o) : x ∈ o.parts :=
  (visit_spec hs st o).2 h

/-- The received object itself is delivered. -/
theorem mem_delivered_self (st : State sp ro binding) (o : Wire sp.n binding) :
    o ∈ delivered hs st o := by
  unfold delivered
  rcases visit_cases hs st o with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact List.mem_cons_self

/-- The parent `y` of `x` inside a received object is no canonical block (whose carried objects
are skipped when it is refused). -/
private def ParentNotBlock (o x : Wire sp.n binding) : Prop :=
  ∃ y ∈ o.parts, x ∈ y.carried ∧ ∀ B, canonEvent sp ro hs y ≠ some (.block B)

/-- `visit` of an object whose processing refuses no block: the object, then `visitList` of what
it carries. -/
theorem visit_of_not_refuses {st : State sp ro binding} {o : Wire sp.n binding}
    (h : ¬ Refuses hs st o) :
    (visit hs st o).1 = o :: (visitList hs (processOne hs st o) o.carried).1 := by
  rcases visit_cases hs st o with ⟨hr, -⟩ | ⟨-, hv⟩
  · exact absurd hr h
  · rw [hv]

/-- Processing an object that is no canonical block refuses no block. -/
theorem not_refuses_of_canonEvent {st : State sp ro binding} {o : Wire sp.n binding}
    (h : ∀ B, canonEvent sp ro hs o ≠ some (.block B)) : ¬ Refuses hs st o :=
  fun ⟨B, hB, _⟩ => h B hB

/-- `visit` of an object that carries nothing is that object. -/
theorem visit_of_carried_eq_nil (st : State sp ro binding) {o : Wire sp.n binding}
    (h : o.carried = []) : (visit hs st o).1 = [o] := by
  rcases visit_cases hs st o with ⟨-, hv⟩ | ⟨-, hv⟩ <;> rw [hv]
  rw [h, visitList]

/-- A delivery of an object that carries nothing processes that object alone. -/
theorem delivered_of_carried_eq_nil (st : State sp ro binding) {o : Wire sp.n binding}
    (h : o.carried = []) : delivered hs st o = [o] :=
  visit_of_carried_eq_nil hs st h

/-- `visit` starts with the visited object. -/
theorem visit_head (st : State sp ro binding) (o : Wire sp.n binding) :
    ∃ rest, (visit hs st o).1 = o :: rest := by
  rcases visit_cases hs st o with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact ⟨_, rfl⟩

mutual
/-- An object of the received object's closure is visited, with everything it leads to, when it is
the received object, when it carries something (no payload object of a block does), or when it has
a parent that is no canonical block. -/
private theorem infix_visit : ∀ (st : State sp ro binding) (o x : Wire sp.n binding),
    x ∈ o.parts → (x = o ∨ x.carried ≠ [] ∨ ParentNotBlock (ro := ro) hs o x) →
      ∃ (pre post : List (Wire sp.n binding)) (st' : State sp ro binding),
        (visit hs st o).1 = pre ++ (visit hs st' x).1 ++ post
  | st, .mk a m cs, x, hx, hc => by
    by_cases hxo : x = .mk a m cs
    · subst hxo
      exact ⟨[], [], st, by simp⟩
    rw [Model.Obj.parts_eq, List.mem_cons] at hx
    obtain ⟨c, hcm, hxc⟩ := List.mem_flatMap.mp (hx.resolve_left hxo)
    rcases visit_cases hs st (.mk a m cs) with ⟨hr, -⟩ | ⟨-, h⟩
    · -- a refused block carries only payload objects, which carry nothing
      exfalso
      obtain ⟨B, hB, -⟩ := hr
      have hpay : ∀ c ∈ (Model.Obj.mk a m cs).carried, c.parts = [c] ∧ c.carried = [] := by
        intro c hc
        have hc0 := carried_of_decodeBlock (decodeBlock_of_canonEvent hB) c hc
        refine ⟨?_, hc0⟩
        rw [Model.Obj.parts_eq, hc0]
        rfl
      obtain ⟨hcp, hc0⟩ := hpay c hcm
      rw [hcp, List.mem_singleton] at hxc
      subst hxc
      rcases hc with hc | hc | ⟨y, hy, hxy, hnb⟩
      · exact hxo hc
      · exact hc hc0
      · rw [Model.Obj.parts_eq, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hnb B hB
        · obtain ⟨d, hdm, hyd⟩ := List.mem_flatMap.mp hy
          obtain ⟨hdp, hd0⟩ := hpay d hdm
          rw [hdp, List.mem_singleton] at hyd
          subst hyd
          simp [hd0] at hxy
    rw [h]
    obtain ⟨pre, post, st', he⟩ := infix_visitList (processOne hs st (.mk a m cs)) cs x (by
      rcases hc with hc | hc | ⟨y, hy, hxy, hnb⟩
      · exact absurd hc hxo
      · exact ⟨c, hcm, hxc, Or.inr (Or.inl hc)⟩
      · rw [Model.Obj.parts_eq, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact ⟨x, hxy, Model.Obj.Contains.refl _, Or.inl rfl⟩
        · obtain ⟨d, hdm, hyd⟩ := List.mem_flatMap.mp hy
          exact ⟨d, hdm, Model.Obj.Contains.trans hyd (.step hxy (.refl _)),
            Or.inr (Or.inr ⟨y, hyd, hxy, hnb⟩)⟩)
    exact ⟨.mk a m cs :: pre, post, st', congrArg (List.cons _) he⟩
/-- `infix_visit` of a list: an object of the closure of one of its objects. -/
private theorem infix_visitList : ∀ (st : State sp ro binding) (cs : List (Wire sp.n binding))
    (x : Wire sp.n binding),
    (∃ c ∈ cs, x ∈ c.parts ∧ (x = c ∨ x.carried ≠ [] ∨ ParentNotBlock (ro := ro) hs c x)) →
      ∃ (pre post : List (Wire sp.n binding)) (st' : State sp ro binding),
        (visitList hs st cs).1 = pre ++ (visit hs st' x).1 ++ post
  | _, [], _, ⟨_, hc, _⟩ => absurd hc List.not_mem_nil
  | st, c :: cs, x, ⟨c', hc', hx, h⟩ => by
    rw [visitList_cons]
    rcases List.mem_cons.mp hc' with hcc | hc'
    · rw [hcc] at hx h
      obtain ⟨pre, post, st', he⟩ := infix_visit st c x hx h
      exact ⟨pre, post ++ (visitList hs (visit hs st c).2 cs).1, st', by
        simp only [he, List.append_assoc]⟩
    · obtain ⟨pre, post, st', he⟩ := infix_visitList (visit hs st c).2 cs x ⟨c', hc', hx, h⟩
      exact ⟨(visit hs st c).1 ++ pre, post, st', by simp only [he, List.append_assoc]⟩
end

private theorem mem_visit (st : State sp ro binding) (o x : Wire sp.n binding)
    (hx : x ∈ o.parts) (hc : x = o ∨ x.carried ≠ [] ∨ ParentNotBlock (ro := ro) hs o x) :
    x ∈ (visit hs st o).1 := by
  obtain ⟨pre, post, st', he⟩ := infix_visit hs st o x hx hc
  obtain ⟨rest, hr⟩ := visit_head hs st' x
  rw [he, hr]
  simp

/-- A delivered object that carries something, contained in the received object, is processed
together with everything it leads to: the delivery's objects are those of a `visit` of it,
surrounded by others. -/
theorem delivered_infix_of_carried {st : State sp ro binding} {o x : Wire sp.n binding}
    (hx : Model.Obj.Contains o x) (hc : x.carried ≠ []) :
    ∃ (pre post : List (Wire sp.n binding)) (st' : State sp ro binding),
        delivered hs st o = pre ++ (visit hs st' x).1 ++ post :=
  infix_visit hs st o x hx (Or.inr (Or.inl hc))

/-- An object of the received object's closure that carries something is delivered: only the
payload objects of a refused block are skipped, and they carry nothing. -/
theorem mem_delivered_of_carried {st : State sp ro binding} {o x : Wire sp.n binding}
    (hx : Model.Obj.Contains o x) (hc : x.carried ≠ []) : x ∈ delivered hs st o :=
  mem_visit hs st o x hx (Or.inr (Or.inl hc))

/-- An object carried, inside the received object, by an object that is no canonical block is
delivered. -/
theorem mem_delivered_of_parent {st : State sp ro binding} {o y x : Wire sp.n binding}
    (hy : Model.Obj.Contains o y) (hx : x ∈ y.carried)
    (hb : ∀ B, canonEvent sp ro hs y ≠ some (.block B)) : x ∈ delivered hs st o :=
  mem_visit hs st o x (hy.trans (.step hx (.refl _))) (Or.inr (Or.inr ⟨y, hy, hx, hb⟩))

/-- In a list of processed objects, every object whose processing (from the state the objects
before it leave) refuses no block is followed by the objects it carries. -/
private def Closed (st : State sp ro binding) (l : List (Wire sp.n binding)) : Prop :=
  ∀ pre x post, l = pre ++ x :: post → ¬ Refuses hs (pre.foldl (processOne hs) st) x →
    x.carried ⊆ l

private theorem closed_append {st : State sp ro binding} {l₁ l₂ : List (Wire sp.n binding)}
    (h₁ : Closed hs st l₁) (h₂ : Closed hs (l₁.foldl (processOne hs) st) l₂) :
    Closed hs st (l₁ ++ l₂) := by
  intro pre x post he hr
  rcases List.append_eq_append_iff.mp he with ⟨a', rfl, h2⟩ | ⟨c', h1, h2⟩
  · rw [List.foldl_append] at hr
    exact List.Subset.trans (h₂ a' x post h2 hr) (List.subset_append_right _ _)
  · cases c' with
    | nil =>
      rw [List.append_nil] at h1
      subst h1
      exact List.Subset.trans (h₂ [] x post (by simpa using h2.symm) hr)
        (List.subset_append_right _ _)
    | cons y c'' =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact List.Subset.trans (h₁ pre x c'' h1 hr) (List.subset_append_left _ _)

private theorem mem_visit_self (st : State sp ro binding) (o : Wire sp.n binding) :
    o ∈ (visit hs st o).1 :=
  mem_delivered_self hs st o

mutual
private theorem visit_closed : ∀ (st : State sp ro binding) (o : Wire sp.n binding),
    Closed hs st (visit hs st o).1
  | st, .mk a m cs => by
    rcases visit_cases hs st (.mk a m cs) with ⟨hr, h⟩ | ⟨-, h⟩ <;> rw [h]
    · intro pre x post he hx
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        exact absurd hr hx
      | cons p pre => simp at he
    · obtain ⟨hcl, hsub⟩ := visitList_closed (processOne hs st (.mk a m cs)) cs
      intro pre x post he hx
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        exact List.Subset.trans hsub (List.subset_cons_self _ _)
      | cons p pre =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        exact List.Subset.trans (hcl pre x post he hx) (List.subset_cons_self _ _)
private theorem visitList_closed : ∀ (st : State sp ro binding) (cs : List (Wire sp.n binding)),
    Closed hs st (visitList hs st cs).1 ∧ cs ⊆ (visitList hs st cs).1
  | st, [] => ⟨fun pre x post he => by simp [visitList] at he, by simp⟩
  | st, c :: cs => by
    rw [visitList_cons]
    obtain ⟨hcl, hsub⟩ := visitList_closed (visit hs st c).2 cs
    refine ⟨closed_append hs (visit_closed st c) (by rw [(visit_spec hs st c).1]; exact hcl), ?_⟩
    exact List.cons_subset.mpr ⟨List.mem_append_left _ (mem_visit_self hs st c),
      List.Subset.trans hsub (List.subset_append_right _ _)⟩
end

/-- The objects carried by a delivered object are delivered too, unless processing it, from the
state the objects delivered before it leave, refuses a block. -/
theorem carried_subset_delivered {st : State sp ro binding} {o x : Wire sp.n binding}
    {pre post : List (Wire sp.n binding)} (he : delivered hs st o = pre ++ x :: post)
    (hr : ¬ Refuses hs (pre.foldl (processOne hs) st) x) :
    x.carried ⊆ delivered hs st o :=
  visit_closed hs st o pre x post he hr

end Visit

end

end Consensus.Goldilocks.Simulation

end
