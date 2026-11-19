module
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! # The objects a delivery processes

`AsChainShape.process` folds `processOne` over `delivered`, the objects `visit` reaches: the
received object, then, unless processing it refuses a block (`Refuses`: a block-shaped object
that fails the wire checks, or a canonical block of a future slot or one the FG refuses),
recursively what it carries. This file relates that list to the received object's closure `parts`.

* `process_eq_visit`: the fold reaches `visit`'s state; `mem_delivered`: a delivered object is in
  the closure; `mem_delivered_self`, `visit_head`: the received object comes first.
* When processing refuses: never for an object with a data body (`not_refuses_of_data`); for a
  canonical block exactly when `on_block` does not accept it (`refuses_iff_of_canonEvent`).
* `carried_subset_delivered` (`_self` for the received object): what an object carries is
  delivered when processing it, from the state the objects before it leave, refuses no block.
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

/-- `visit` of an object whose processing refuses no block: the object, then `visitList` of what
it carries. -/
theorem visit_of_not_refuses {st : State sp ro binding} {o : Wire sp.n binding}
    (h : ¬ Refuses hs st o) :
    (visit hs st o).1 = o :: (visitList hs (processOne hs st o) o.carried).1 := by
  rcases visit_cases hs st o with ⟨hr, -⟩ | ⟨-, hv⟩
  · exact absurd hr h
  · rw [hv]

/-- Processing an object with a data body (a vote, an attestation or a wrapper) refuses no
block. -/
theorem not_refuses_of_data {st : State sp ro binding} {o : Wire sp.n binding} {au b cs}
    (ho : o = .mk au (.data b) cs) : ¬ Refuses hs st o := by
  rintro ⟨h, -⟩
  subst ho
  exact h

/-- Processing a canonical block refuses it exactly when `on_block` does not accept it: it is of
a future slot or the FG refuses it. -/
theorem refuses_iff_of_canonEvent {st : State sp ro binding} {o : Wire sp.n binding} {B : Blk sp}
    (h : canonEvent sp ro hs o = some (.block B)) :
    Refuses hs st o ↔ sp.toParams.slotOf st.now < B.slot ∨ st.node.fg.onBlock B = none := by
  have hshape : BlockShaped o := by
    have hd := decodeBlock_of_canonEvent h
    unfold decodeBlock at hd
    split at hd
    · trivial
    · cases hd
  constructor
  · exact fun hr => hr.2 B h
  · intro hB
    refine ⟨hshape, fun B' h' => ?_⟩
    rw [h, Option.some.injEq, Node.Event.block.injEq] at h'
    exact h' ▸ hB

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
    exact List.cons_subset.mpr ⟨List.mem_append_left _ (mem_delivered_self hs st c),
      List.Subset.trans hsub (List.subset_append_right _ _)⟩
end

/-- The objects carried by a delivered object are delivered too, unless processing it, from the
state the objects delivered before it leave, refuses a block. -/
theorem carried_subset_delivered {st : State sp ro binding} {o x : Wire sp.n binding}
    {pre post : List (Wire sp.n binding)} (he : delivered hs st o = pre ++ x :: post)
    (hr : ¬ Refuses hs (pre.foldl (processOne hs) st) x) :
    x.carried ⊆ delivered hs st o :=
  visit_closed hs st o pre x post he hr

/-- The objects the received object carries are delivered unless processing it refuses a block. -/
theorem carried_subset_delivered_self {st : State sp ro binding} {o : Wire sp.n binding}
    (hr : ¬ Refuses hs st o) : o.carried ⊆ delivered hs st o := by
  obtain ⟨rest, h⟩ := visit_head hs st o
  exact carried_subset_delivered hs (pre := []) (post := rest) h hr

end Visit

end

end Consensus.Goldilocks.Simulation

end
