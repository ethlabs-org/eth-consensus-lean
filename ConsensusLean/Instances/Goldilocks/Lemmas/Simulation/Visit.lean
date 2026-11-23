module
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin

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
open AC (ACParams ReplayOrder)

variable {binding : VoteBinding}

section

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- A received object standing for a block event decodes to that block. -/
theorem decodeBlock_of_canonEvent {hs : List (Header Info × Nat)} {o : Wire sp.n binding}
    {io : VoteAuth sp.n binding} {B : Blk sp}
    (h : canonEvent sp ro io hs o = some (.block B)) : decodeBlock sp hs o = some B := by
  cases hb : decodeBlock sp hs o with
  | some B' => simp only [canonEvent_eq, hb, Option.some.injEq, Event.block.injEq] at h; rw [h]
  | none =>
    cases hv : decodeVoteObj sp io o <;> cases ha : decodeAttObj sp o <;>
      simp [canonEvent_eq, hb, hv, ha] at h

section Visit

variable (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))

/-- `visit` of a canonical-form object: the object, then nothing when it refuses a block, else
`visitList` of what it carries from the state after it. -/
theorem visit_cases (st : State sp ro binding) (o : Wire sp.n binding) :
    (Refuses io hs st o ∧ visit io hs st o = ([o], processOne io hs st o)) ∨
      (¬ Refuses io hs st o ∧ visit io hs st o =
        (o :: (visitList io hs (processOne io hs st o) o.carried).1,
          (visitList io hs (processOne io hs st o) o.carried).2)) := by
  obtain ⟨a, m, cs⟩ := o
  rw [visit_eq]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

/-- `visitList` of a list: `visit` of its head, then `visitList` of the rest. -/
theorem visitList_cons (st : State sp ro binding) (c : Wire sp.n binding)
    (cs : List (Wire sp.n binding)) :
    visitList io hs st (c :: cs) =
      ((visit io hs st c).1 ++ (visitList io hs (visit io hs st c).2 cs).1,
        (visitList io hs (visit io hs st c).2 cs).2) := by
  rw [visitList_cons_eq]

/-- A delivered object belongs to the received object's recursive closure. -/
theorem mem_delivered {st : State sp ro binding} {o x : Wire sp.n binding}
    (h : x ∈ delivered io hs st o) : x ∈ o.parts :=
  NodeAsChainShape.CanonicalTrace.contains_of_mem_delivered
    (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs h

/-- The received object itself is delivered. -/
theorem mem_delivered_self (st : State sp ro binding) (o : Wire sp.n binding) :
    o ∈ delivered io hs st o :=
  NodeAsChainShape.CanonicalTrace.mem_delivered_self (wireCodec sp ro binding io)
    (nodeAdapter sp ro binding) hs st o

/-- `visit` of an object whose processing refuses no block: the object, then `visitList` of what
it carries. -/
theorem visit_of_not_refuses {st : State sp ro binding} {o : Wire sp.n binding}
    (h : ¬ Refuses io hs st o) :
    (visit io hs st o).1 = o :: (visitList io hs (processOne io hs st o) o.carried).1 := by
  rcases visit_cases io hs st o with ⟨hr, -⟩ | ⟨-, hv⟩
  · exact absurd hr h
  · rw [hv]

/-- Processing an object with a data body (a vote, an attestation or a wrapper) refuses no
block. -/
theorem not_refuses_of_data {st : State sp ro binding} {o : Wire sp.n binding} {au b cs}
    (ho : o = .mk au (.data b) cs) : ¬ Refuses io hs st o := by
  rintro ⟨h, -⟩
  subst ho
  exact h

/-- Processing a canonical block refuses it exactly when `on_block` does not accept it: it is of
a future slot or the FG refuses it. -/
theorem refuses_iff_of_canonEvent {st : State sp ro binding} {o : Wire sp.n binding} {B : Blk sp}
    (h : canonEvent sp ro io hs o = some (.block B)) :
    Refuses io hs st o ↔ sp.toParams.slotOf st.now < B.slot ∨ st.node.fg.onBlock B = none := by
  have hshape : BlockShaped o := by
    have hd := decodeBlock_of_canonEvent h
    rw [decodeBlock_eq] at hd
    split at hd
    · trivial
    · cases hd
  constructor
  · exact fun hr => hr.2 B h
  · intro hB
    refine ⟨hshape, fun B' h' => ?_⟩
    change canonEvent sp ro io hs o = some (.block B') at h'
    rw [h, Option.some.injEq, Node.Event.block.injEq] at h'
    exact h' ▸ hB

/-- `visit` of an object that carries nothing is that object. -/
theorem visit_of_carried_eq_nil (st : State sp ro binding) {o : Wire sp.n binding}
    (h : o.carried = []) : (visit io hs st o).1 = [o] := by
  rcases visit_cases io hs st o with ⟨-, hv⟩ | ⟨-, hv⟩ <;> rw [hv]
  rw [h, visitList_nil_eq]

/-- A delivery of an object that carries nothing processes that object alone. -/
theorem delivered_of_carried_eq_nil (st : State sp ro binding) {o : Wire sp.n binding}
    (h : o.carried = []) : delivered io hs st o = [o] :=
  visit_of_carried_eq_nil io hs st h

/-- `visit` starts with the visited object. -/
theorem visit_head (st : State sp ro binding) (o : Wire sp.n binding) :
    ∃ rest, (visit io hs st o).1 = o :: rest := by
  rcases visit_cases io hs st o with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact ⟨_, rfl⟩

end Visit
end
end Consensus.Goldilocks.Simulation

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
open Shape Blocks

variable {P : Params} {A : NodeAC P} {K I B S : Type} [DecidableEq I]
  (C : WireCodec A K I B) (D : Adapter A K I B S) (hs : List (Header I × Nat))

/-- Every non-refused visited object has its direct children in the visit list. -/
private def Closed (st : S) (l : List (ShapeObj P.n K I B)) : Prop :=
  ∀ pre x post, l = pre ++ x :: post → ¬ Refuses C D hs (pre.foldl (processOne C D hs) st) x →
    x.carried ⊆ l

private theorem closed_append {st : S} {l₁ l₂ : List (ShapeObj P.n K I B)}
    (h₁ : Closed C D hs st l₁) (h₂ : Closed C D hs (l₁.foldl (processOne C D hs) st) l₂) :
    Closed C D hs st (l₁ ++ l₂) := by
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
private theorem visit_closed : ∀ (st : S) (o : ShapeObj P.n K I B),
    Closed C D hs st (visit C D hs st o).1 ∧
      (visit C D hs st o).1.foldl (processOne C D hs) st = (visit C D hs st o).2 ∧
      o ∈ (visit C D hs st o).1
  | st, .mk a m cs => by
    rw [visit]
    split
    · rename_i hr
      refine ⟨?_, rfl, List.mem_cons_self⟩
      intro pre x post he hx
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        exact absurd hr hx
      | cons p pre => simp at he
    · obtain ⟨hcl, hsub, hfold⟩ := visitList_closed (processOne C D hs st (.mk a m cs)) cs
      refine ⟨?_, hfold, List.mem_cons_self⟩
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
private theorem visitList_closed : ∀ (st : S) (cs : List (ShapeObj P.n K I B)),
    Closed C D hs st (visitList C D hs st cs).1 ∧ cs ⊆ (visitList C D hs st cs).1 ∧
      (visitList C D hs st cs).1.foldl (processOne C D hs) st = (visitList C D hs st cs).2
  | st, [] => ⟨fun pre x post he => by simp [visitList] at he, by simp, rfl⟩
  | st, c :: cs => by
    rw [visitList]
    obtain ⟨hcl, hsub, hfold⟩ := visitList_closed (visit C D hs st c).2 cs
    obtain ⟨hc, hfc, hmem⟩ := visit_closed st c
    refine ⟨closed_append C D hs hc (by rw [hfc]; exact hcl), ?_, ?_⟩
    · exact List.cons_subset.mpr ⟨List.mem_append_left _ hmem,
        List.Subset.trans hsub (List.subset_append_right _ _)⟩
    · dsimp only
      rw [List.foldl_append, hfc, hfold]
end

/-- Folding the visited objects reaches the visit's final state. -/
theorem foldl_delivered {st : S} {o : ShapeObj P.n K I B} :
    (delivered C D hs st o).foldl (processOne C D hs) st = (visit C D hs st o).2 :=
  (visit_closed C D hs st o).2.1

/-- A non-refused visited object has its direct children in the same delivery. -/
theorem carried_subset_delivered {st : S} {o x : ShapeObj P.n K I B}
    {pre post : List (ShapeObj P.n K I B)} (he : delivered C D hs st o = pre ++ x :: post)
    (hr : ¬ Refuses C D hs (pre.foldl (processOne C D hs) st) x) :
    x.carried ⊆ delivered C D hs st o :=
  (visit_closed C D hs st o).1 pre x post he hr

/-- A non-refused receipt visits its direct children. -/
theorem carried_subset_delivered_self {st : S} {o : ShapeObj P.n K I B}
    (hr : ¬ Refuses C D hs st o) : o.carried ⊆ delivered C D hs st o := by
  obtain ⟨a, m, cs⟩ := o
  apply carried_subset_delivered C D hs (pre := []) (post :=
    (visitList C D hs (processOne C D hs st (.mk a m cs)) cs).1) _ hr
  unfold delivered
  rw [visit, ite_eq_right hr]
  rfl

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Simulation
open AsChainShape Shape Blocks
open AC (ACParams ReplayOrder)
variable {binding : VoteBinding} {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- A delivery processes its delivered objects in order (`process`): their fold reaches
`visit`'s state. -/
theorem process_eq_visit (hs : List (Header Info × Nat))
    (st : State sp ro binding) (o : Wire sp.n binding) :
    process st o hs = (visit st.voteIO hs st o).2 :=
  NodeAsChainShape.CanonicalTrace.foldl_delivered
    (wireCodec sp ro binding st.voteIO) (nodeAdapter sp ro binding) hs

variable (io : VoteAuth sp.n binding) (hs : List (Header Info × Nat))

/-- The objects carried by a delivered object are delivered too, unless processing it, from the
state the objects delivered before it leave, refuses a block. -/
theorem carried_subset_delivered {st : State sp ro binding} {o x : Wire sp.n binding}
    {pre post : List (Wire sp.n binding)} (he : delivered io hs st o = pre ++ x :: post)
    (hr : ¬ Refuses io hs (pre.foldl (processOne io hs) st) x) :
    x.carried ⊆ delivered io hs st o :=
  NodeAsChainShape.CanonicalTrace.carried_subset_delivered
    (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs he hr

/-- The objects the received object carries are delivered unless processing it refuses a block. -/
theorem carried_subset_delivered_self {st : State sp ro binding} {o : Wire sp.n binding}
    (hr : ¬ Refuses io hs st o) : o.carried ⊆ delivered io hs st o :=
  NodeAsChainShape.CanonicalTrace.carried_subset_delivered_self
    (wireCodec sp ro binding io) (nodeAdapter sp ro binding) hs hr

end Consensus.Goldilocks.Simulation

end
