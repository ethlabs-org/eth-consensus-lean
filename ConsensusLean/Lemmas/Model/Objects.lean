module
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Good
public import ConsensusLean.Lemmas.Model.Protocol

public section

/-! Structural facts about objects (`Contains` is membership in `parts`) and
the one-step unfolding of `stateBefore`; shared by the canonical-run
construction and the lifting lemmas. -/

namespace Consensus.Model

namespace Obj
variable {n : Nat} {Role Item Body : Type}

/-- The message of an object (a field accessor; no trusted definition reads it). -/
abbrev msg : Obj n Role Item Body → Msg Item Body
  | mk _ m _ => m

theorem partsList_eq (cs : List (Obj n Role Item Body)) :
    parts.partsList cs = cs.flatMap parts := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [parts.partsList, ih]

theorem parts_eq (o : Obj n Role Item Body) : o.parts = o :: o.carried.flatMap parts := by
  cases o
  simp [parts, partsList_eq, carried]

theorem carried_size_lt (o : Obj n Role Item Body) : sizeOf o.carried < sizeOf o := by
  cases o
  simp [carried]

theorem Contains.refl (o : Obj n Role Item Body) : Contains o o := by
  rw [Contains, parts_eq]
  exact List.mem_cons_self

theorem Contains.step {o c d : Obj n Role Item Body} (hc : c ∈ o.carried) (h : Contains c d) :
    Contains o d := by
  rw [Contains, parts_eq]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, h⟩)

/-- `o` contains `d` iff `d` is `o` or is contained in an object `o` carries. -/
theorem Contains.cases {o d : Obj n Role Item Body} (h : Contains o d) :
    d = o ∨ ∃ c ∈ o.carried, Contains c d := by
  rw [Contains, parts_eq, List.mem_cons] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_flatMap.mp h)

theorem Contains.trans {a b c : Obj n Role Item Body} (h₁ : Contains a b)
    (h₂ : Contains b c) : Contains a c := by
  rcases h₁.cases with rfl | ⟨x, hx, hxb⟩
  · exact h₂
  · exact .step hx (hxb.trans h₂)
termination_by sizeOf a
decreasing_by exact lt_trans (List.sizeOf_lt_of_mem hx) (carried_size_lt _)

end Obj

namespace Run

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

theorem stateBefore_succ (rho : Run F E) {i : Nat} {e : Event V (protoOf F E).Object}
    (hi : rho.events[i]? = some e) :
    rho.stateBefore (i + 1) = rho.step (rho.stateBefore i) e := by
  simp only [stateBefore, List.take_add_one, hi, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

end Run

end Consensus.Model

end
