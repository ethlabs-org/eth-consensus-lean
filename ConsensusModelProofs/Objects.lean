module
public import ConsensusModel.System

@[expose] public section

/-! Structural facts about objects (`parts` is the list of descendants, so
membership is `Contains`) and the one-step unfolding of `stateBefore`; shared
by the canonical-run construction and the lifting lemmas. -/

namespace Consensus.Model

namespace Obj
variable {n : Nat} {Role Item Body : Type}

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

theorem contains_of_mem_parts (o d : Obj n Role Item Body) (h : d ∈ o.parts) : Contains o d := by
  rw [parts_eq, List.mem_cons] at h
  rcases h with rfl | h
  · exact .refl _
  · obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp h
    exact .step hc (contains_of_mem_parts c d hd)
termination_by sizeOf o
decreasing_by exact lt_trans (List.sizeOf_lt_of_mem hc) (carried_size_lt _)

theorem mem_parts_of_contains {o d : Obj n Role Item Body} (h : Contains o d) : d ∈ o.parts := by
  induction h with
  | refl o => rw [parts_eq]; exact List.mem_cons_self
  | step hc _ ih =>
    rw [parts_eq]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, hc, ih⟩)

theorem mem_parts_iff (o d : Obj n Role Item Body) : d ∈ o.parts ↔ Contains o d :=
  ⟨contains_of_mem_parts o d, mem_parts_of_contains⟩

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
