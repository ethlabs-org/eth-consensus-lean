module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.State

public section

/-! # Membership of the newest finality pair

Start with `foldl_newest_mem_or_initial`: selecting the newest height returns the initial pair or a
pair in the input list. Client safety and held-state record arguments share this induction. -/

namespace Consensus.Goldilocks.FG.Record

/-- The newest-pair fold returns its start or a member of the list. -/
theorem foldl_newest_mem_or_initial {l : List (Nat × Nat)} {acc : Option (Nat × Nat)}
    {p : Nat × Nat}
    (h : l.foldl (fun acc p => match acc with
      | none => some p
      | some r => if r.1 < p.1 then some p else some r) acc = some p) :
    acc = some p ∨ p ∈ l := by
  induction l generalizing acc with
  | nil => exact Or.inl h
  | cons q l ih =>
    rcases ih h with h' | h'
    · rcases acc with _ | r
      · simp only [Option.some.injEq] at h'
        exact Or.inr (h' ▸ List.mem_cons_self)
      · dsimp only at h'
        split_ifs at h' with hlt
        · simp only [Option.some.injEq] at h'
          exact Or.inr (h' ▸ List.mem_cons_self)
        · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

end Consensus.Goldilocks.FG.Record

end
