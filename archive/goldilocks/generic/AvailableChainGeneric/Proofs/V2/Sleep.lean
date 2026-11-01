module
public import AvailableChainGeneric.Proofs.V2.Reads

public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

variable {V In : Type} [DecidableEq V] {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : V2.Run V P} {v : V} {a b : Time}

/-- A time window after the action cut gives the exact index restriction. -/
theorem restartFree_actionCut_idxBefore (hS : V2.ScheduleWellFormed E rho)
    (hab : a < b) (hR : V2.NoRestartOn rho v a b) :
    V2.restartFree rho v (V2.Run.actionCut rho a) (V2.Run.idxBefore rho b) := by
  intro k t hak hkb he
  have hb := (index_lt_idxBefore_iff hS he b).mp hkb
  have ha := (index_lt_actionCut_iff hS he a).not.mp (Nat.not_lt.mpr hak)
  apply hR k t he
  · apply lt_of_not_ge
    intro h
    rcases lt_or_eq_of_le h with h | h
    · exact ha (Or.inl h)
    · exact ha (Or.inr ⟨h, rfl⟩)
  · exact hb

/-- Every event in the action cut is strictly before a later deadline. -/
theorem actionCut_le_idxBefore (hS : V2.ScheduleWellFormed E rho) (hab : a < b) :
    V2.Run.actionCut rho a ≤ V2.Run.idxBefore rho b := by
  change (rho.events.filter (fun e =>
    decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))).length ≤ _
  rw [V2.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  apply decide_eq_true
  have h : e.time < a ∨ (e.time = a ∧ e.phase = 0) := of_decide_eq_true he
  rcases h with h | ⟨h, _⟩
  · exact h.trans hab
  · exact h ▸ hab

end AvailableChain.Gen.V2
