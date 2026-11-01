module
public import AvailableChainGeneric.Proofs.V2.Duty.Reads

public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

variable {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
  {E : Generic.Env V} {rho : D.Run V P} {v : V} {a b : Time}

/-- A time window after the action cut gives the exact index restriction. -/
theorem restartFree_actionCut_idxBefore (hS : D.ScheduleWellFormed E rho)
    (hab : a < b) (hR : D.NoRestartOn rho v a b) :
    D.restartFree rho v (D.Run.actionCut rho a) (D.Run.idxBefore rho b) := by
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
theorem actionCut_le_idxBefore (hS : D.ScheduleWellFormed E rho) (hab : a < b) :
    D.Run.actionCut rho a ≤ D.Run.idxBefore rho b := by
  change (rho.events.filter (fun e =>
    decide (e.time < a ∨ (e.time = a ∧ e.phase = 0)))).length ≤ _
  rw [D.Run.idxBefore_def]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  apply decide_eq_true
  have h : e.time < a ∨ (e.time = a ∧ e.phase = 0) := of_decide_eq_true he
  rcases h with h | ⟨h, _⟩
  · exact h.trans hab
  · exact h ▸ hab

end AvailableChain.Gen.V2.Duty
