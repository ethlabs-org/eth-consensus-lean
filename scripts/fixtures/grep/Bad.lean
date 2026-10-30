-- Fixture for grep backstop 7a (never built): every line below must be flagged.
theorem a : 1 = 2 := sorry
theorem b : 1 = 2 := by admit
theorem c : 2 + 2 = 4 := by native_decide
theorem d : 2 + 2 = 4 := by decide +native
set_option debug.skipKernelTC true in
theorem e : 1 = 2 := sorryAx _ false
elab "fake" : tactic => do Lean.Elab.Tactic.closeMainGoal `fake (← Lean.Meta.mkSorry (← Lean.Elab.Tactic.getMainTarget) false)
elab "fake2" : tactic => do let _ ← Lean.Meta.mkLabeledSorry (.const ``Nat []) false true
set_option debug.terminalTacticsAsSorry true in
