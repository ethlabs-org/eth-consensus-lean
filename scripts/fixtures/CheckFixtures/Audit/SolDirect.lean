module

public import CheckFixtures.Audit.Clean

@[expose] public section

/-! Step 3b self-test: a solution with a direct `sorry`. -/

theorem CheckFixtures.Audit.SolDirect.s : 1 = 1 := sorry
