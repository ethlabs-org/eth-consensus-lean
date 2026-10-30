module

public import CheckFixtures.Audit.Clean

@[expose] public section

/-! Step 3b self-test: a solution whose closure uses only the standard axioms. -/

theorem CheckFixtures.Audit.SolGood.s : 1 = 1 := CheckFixtures.Audit.Clean.ok
