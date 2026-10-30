module

public import CheckFixtures.Audit.Lemma

@[expose] public section

/-! Step 3b self-test: a solution that reaches a `sorry` through an import. -/

theorem CheckFixtures.Audit.SolTransitive.s : 2 = 2 := CheckFixtures.Audit.Lemma.helper
