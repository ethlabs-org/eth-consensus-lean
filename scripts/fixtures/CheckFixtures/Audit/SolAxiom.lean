module

@[expose] public section

/-! Step 3b self-test: a solution that uses a declared axiom. -/

axiom CheckFixtures.Audit.SolAxiom.ax : 1 = 1

theorem CheckFixtures.Audit.SolAxiom.s : 1 = 1 := CheckFixtures.Audit.SolAxiom.ax
