module

@[expose] public section

/-! Step 3b self-test: a solution proved by `native_decide` (it trusts compiled code). -/

theorem CheckFixtures.Audit.SolNative.s : 2 + 2 = 4 := by native_decide
