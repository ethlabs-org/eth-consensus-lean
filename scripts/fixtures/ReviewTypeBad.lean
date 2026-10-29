import CheckFixtures.Proof

/-! Negative fixture for the type pins of `ConsensusShapeTests/ReviewAxioms.lean`: the pinned statement
differs from the theorem's type (`n ≤ n + 2` instead of `n ≤ n + helper`, `helper = 1`), so the
`example` does not elaborate and `lake env lean` exits nonzero. -/

example : ∀ n : Nat, n ≤ n + 2 := @CheckFixtures.Proof.le_helper
