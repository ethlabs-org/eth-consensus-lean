import CheckDeclsTest.Bad

/-! Negative fixture for the pinned-axiom mechanism of `ConsensusTests/ReviewAxioms.lean`:
`usesAssumed` depends on the axiom `assumed`, so the pinned standard list does not match and
`lake env lean` exits nonzero. -/

/-- info: 'CheckDeclsTest.Bad.usesAssumed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CheckDeclsTest.Bad.usesAssumed
