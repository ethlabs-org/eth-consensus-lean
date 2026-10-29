import CheckFixtures.BadAxiom.A

/-! Negative fixture for the pinned-axiom mechanism: `u` uses the axiom `ax`, so the pinned
standard list does not match and `lake env lean` exits nonzero. -/

/-- info: 'CheckFixtures.BadAxiom.u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CheckFixtures.BadAxiom.u
