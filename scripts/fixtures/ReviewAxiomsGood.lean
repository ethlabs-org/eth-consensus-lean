import CheckFixtures.Proof

/-! Positive fixture for the pinned-axiom mechanism of `ConsensusTests/ReviewAxioms.lean`:
the pinned message matches, so `lake env lean` exits 0. -/

example : CheckFixtures.Proof.helper = 1 := CheckFixtures.Proof.helper_eq

/-- info: 'CheckFixtures.Proof.helper_eq' does not depend on any axioms -/
#guard_msgs in #print axioms CheckFixtures.Proof.helper_eq
