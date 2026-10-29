/-! Fixture for the exclusion of `CheckConsensusAxioms.lean`: a module whose name only shares the
prefix `ConsensusChallenge` is still audited, so its axiom `bad` must be reported. -/

axiom CheckFixtures.ChallengePrefix.bad : False

theorem CheckFixtures.ChallengePrefix.usesBad : False := CheckFixtures.ChallengePrefix.bad
