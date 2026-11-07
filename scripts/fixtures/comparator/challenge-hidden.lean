module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): a declaration between two
comments on one line. -/

theorem Consensus.Review.obligationsSufficient : Consensus.Review.ObligationsSufficient := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Review.obligationsSufficientOn : Consensus.Review.ObligationsSufficientOn := sorry
theorem Consensus.Goldilocks.meetsObligations : Consensus.Goldilocks.MeetsObligations := sorry
theorem Consensus.Goldilocks.goldilocksCorrect : Consensus.Goldilocks.GoldilocksCorrect := sorry

/- harmless -/ axiom extra : False /- harmless -/

end
