module
public import ConsensusLean.Statements.Review

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): the challenge imports fewer than the statements modules (the milestone statements module is missing). -/

theorem Consensus.Review.obligationsSufficient : Consensus.Review.ObligationsSufficient := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Review.obligationsSufficientOn : Consensus.Review.ObligationsSufficientOn := sorry
theorem Consensus.Goldilocks.meetsObligationsConstant : Consensus.Goldilocks.MeetsObligationsConstant := sorry
theorem Consensus.Goldilocks.goldilocksCorrectConstant : Consensus.Goldilocks.GoldilocksCorrectConstant := sorry

end
