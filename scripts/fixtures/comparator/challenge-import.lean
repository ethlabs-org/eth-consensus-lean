module
public import ConsensusSpec
public import ConsensusProofs.Review

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): the challenge imports more than the Spec root. -/

theorem Consensus.Review.acceptedGood : Consensus.Review.AcceptedGood := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry

end
