module
public import ConsensusSpec

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): one theorem states `True` instead of its statement. -/

theorem Consensus.Review.acceptedGood : Consensus.Review.AcceptedGood := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : True := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry

end
