module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Accepted
public import Solution

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): the challenge imports more than the statements module. -/

theorem Consensus.Review.acceptedGood : Consensus.Review.AcceptedGood := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Goldilocks.Refinement.acceptedEndpoint : Consensus.Goldilocks.Refinement.AcceptedEndpoint := sorry

end
