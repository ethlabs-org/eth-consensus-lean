module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

@[expose] public section

/-! Negative fixture for check.sh step 9 (challenge_ok; never built): an extra declaration next to the theorems. -/

theorem Consensus.Review.obligationsSufficient : Consensus.Review.ObligationsSufficient := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Goldilocks.meetsObligations : Consensus.Goldilocks.MeetsObligations := sorry

axiom Consensus.Review.extra : False

end
