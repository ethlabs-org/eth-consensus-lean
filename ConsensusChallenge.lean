module
public import ConsensusSpec

@[expose] public section

/-! # Comparator challenge (non-default library; never built by `lake build`)

The review statements of `ConsensusSpec/Statements.lean` with `sorry` proofs. `lake comparator`
(`comparator.json`, CI only) checks that the solution module `ConsensusProofs.Review` proves exactly
these statements, built from Spec alone, under `propext`, `Quot.sound` and `Classical.choice`. -/

theorem Consensus.Review.acceptedGood : Consensus.Review.AcceptedGood := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry

end
