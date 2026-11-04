module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Accepted

@[expose] public section

/-! # Comparator challenge (non-default library; never built by `lake build`)

The review statements of `ConsensusLean/Statements/Review.lean` and the Goldilocks acceptance
endpoint (`milestone_statements_modules` in `scripts/boundaries.toml`) with `sorry` proofs.
`lake comparator` (`comparator.json`, CI only) checks that the solution module `Solution` proves
exactly these statements, built from Spec alone, under `propext`, `Quot.sound` and
`Classical.choice`. The other Goldilocks milestones are proved lemmas, not certified here
(docs/decisions.md, 2026-11-04). -/

theorem Consensus.Review.obligationsSufficient : Consensus.Review.ObligationsSufficient := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Goldilocks.Refinement.acceptedEndpoint : Consensus.Goldilocks.Refinement.AcceptedEndpoint := sorry

end
