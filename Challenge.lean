module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

@[expose] public section

/-! # Comparator challenge (non-default library; never built by `lake build`)

The review statements of `ConsensusLean/Statements/Review.lean` and the Goldilocks statements, the
obligations endpoint and the headline on runs whose faults do not grow (`MeetsObligationsConstant`,
`GoldilocksCorrectConstant`; `milestone_statements_modules` in `scripts/boundaries.toml`), with
`sorry` proofs. The growing-fault Goldilocks endpoint and headline (`Statements/Growing`) are stated
and not yet certified.
`lake comparator` (`comparator.json`, CI only) checks that the solution module `Solution` proves
exactly these statements, built from Spec alone, under `propext`, `Quot.sound` and
`Classical.choice`. The other Goldilocks milestones are proved lemmas, not certified here
(`docs/decisions.md` §"Trusted surface and Challenge scope"). -/

theorem Consensus.Review.obligationsSufficient : Consensus.Review.ObligationsSufficient := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Review.obligationsSufficientOn : Consensus.Review.ObligationsSufficientOn := sorry
theorem Consensus.Goldilocks.meetsObligationsConstant :
    Consensus.Goldilocks.MeetsObligationsConstant := sorry
theorem Consensus.Goldilocks.goldilocksCorrectConstant :
    Consensus.Goldilocks.GoldilocksCorrectConstant := sorry

end
