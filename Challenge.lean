module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

@[expose] public section

/-! # Comparator challenge (non-default library; never built by `lake build`)

The review statements of `ConsensusLean/Statements/Review.lean` and the Goldilocks statements, the
obligations endpoint, the headline and the outage row at every vote binding (`MeetsObligations`,
`GoldilocksCorrect`, `GoldilocksCorrectWithExcuses`, `PersistsWith`;
`milestone_statements_modules` in `scripts/boundaries.toml`), with `sorry` proofs.
`lake comparator` (`comparator.json`, CI only) checks that the solution module `Solution` proves
exactly these statements, built from Spec alone, under `propext`, `Quot.sound` and
`Classical.choice`. The other Goldilocks milestones are proved lemmas, not certified here
(`docs/decisions.md` §"Trusted surface and Challenge scope"). -/

theorem Consensus.Review.obligationsSufficient : Consensus.Review.ObligationsSufficient := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Review.obligationsSufficientOn : Consensus.Review.ObligationsSufficientOn := sorry
theorem Consensus.Goldilocks.meetsObligations : Consensus.Goldilocks.MeetsObligations := sorry
theorem Consensus.Goldilocks.goldilocksCorrect : Consensus.Goldilocks.GoldilocksCorrect := sorry

/-- For every vote binding, population-wide or a per-slot committee: the outage row of the
obligations (`persists`) for `goldilocksWith S` at the obligations contract. -/
theorem Consensus.Goldilocks.persistsWith : Consensus.Goldilocks.PersistsWith := sorry

/-- On every structural run: the full behaviour on that single run, or a forgery,
credential failure or inadmissible selection. Collisions excuse only `Holds`
rows, never `HoldsAlways` rows. The laws `convicts_mono` and `view_mono` remain
global over all runs. `SelValid` checks every role, including slots beyond the
horizon, of selection data fixed before execution; a failure need not be observed.
No execution binding is assumed; adequacy and realizability keep their clean witnesses. -/
theorem Consensus.Goldilocks.goldilocksCorrectWithExcuses : Consensus.Goldilocks.GoldilocksCorrectWithExcuses := sorry

end
