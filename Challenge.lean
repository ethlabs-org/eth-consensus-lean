module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Local
public import ConsensusLean.Instances.Goldilocks.Statements.FGStore.Trace

@[expose] public section

/-! # Comparator challenge (non-default library; never built by `lake build`)

The review statements of `ConsensusLean/Statements/Review.lean` and the closed statements of the
finished instance milestones (`milestone_statements_modules` in `scripts/boundaries.toml`) with
`sorry` proofs.
`lake comparator` (`comparator.json`, CI only) checks that the solution module `Solution` proves
exactly these statements, built from Spec alone, under `propext`, `Quot.sound` and
`Classical.choice`. -/

theorem Consensus.Review.acceptedGood : Consensus.Review.AcceptedGood := sorry
theorem Consensus.Review.regimesRealizable : Consensus.Review.RegimesRealizable := sorry
theorem Consensus.Review.logFaithful : Consensus.Review.LogFaithful := sorry
theorem Consensus.Review.heldIffServed : Consensus.Review.HeldIffServed := sorry
theorem Consensus.Goldilocks.FG.fGSafety : Consensus.Goldilocks.FG.FGSafety := sorry
theorem Consensus.Goldilocks.SA.aCSteps : Consensus.Goldilocks.SA.ACSteps := sorry
theorem Consensus.Goldilocks.Store.fGStoreLocal : Consensus.Goldilocks.Store.FGStoreLocal := sorry
theorem Consensus.Goldilocks.Store.fGStoreTrace : Consensus.Goldilocks.Store.FGStoreTrace := sorry

end
