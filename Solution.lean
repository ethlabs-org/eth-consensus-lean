module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Main
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Proofs.Faithful.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Obligations.Main

@[expose] public section

/-! # Proofs of the Challenge statements

Each statement of `ConsensusLean/Statements/Review.lean` is proved by the existing theorem whose
type it is, so the kernel checks the statement against that theorem's type; the Goldilocks
constant-fault obligations endpoint is proved by its milestone proof, and the headline
`GoldilocksCorrectConstant` by that proof and `ShapeObligationsOn.correct`.
This module is the comparator's solution
module (`comparator.json`). The other Goldilocks milestones are proved lemmas, pinned by
`ConsensusLeanTest/MilestoneAxioms.lean` (`docs/decisions.md`
§"Trusted surface and Challenge scope"). -/

namespace Consensus.Review

theorem obligationsSufficient : ObligationsSufficient := @Consensus.Shape.ShapeObligations.correct

theorem obligationsSufficientOn : ObligationsSufficientOn :=
  @Consensus.Shape.ShapeObligationsOn.correct

theorem regimesRealizable : RegimesRealizable := @Consensus.Shape.regimes_realizable

theorem logFaithful : LogFaithful := @Consensus.Model.sysOf_log_faithful

theorem heldIffServed : HeldIffServed := @Consensus.Model.Run.held_iff_served

end Consensus.Review

/-! Goldilocks meets the obligations: the concrete obligations endpoint
(`Statements/Obligations`). -/

/-- Goldilocks meets the obligations on constant-fault runs. -/
theorem Consensus.Goldilocks.meetsObligationsConstant :
    Consensus.Goldilocks.MeetsObligationsConstant :=
  Consensus.Goldilocks.Obligations.meets_obligations_constant

/-- Goldilocks is correct on constant-fault runs; adequacy and realizability remain unrestricted. -/
theorem Consensus.Goldilocks.goldilocksCorrectConstant :
    Consensus.Goldilocks.GoldilocksCorrectConstant := fun S A V =>
  Consensus.Shape.ShapeObligationsOn.correct _
    (Consensus.Goldilocks.Obligations.meets_obligations_constant S A).2 V

end
