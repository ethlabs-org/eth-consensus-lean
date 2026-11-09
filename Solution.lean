module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Main
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Proofs.Faithful.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Obligations.Main
public import ConsensusLean.Lemmas.Model.Excuses

@[expose] public section

/-! # Proofs of the Challenge statements

Each statement of `ConsensusLean/Statements/Review.lean` is proved by the existing theorem whose
type it is, so the kernel checks the statement against that theorem's type; the Goldilocks
obligations endpoint is proved by its milestone proof, and the headline `GoldilocksCorrect` by that
proof and `ShapeObligations.correct`.
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

/-- Goldilocks meets the obligations. -/
theorem Consensus.Goldilocks.meetsObligations : Consensus.Goldilocks.MeetsObligations :=
  Consensus.Goldilocks.Growing.meets_obligations

/-- Goldilocks is correct. -/
theorem Consensus.Goldilocks.goldilocksCorrect : Consensus.Goldilocks.GoldilocksCorrect :=
  fun S A V => Consensus.Shape.ShapeObligations.correct
    (Consensus.Goldilocks.Growing.meets_obligations S A).2 V

/-- Goldilocks' full per-run behaviour, or a forgery, credential failure or
inadmissible selection. Collisions excuse only `Holds`, never `HoldsAlways` rows;
conviction and view monotonicity remain global. Selection checks every role,
including slots beyond the horizon, in data fixed before execution, not only
observed events. No binding premise is assumed. -/
theorem Consensus.Goldilocks.goldilocksCorrectWithExcuses :
    Consensus.Goldilocks.GoldilocksCorrectWithExcuses :=
  fun S A V => Consensus.Model.correctProtocol_with_excuses (goldilocksCorrect S A V)

end
