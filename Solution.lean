module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Main
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Proofs.Faithful.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Refinement.Main

@[expose] public section

/-! # Proofs of the Challenge statements

Each statement of `ConsensusLean/Statements/Review.lean` is proved by the existing theorem whose
type it is, so the kernel checks the statement against that theorem's type; the Goldilocks
acceptance endpoint is proved by its milestone proof. This module is the comparator's solution
module (`comparator.json`). The other Goldilocks milestones are proved lemmas, pinned by
`ConsensusLeanTest/MilestoneAxioms.lean` (docs/decisions.md, 2026-11-04). -/

namespace Consensus.Review

theorem acceptedGood : AcceptedGood := @Consensus.Shape.Accepted.good

theorem regimesRealizable : RegimesRealizable := @Consensus.Shape.regimes_realizable

theorem logFaithful : LogFaithful := @Consensus.Model.sysOf_log_faithful

theorem heldIffServed : HeldIffServed := @Consensus.Model.Run.held_iff_served

end Consensus.Review

/-! Goldilocks Accepted: the concrete acceptance endpoint
(`Statements/Refinement/Accepted`). -/

/-- Goldilocks Accepted: `AcceptedEndpoint`. -/
theorem Consensus.Goldilocks.Refinement.acceptedEndpoint :
    Consensus.Goldilocks.Refinement.AcceptedEndpoint :=
  Consensus.Goldilocks.Refinement.accepted_endpoint

end
