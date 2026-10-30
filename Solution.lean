module
public import ConsensusLean.Statements.Review
public import ConsensusLean.Main
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Proofs.Faithful.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.FGSafety.Main

@[expose] public section

/-! # Proofs of the review statements

Each statement of `ConsensusLean/Statements/Review.lean` is proved by the existing theorem whose
type it is, so the kernel checks the statement against that theorem's type; each finished instance
milestone is proved by its milestone proof. This module is the comparator's solution module
(`comparator.json`). -/

namespace Consensus.Review

theorem acceptedGood : AcceptedGood := @Consensus.Shape.Accepted.good

theorem regimesRealizable : RegimesRealizable := @Consensus.Shape.regimes_realizable

theorem logFaithful : LogFaithful := @Consensus.Model.sysOf_log_faithful

theorem heldIffServed : HeldIffServed := @Consensus.Model.Run.held_iff_served

end Consensus.Review

/-! The finished instance milestones: each statement is the milestone definition itself. -/

/-- Goldilocks M₁, FG safety. -/
theorem Consensus.Goldilocks.FG.fGSafety : Consensus.Goldilocks.FG.FGSafety :=
  Consensus.Goldilocks.FG.fg_safety

end
