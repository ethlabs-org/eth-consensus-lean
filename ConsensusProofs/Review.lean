module
public import ConsensusSpec.Statements
public import ConsensusProofs.Shape.Accepted
public import ConsensusProofs.Shape.Realizable
public import ConsensusProofs.Model.Faithful

@[expose] public section

/-! # Proofs of the review statements

Each statement of `ConsensusSpec/Statements.lean` is proved by the existing theorem whose type it
is, so the kernel checks the statement against that theorem's type. This module is the comparator's
solution module (`comparator.json`). -/

namespace Consensus.Review

theorem acceptedGood : AcceptedGood := @Consensus.Shape.Accepted.good

theorem regimesRealizable : RegimesRealizable := @Consensus.Shape.regimes_realizable

theorem logFaithful : LogFaithful := @Consensus.Model.sysOf_log_faithful

theorem heldIffServed : HeldIffServed := @Consensus.Model.Run.held_iff_served

end Consensus.Review

end
