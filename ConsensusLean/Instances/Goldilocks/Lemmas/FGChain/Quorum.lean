module
public import ConsensusLean.Instances.Goldilocks.Statements.FGSafety

public section

/-! # Goldilocks FG: quorum intersection (G1.1)

Two sets of at least `q = ⌈2n/3⌉` validators meet in at least `2q − n ≥ n/3` of them. -/

namespace Consensus.Goldilocks.FG

/-- **G1.1.** -/
theorem quorum_intersection (gp : FGParams) : QuorumIntersection gp := by
  sorry

end Consensus.Goldilocks.FG

end
