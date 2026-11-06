module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.State

public section

/-! # Fault bounds in quorum form

Start with `FGParams.faults_lt_quorum_margin`: the positive population and the
`3f ≤ n - 1` bound suffice for `f < 2q - n`. No run or set assumptions are needed. -/

namespace Consensus.Goldilocks.FG.FGParams

/-- `3f ≤ n - 1` gives the strict fault margin of two quorums. -/
theorem faults_lt_quorum_margin (gp : FGParams) {f : Nat}
    (hf : 3 * f ≤ gp.n - 1) : f < 2 * gp.q - gp.n := by
  have hn : 0 < gp.n := gp.hn
  change f < 2 * ((2 * gp.n + 2) / 3) - gp.n
  omega

end Consensus.Goldilocks.FG.FGParams

end
