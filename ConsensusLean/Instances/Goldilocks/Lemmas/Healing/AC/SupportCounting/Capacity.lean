module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.SupportCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-! # Split capacity (proofs)

The arithmetic of the split-capacity statements (paper `cfb2d338`, §1): substituting
`2b = n − m − (a − b)` in the support bound `b + h`. -/

namespace Consensus.Goldilocks.SA

theorem split_capacity_half : SplitCapacityHalf := by
  intro n m a b h habm hba hn
  omega

theorem split_capacity : SplitCapacity := by
  intro n m a b h q habm hba hq
  have hn : (n : ℚ) = a + b + m := by exact_mod_cast habm.symm
  have e : (2 * q - 1) * n = 2 * (q * n) - n := by ring
  rw [e]
  linarith

theorem split_half_excluded : SplitHalfExcluded := by
  intro n m a b h habm hba hh hn
  have := split_capacity_half n m a b h habm hba hn
  omega

theorem split_three_quarter_excluded : SplitThreeQuarterExcluded := by
  intro n m a b h f habm hba hhf hfm hfn hq
  omega

end Consensus.Goldilocks.SA

end
