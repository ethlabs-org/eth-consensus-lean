module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.SupportCounting

@[expose] public section

/-! # Support counting: controls

The tie the split-capacity statements leave open: at `a = b` and `2h = m` (the paper's checked
geometry `n = 16`, `m = 4`, `a = b = 6`, `h = 2`), a smaller-side count of `b + h` passes the half
test, so `SplitHalfExcluded` cannot be strengthened to `2h ≤ m`. -/

namespace Consensus.Goldilocks.SA.Test

/-- At `n = 16`, `m = 4`, `a = b = 6`, `h = 2`: `2h = m` and `b + h` passes the half test. -/
theorem split_half_tie_passes :
    6 + 6 + 4 = 16 ∧ 2 * 2 = 4 ∧ 16 ≤ 2 * (6 + 2) := by decide

/-- So `2h < m` cannot be weakened to `2h ≤ m` in `SplitHalfExcluded`. -/
theorem split_half_excluded_tight :
    ¬ ∀ n m a b h : ℕ, a + b + m = n → b ≤ a → 2 * h ≤ m → ¬ n ≤ 2 * (b + h) :=
  fun hall => hall 16 4 6 6 2 (by decide) le_rfl (by decide) (by decide)

end Consensus.Goldilocks.SA.Test

end
