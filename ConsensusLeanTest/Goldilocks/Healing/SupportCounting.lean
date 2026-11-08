module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SupportCounting

@[expose] public section

/-! # Support counting: controls

The tie the split-capacity statements leave open: at `a = b` and `2h = m` (the paper's checked
geometry `n = 16`, `m = 4`, `a = b = 6`, `h = 2`), a smaller-side count of `b + h` passes the half
test, so `SplitHalfExcluded` cannot be strengthened to `2h ≤ m`. The proved statements are pinned
below by named theorems and their axioms. -/

namespace Consensus.Goldilocks.SA.Test

/-- At `n = 16`, `m = 4`, `a = b = 6`, `h = 2`: `2h = m` and `b + h` passes the half test. -/
theorem split_half_tie_passes :
    6 + 6 + 4 = 16 ∧ 2 * 2 = 4 ∧ 16 ≤ 2 * (6 + 2) := by decide

/-- So `2h < m` cannot be weakened to `2h ≤ m` in `SplitHalfExcluded`. -/
theorem split_half_excluded_tight :
    ¬ ∀ n m a b h : ℕ, a + b + m = n → b ≤ a → 2 * h ≤ m → ¬ n ≤ 2 * (b + h) :=
  fun hall => hall 16 4 6 6 2 (by decide) le_rfl (by decide) (by decide)


/-- `SplitCapacityHalf`, proved. -/
theorem pinCapHalf : Consensus.Goldilocks.SA.SplitCapacityHalf :=
  Consensus.Goldilocks.SA.split_capacity_half

/-- `SplitCapacity`, proved. -/
theorem pinCap : Consensus.Goldilocks.SA.SplitCapacity :=
  Consensus.Goldilocks.SA.split_capacity

/-- `SplitHalfExcluded`, proved. -/
theorem pinHalfExcl : Consensus.Goldilocks.SA.SplitHalfExcluded :=
  Consensus.Goldilocks.SA.split_half_excluded

/-- `SplitThreeQuarterExcluded`, proved. -/
theorem pinQuarterExcl : Consensus.Goldilocks.SA.SplitThreeQuarterExcluded :=
  Consensus.Goldilocks.SA.split_three_quarter_excluded

/-- `CountedHonestInRowSupport`, proved. -/
theorem pinHonestInRow : Consensus.Goldilocks.SA.CountedHonestInRowSupport :=
  Consensus.Goldilocks.SA.counted_honest_in_rowSupport

/-- `RowSupportDisjoint`, proved. -/
theorem pinRowDisjoint : Consensus.Goldilocks.SA.RowSupportDisjoint :=
  Consensus.Goldilocks.SA.rowSupport_disjoint

/-- `NoConflictingHalfOrigins`, proved. -/
theorem pinNoHalfOrigins : Consensus.Goldilocks.SA.NoConflictingHalfOrigins :=
  Consensus.Goldilocks.SA.no_conflicting_half_origins

/-- `CountedFaultyAdmitted`, proved. -/
theorem pinFaultyAdmitted : Consensus.Goldilocks.SA.CountedFaultyAdmitted :=
  Consensus.Goldilocks.SA.counted_faulty_admitted

/-- `SelectedResultsComparable`, proved. -/
theorem pinSelComparable : Consensus.Goldilocks.SA.SelectedResultsComparable :=
  Consensus.Goldilocks.SA.selected_results_comparable

/-- `EligibleBelowSelected`, proved. -/
theorem pinEligibleBelow : Consensus.Goldilocks.SA.EligibleBelowSelected :=
  Consensus.Goldilocks.SA.eligible_below_selected

end Consensus.Goldilocks.SA.Test

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.SA.Test.pinCapHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinCapHalf

/-- info: 'Consensus.Goldilocks.SA.Test.pinCap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinCap

/-- info: 'Consensus.Goldilocks.SA.Test.pinHalfExcl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinHalfExcl

/-- info: 'Consensus.Goldilocks.SA.Test.pinQuarterExcl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinQuarterExcl

/-- info: 'Consensus.Goldilocks.SA.Test.pinHonestInRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinHonestInRow

/-- info: 'Consensus.Goldilocks.SA.Test.pinRowDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinRowDisjoint

/-- info: 'Consensus.Goldilocks.SA.Test.pinNoHalfOrigins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinNoHalfOrigins

/-- info: 'Consensus.Goldilocks.SA.Test.pinFaultyAdmitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinFaultyAdmitted

/-- info: 'Consensus.Goldilocks.SA.Test.pinSelComparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinSelComparable

/-- info: 'Consensus.Goldilocks.SA.Test.pinEligibleBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.Test.pinEligibleBelow


end
