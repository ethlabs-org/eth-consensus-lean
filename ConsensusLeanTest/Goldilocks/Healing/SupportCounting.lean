module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SupportCounting

@[expose] public section

/-! # Support counting: controls

The tie the split-capacity statements leave open: at `a = b` and `2h = m` (the paper's checked
geometry `n = 16`, `m = 4`, `a = b = 6`, `h = 2`), a smaller-side count of `b + h` passes the half
test, so `SplitHalfExcluded` cannot be strengthened to `2h ≤ m`. The proved statements are pinned
below by named theorems and their axioms. -/

namespace Consensus.Goldilocks.AC.Test

/-- At `n = 16`, `m = 4`, `a = b = 6`, `h = 2`: `2h = m` and `b + h` passes the half test. -/
theorem split_half_tie_passes :
    6 + 6 + 4 = 16 ∧ 2 * 2 = 4 ∧ 16 ≤ 2 * (6 + 2) := by decide

/-- So `2h < m` cannot be weakened to `2h ≤ m` in `SplitHalfExcluded`. -/
theorem split_half_excluded_tight :
    ¬ ∀ n m a b h : ℕ, a + b + m = n → b ≤ a → 2 * h ≤ m → ¬ n ≤ 2 * (b + h) :=
  fun hall => hall 16 4 6 6 2 (by decide) le_rfl (by decide) (by decide)


/-- `SplitCapacityHalf`, proved. -/
theorem pinCapHalf : Consensus.Goldilocks.AC.SplitCapacityHalf :=
  Consensus.Goldilocks.AC.split_capacity_half

/-- `SplitCapacity`, proved. -/
theorem pinCap : Consensus.Goldilocks.AC.SplitCapacity :=
  Consensus.Goldilocks.AC.split_capacity

/-- `SplitHalfExcluded`, proved. -/
theorem pinHalfExcl : Consensus.Goldilocks.AC.SplitHalfExcluded :=
  Consensus.Goldilocks.AC.split_half_excluded

/-- `SplitThreeQuarterExcluded`, proved. -/
theorem pinQuarterExcl : Consensus.Goldilocks.AC.SplitThreeQuarterExcluded :=
  Consensus.Goldilocks.AC.split_three_quarter_excluded

/-- `CountedHonestInRowSupport`, proved. -/
theorem pinHonestInRow : Consensus.Goldilocks.AC.CountedHonestInRowSupport :=
  Consensus.Goldilocks.AC.counted_honest_in_rowSupport

/-- `RowSupportDisjoint`, proved. -/
theorem pinRowDisjoint : Consensus.Goldilocks.AC.RowSupportDisjoint :=
  Consensus.Goldilocks.AC.rowSupport_disjoint

/-- `NoConflictingHalfOrigins`, proved. -/
theorem pinNoHalfOrigins : Consensus.Goldilocks.AC.NoConflictingHalfOrigins :=
  Consensus.Goldilocks.AC.no_conflicting_half_origins

/-- `CountedFaultyAdmitted`, proved. -/
theorem pinFaultyAdmitted : Consensus.Goldilocks.AC.CountedFaultyAdmitted :=
  Consensus.Goldilocks.AC.counted_faulty_admitted

/-- `SelectedResultsComparable`, proved. -/
theorem pinSelComparable : Consensus.Goldilocks.AC.SelectedResultsComparable :=
  Consensus.Goldilocks.AC.selected_results_comparable

/-- `EligibleBelowSelected`, proved. -/
theorem pinEligibleBelow : Consensus.Goldilocks.AC.EligibleBelowSelected :=
  Consensus.Goldilocks.AC.eligible_below_selected

end Consensus.Goldilocks.AC.Test

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.AC.Test.pinCapHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinCapHalf

/-- info: 'Consensus.Goldilocks.AC.Test.pinCap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinCap

/-- info: 'Consensus.Goldilocks.AC.Test.pinHalfExcl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinHalfExcl

/-- info: 'Consensus.Goldilocks.AC.Test.pinQuarterExcl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinQuarterExcl

/-- info: 'Consensus.Goldilocks.AC.Test.pinHonestInRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinHonestInRow

/-- info: 'Consensus.Goldilocks.AC.Test.pinRowDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinRowDisjoint

/-- info: 'Consensus.Goldilocks.AC.Test.pinNoHalfOrigins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinNoHalfOrigins

/-- info: 'Consensus.Goldilocks.AC.Test.pinFaultyAdmitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinFaultyAdmitted

/-- info: 'Consensus.Goldilocks.AC.Test.pinSelComparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinSelComparable

/-- info: 'Consensus.Goldilocks.AC.Test.pinEligibleBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.Test.pinEligibleBelow


end
