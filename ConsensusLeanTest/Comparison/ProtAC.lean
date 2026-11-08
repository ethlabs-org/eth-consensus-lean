module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.ProtAC
public import ConsensusLeanTest.Goldilocks.AC.Base

@[expose] public section

/-! # Tier A protection: sanity and rejection tests

* `parentRunAC` is inhabited (the one-tick run), so the parent's profile is not vacuous by its
  run predicate.
* A validator with no call by `T` reads nothing (`ReadAC`).
* The default lag and recovery are `⊤` outside the contract's outage (a budget above `4k − 5`, a
  catch-up below the contract's) and the contract's `4k + 6` and `9` at its numbers. -/

namespace Consensus.Goldilocks.Comparison.Test.ProtAC

open SA Consensus.Comparison Consensus.Goldilocks.SA.Test

/-- **The parent's run predicate is inhabited.** -/
theorem parentRunAC_oneTick : parentRunAC oneTick Set.univ ({g} : Set (Blk sp1.n Unit)) :=
  ⟨_, acRun_one_tick⟩

/-- **No read before the first call**: the one-tick run's only call is at time `0`. -/
theorem not_readAC_before_first_call (B : Blk sp1.n Unit) : ¬ ReadAC oneTick v0 (-1) B := by
  rintro ⟨j, ℓ, ⟨-, hj, -⟩, -, -⟩
  simp [oneTick] at hj

/-- The point at the contract's numbers with budget `β`, cohort `A`, cap `f` and catch-up `cu`. -/
def contractPt (β A f cu : ℕ) : ProtQ :=
  ⟨β, A, f, .stable, 0, 4 * sp1.k + 6, 0, 5, 1 / 2, cu⟩

/-- **The contract's lag and recovery at its numbers.** -/
theorem protLagAC0_contract :
    protLagAC0 sp1 (contractPt 3 1 0 19) = ((4 * sp1.k + 6 : ℕ) : WithTop ℕ) ∧
    protRecAC0 sp1 (contractPt 3 1 0 19) = ((9 : ℕ) : WithTop ℕ) := by
  refine ⟨ite_eq_left ?_, ite_eq_left ?_⟩ <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [contractPt]

/-- **A budget above `4k − 5` is outside the contract's outage.** -/
theorem protLagAC0_off_contract : protLagAC0 sp1 (contractPt 4 1 0 19) = ⊤ := by
  refine ite_eq_right ?_
  rintro ⟨h, -⟩
  norm_num [contractPt] at h

/-- **A catch-up below the contract's is outside its outage.** -/
theorem protRecAC0_off_contract : protRecAC0 sp1 (contractPt 3 1 0 18) = ⊤ := by
  refine ite_eq_right ?_
  rintro ⟨-, -, -, -, -, h⟩
  norm_num [contractPt] at h

end Consensus.Goldilocks.Comparison.Test.ProtAC

end
