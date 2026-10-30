module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Base

public section

/-! # Goldilocks SA: views and counting (A0.2's support clause, A0.3's view facts)

Facts about vote views that hold in any well-formed frame, with no reachability: support heads
are in the tree, supporters shrink and opponents grow along ancestry, and majorities lie on one
chain. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A0.2, support heads and the opponents of `Φ.F`.** -/
theorem support_in_tree : SupportInTree sp := by
  sorry

/-- **A0.3, supporters.** -/
theorem supporters_antitone : SupportersAntitone sp := by
  intro FGP Φ V s B C hBC i ⟨hne, x, hx, hval, hslot, R, hR, hroot, hCR⟩
  exact ⟨hne, x, hx, hval, hslot, R, hR, hroot, Relation.ReflTransGen.trans hBC hCR⟩

/-- **A0.3, opponents.** -/
theorem opponents_monotone : OpponentsMonotone sp := by
  sorry

/-- **A0.3, majority blocks.** -/
theorem majority_chain : MajorityChain sp := by
  sorry

/-- **A0.3, optimistic blocks.** -/
theorem optimistic_chain : OptimisticChain sp := by
  sorry

end Consensus.Goldilocks.SA

end
