module
public import AvailableChainKitFG.FinalizedOccurrence
public import AvailableChainKitFG.CertificateSimplex

public section

/-! WC plan §5; DC the zero-height case and the pure adapter's kernel axiom audit. -/

namespace AvailableChain.KitFG.Tests.FinalizedOccurrence

open AvailableChain.SimplexFG

/-- WC plan §5; DC zero finalized height gives the genesis prefix. -/
theorem zero_height : FGBlock.Preceq (.genesis : FGBlock (Fin 4)) .genesis := by
  apply finalizedOccurrence_preceq_of_crossing E4 (simplexHeightView E4 cfg1)
    (simplexFinalityView E4 cfg1) (simplexCertificateLaws E4 cfg1)
    .genesis .genesis .genesis 0 rfl rfl _ ∅ (by decide) _ (by decide)
  · intro A B hA hB _
    have ha : A = .genesis := by
      rcases hA with h | h <;> exact of_decide_eq_true h
    have hb : B = .genesis := by
      rcases hB with h | h <;> exact of_decide_eq_true h
    exact ha.trans hb.symm
  · intro a ha
    simp [chainRows] at ha

#print axioms AvailableChain.KitFG.finalizedOccurrence_preceq_of_crossing
#print axioms AvailableChain.KitFG.Tests.FinalizedOccurrence.zero_height

end AvailableChain.KitFG.Tests.FinalizedOccurrence
end
