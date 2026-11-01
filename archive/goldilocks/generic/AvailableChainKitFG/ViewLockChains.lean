module
public import AvailableChainKitFG.ViewLockChainsDef
public import AvailableChainKitFG.Accountable

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- Apply the finalized chain comparison to each block above the threshold.
DC: ChainState/FinalityComparison.lean:50–56; same: strict height and finalized ancestry.
The local chain agreement premise supplies DC's bound for this comparison.
INTENTIONAL: root is a function of the content; record K/Accountable:15–18, GLY:57–58. -/
theorem viewLock_of_chains : ViewLockOfChainsStatement := by
  intro V _ _ _ E cfg K Fb vw θ hroots hKF hθ hbound W hW hh
  have hc := (slashableWeight_or_finalized_preceq E cfg K W (hroots W hW)
    (Nat.lt_of_le_of_lt hθ hh)).resolve_left (hbound W hW)
  exact hKF ▸ hc

/-- All signers in the evidence set are faulty, so their weight is too small.
DC: ChainState/FinalityComparison.lean:50–56; same: strict height and finalized ancestry.
The strict weight bound and honest chain rows supply the agreement premise.
INTENTIONAL: root is a function of the content; record K/Accountable:15–18, GLY:57–58. -/
theorem viewLock_of_honest_chains : ViewLockOfHonestChainsStatement := by
  intro V _ _ _ E cfg K Fb vw θ faulty hroots hKF hθ hweight hnoSlash
  apply viewLock_of_chains E cfg K Fb vw θ hroots hKF hθ
  intro W hW hev
  obtain ⟨S, hS, he⟩ := hev
  have hsub : S ⊆ faulty := by
    intro i hi
    obtain ⟨a, ha, b, hb, hai, _, hab⟩ := he i hi
    by_contra hif
    exact hnoSlash W hW a ha b hb (by simpa only [hai] using hif) hab
  have hw : E.weightOf S ≤ E.weightOf faulty := Finset.sum_le_sum_of_subset hsub
  change 2 * E.q ≤ E.totalWeight + E.weightOf S at hS
  omega

end AvailableChain.KitFG
end
