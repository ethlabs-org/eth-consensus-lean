module
public import AvailableChainKitFG.CrossingCore
public import AvailableChainKitFG.StoreSafety

public section

/-! WC plan §5; DC low finalizations use the exact finalized pair. -/

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- WC plan §5; DC crossing with explicit root identity and honest row evidence. -/
theorem finalizedOccurrence_preceq_of_crossing (Elect : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws Elect H f)
    (D W X : FGBlock V) (h : Height) (hF : (f D).F = X) (hheight : (f D).h_F = h)
    (hroot : RootInjectiveOn D W) (faulty : Finset V)
    (hcap : Elect.weightOf faulty + Elect.totalWeight < 2 * Elect.q)
    (hsafe : ∀ a ∈ chainRows W, ∀ b ∈ chainRows D,
      a.signer ∉ faulty → ¬ Slashable a b)
    (hcross : h < (H W).h) : FGBlock.Preceq X W := by
  subst X
  by_cases hz : h = 0
  · rw [hc.finalized_zero D (hheight.trans hz)]
    exact genesis_preceq W
  · by_contra hn
    exact no_slashableWeight_of_fault_bound Elect faulty _ _ hcap hsafe
      (slashableWeight_of_finalized_pair_crossing_of_certificate Elect H f hc D W hroot
        (fun he => hz (hheight.symm.trans he)) (hheight ▸ hcross) hn)

end AvailableChain.KitFG
end
