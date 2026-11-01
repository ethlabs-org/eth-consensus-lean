module
public import AvailableChainGeneric -- shake: keep (test scope)

public section

namespace AvailableChain.Gen.AC.Tests

open AvailableChain AvailableChain.GridCO AvailableChain.Gen.Pure

def oneHead : Wire 1 := ⟨.seat 0 ⟨0, by decide⟩, .head .genesis⟩

-- One honest seat and no other seat give all batch count bounds.
theorem batch_counts_single_head : BatchBounds [.genesis] [oneHead] [oneHead] [oneHead]
    Finset.univ 1 0 .genesis := by
  exact batch_counts [.genesis] [oneHead] [oneHead] [oneHead] Finset.univ 1 0 .genesis
    (by simp) (by simp) (by decide) (by decide) (by decide) (by decide) ⟨by decide⟩

end AvailableChain.Gen.AC.Tests
