module
public import AvailableChainGeneric -- shake: keep (examples)

public section

namespace AvailableChain.Gen.AC.Tests

open AvailableChain AvailableChain.GridCO AvailableChain.Gen.Pure

-- The n=7, a=2, h=3 case uses the exact h>a count (blueprint/02-clean.md:82).
example :
    ∃ k ∈ ({0, 1, 3} : Finset Nat), k ∉ ({3, 4} : Finset Nat) := by
  exact honest_origin_of_count ({0, 1, 2} : Finset Nat) {3, 4} {0, 1, 3} {0, 1, 2, 3, 4}
    (by decide) (by decide) (by decide) (by decide) (by decide)

end AvailableChain.Gen.AC.Tests
