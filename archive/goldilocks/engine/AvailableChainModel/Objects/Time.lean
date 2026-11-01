module
public import Mathlib.Algebra.Order.Group.Int
public import AvailableChainModel.Objects.Identifiers

@[expose] public section

namespace AvailableChain

/-- The source model uses integer time. -/
abbrev Time := Int

end AvailableChain
end
