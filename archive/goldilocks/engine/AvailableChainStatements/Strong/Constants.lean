module
public import AvailableChainStatements.Generic.Constants

@[expose] public section
namespace AvailableChain.Statements.Generic

/-- Constants of the additive companion. The base constants stay separate.
The arming lag is the environment's Δ; persistence has no finite budget. -/
structure StrongConstants where
  faultCap : Nat
  strongDelay : Time

structure StrongConstants.Valid (C : StrongConstants) : Prop where
  delay_nonneg : 0 ≤ C.strongDelay

end AvailableChain.Statements.Generic
end
