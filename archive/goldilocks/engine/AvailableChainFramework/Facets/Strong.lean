module
public import AvailableChainFramework.DomainMap
public import AvailableChainStatements.Strong.Interface

@[expose] public section

namespace AvailableChain.Framework

open AvailableChain.Statements.Generic

/-- An instance with the strong output (`StrongInterface`): the facet is a
field, so it is bound once (design §3). -/
structure StrongInstance extends Instance where
  strong : P.State → Block

/-- The strong interface of a strong instance. -/
def StrongInstance.sface (I : StrongInstance) : StrongInterface I.P :=
  { I.iface with strong := I.strong }

/-- The claim domain of strong instances. Its contexts are the v1 contexts of the
base instance. -/
@[reducible] def ClaimDomain.strong : ClaimDomain :=
  ClaimDomain.ofV1 `strong StrongInstance StrongInstance.toInstance

/-- Base claims pull back to strong instances. -/
def DomainMap.strongV1 : DomainMap ClaimDomain.strong ClaimDomain.v1 :=
  DomainMap.ofV1 `strong StrongInstance StrongInstance.toInstance

end AvailableChain.Framework

end
