module
public import AvailableChainGeneric.Statements.V2.Duty.Linked
public import AvailableChainKitV2.DutyLinked

public section

namespace AvailableChain.Gen.V2.Duty

theorem linked_singleton_statement : LinkedSingletonStatement :=
  AvailableChain.V2.D.Engine.linked_singleton_iff

end AvailableChain.Gen.V2.Duty
