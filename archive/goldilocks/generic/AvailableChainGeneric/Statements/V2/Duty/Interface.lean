module
public import AvailableChainEngineV2.Conditions.Duty.Interface

@[expose] public section

namespace AvailableChain.V2.D.Engine
end AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

-- DC: Interface.lean:29; same: Same getter; additive field; GLY r3.19 S099.
-- Source: AvailableChainGeneric/Statements/V2/Interface.lean:24.
structure FinalityInterface {In : Type} (P : ProtocolSpecD In) extends D.Interface P where
  finalized : P.State → Block

end AvailableChain.Gen.V2.Duty
