module
public import AvailableChainEngineV2.Conditions.Interface

@[expose] public section

/-! The additive finality interface. Source: GLY
`claude-files/a0/generic-layer.md`:1694 (I-1). Step-2 item I25, D17. -/

-- This import does not declare the KitV2 Engine namespace.
-- Register it for the required open list without an unused KitV2 import.
namespace AvailableChain.V2.Engine
end AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- DESIGNED: extend the existing interface by its finalized output only.
GLY:1694 requires the extension for the 2b catalog. The getter's carrier
is Block: P3 `fgsa-f0-f2-plan-r3.5-2a9a5877.md`:1197 identifies F as the
erased finalized block. Consumers: finalized-output properties in F0
and the later catalog. No finality law is part of this read structure.
DC: Interface.lean:29; same: Same getter; additive field; GLY r3.19 S099. -/
structure FinalityInterface {In : Type} (P : ProtocolSpec In) extends Interface P where
  finalized : P.State → Block

end AvailableChain.Gen.V2
