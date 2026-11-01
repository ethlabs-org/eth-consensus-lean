module
public import AvailableChainEngineV2.Engine.Duty.Spec

@[expose] public section

namespace AvailableChain.V2.D

/-- At one time, at most one due duty uses each signing label. -/
def DutiesInjectiveAt {In : Type} (P : ProtocolSpecD In) (t : Time) : Prop :=
  ∀ d d', P.actTime d = t → P.actTime d' = t →
    P.signLabel d = P.signLabel d' → d = d'

end AvailableChain.V2.D
