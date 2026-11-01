module
public import AvailableChainGeneric.Statements.V2.Duty.Interface

@[expose] public section

namespace AvailableChain.Gen.V2.Duty

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

-- DC: Interface.lean:58; same: Frozen base; no SA/GridCO evidence; GLY r3.19 S132.
-- Source: AvailableChainGeneric/Statements/V2/Slashing.lean:15.
structure SlashingInterface {V : Type} {In : Type} (P : ProtocolSpecD In)
    extends FinalityInterface P where

  slashes : D.Run V P → V → Prop

variable {V : Type} {In : Type} {P : ProtocolSpecD In}

-- DC: Claims.lean:63; same: Same conclusion; claim premise separate; GLY r3.19 S133.
-- Source: AvailableChainGeneric/Statements/V2/Slashing.lean:27.
def HonestNeverSlashed (I : SlashingInterface (V := V) P) (rho : D.Run V P) : Prop :=
  ∀ v ∈ rho.honest, ¬ I.slashes rho v

-- Source: AvailableChainGeneric/Statements/V2/Slashing.lean:30.
theorem HonestNeverSlashed_def (I : SlashingInterface (V := V) P) (rho : D.Run V P) :
    HonestNeverSlashed I rho = (∀ v ∈ rho.honest, ¬ I.slashes rho v) := rfl

end AvailableChain.Gen.V2.Duty
