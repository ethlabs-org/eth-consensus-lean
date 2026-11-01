module
public import AvailableChainEngineV2.Engine.Duty.Run
public import Mathlib.Data.Finset.SDiff -- shake: keep (re-export)
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace AvailableChain.V2.D.Engine
end AvailableChain.V2.D.Engine

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Counts.lean:23.
def faulty [Fintype V] (rho : D.Run V P) : Finset V := Finset.univ \ rho.honest

-- Source: AvailableChainGeneric/Statements/V2/Counts.lean:26.
theorem faulty_def [Fintype V] (rho : D.Run V P) :
    faulty rho = Finset.univ \ rho.honest := rfl

-- DC: Conditions.lean:158; same: Same honest filter; Bool to Prop; GLY r3.19 S098.
-- Source: AvailableChainGeneric/Statements/V2/Counts.lean:32.
def awakeHonest (E : Generic.Env V) (rho : D.Run V P) (t : Time) : Finset V :=
  rho.honest.filter (E.awake · t)

omit [DecidableEq V] in
-- Source: AvailableChainGeneric/Statements/V2/Counts.lean:37.
theorem awakeHonest_def (E : Generic.Env V) (rho : D.Run V P) (t : Time) :
    awakeHonest E rho t = rho.honest.filter (E.awake · t) := rfl

end AvailableChain.Gen.V2.Duty
