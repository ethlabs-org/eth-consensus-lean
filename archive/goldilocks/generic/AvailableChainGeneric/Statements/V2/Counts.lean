module
public import AvailableChainEngineV2.Engine.Run
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Fintype.Defs

@[expose] public section

/-! P3 is `fgsa-f0-f2-plan-r3.5-2a9a5877.md` §4.3.
Step-2 item I04; ruling D11. -/

-- These EngineV2 imports contain no declarations in the KitV2 Engine namespace.
-- Register that namespace for the required open list without a KitV2 import.
namespace AvailableChain.V2.Engine
end AvailableChain.V2.Engine

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

-- P3:1540; [Fintype V] supplies Finset.univ.
def faulty [Fintype V] (rho : Run V P) : Finset V := Finset.univ \ rho.honest

-- P3:1540; equation export required by BUILD §7.2 B3a.
theorem faulty_def [Fintype V] (rho : Run V P) :
    faulty rho = Finset.univ \ rho.honest := by
  rw [faulty]

-- P3:1541.
/-- DC: Conditions.lean:158; same: Same honest filter; Bool to Prop; GLY r3.19 S098. -/
def awakeHonest (E : Generic.Env V) (rho : Run V P) (t : Time) : Finset V :=
  rho.honest.filter (E.awake · t)

-- P3:1541; equation export required by BUILD §7.2 B3a.
omit [DecidableEq V] in
theorem awakeHonest_def (E : Generic.Env V) (rho : Run V P) (t : Time) :
    awakeHonest E rho t = rho.honest.filter (E.awake · t) := by
  rw [awakeHonest]

end AvailableChain.Gen.V2
