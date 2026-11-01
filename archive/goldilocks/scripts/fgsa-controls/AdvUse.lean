import AdvLib
namespace AvailableChain.FGSA
def useLet (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 := GridCO.fixedLet p st r
def useBeta (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 := GridCO.fixedBeta p st r
def usePriv (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 := GridCO.fixedViaPriv p st r
def useIrr (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.genI (cast GridCO.polI_eq GridCO.gridLeasePolicy) p st r
def useEvil (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 := Evil.fixedGate p st r
end AvailableChain.FGSA
