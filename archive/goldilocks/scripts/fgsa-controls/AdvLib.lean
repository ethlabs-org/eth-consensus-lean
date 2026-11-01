import AvailableChainFGSA
namespace AvailableChain.GridCO
def fixedLet (p : Params) (st : State 1) (r : Nat) : State 1 :=
  let pol := gridLeasePolicy
  @gate pol p 1 .block st r
def fixedBeta (p : Params) (st : State 1) (r : Nat) : State 1 :=
  (fun (pol : LeasePolicy) => @gate pol p 1 .block st r) gridLeasePolicy
private def fixedPriv (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 .block st r
def fixedViaPriv (p : Params) (st : State 1) (r : Nat) : State 1 :=
  fixedPriv p st r
def PolI : Type := LeasePolicy
def genI (pol : PolI) (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate pol p 1 .block st r
theorem polI_eq : LeasePolicy = PolI := rfl
attribute [irreducible] PolI
end AvailableChain.GridCO
namespace Evil
def fixedGate (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) (r : Nat) :
    AvailableChain.GridCO.State 1 :=
  @AvailableChain.GridCO.gate AvailableChain.GridCO.gridLeasePolicy p 1 .block st r
end Evil
