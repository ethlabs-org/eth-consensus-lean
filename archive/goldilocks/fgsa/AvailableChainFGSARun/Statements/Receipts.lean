module
public import AvailableChainFGSARun.Model.Protocol

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The decoded block of a proposal object (plan T7.8). -/
def blockOf? (p : Params) (o : Obj p) : Option Block :=
  match (toWire p o).decode with
  | some (.block _ N) => some N.erase
  | _ => none

end AvailableChain.FGSA.Run
end
