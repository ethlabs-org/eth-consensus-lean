module
public import AvailableChainStatements.Generic.Conditions -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Framework.Kit

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

variable {V : Type} {n : Nat} {P : ProtocolSpec n} [DecidableEq V]

end AvailableChain.Framework.Kit
end
