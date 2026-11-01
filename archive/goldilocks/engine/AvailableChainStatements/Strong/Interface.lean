module
public import AvailableChainStatements.Generic.Interface

@[expose] public section
namespace AvailableChain.Statements.Generic

/-- An additional persistent output. There is no unconditional order
between this output and either base output. -/
structure StrongInterface {n : Nat} (P : AvailableChain.Generic.ProtocolSpec n)
    extends Interface P where
  strong : P.State → Block

end AvailableChain.Statements.Generic
end
