module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation

public section

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks Generic
variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V}

variable {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}
def OutputValidityEdge (M : RunMap rho payload) : Prop :=
  ReadRepresentation M → HonestReadTransport M → rho.ExecutionValid →
    ∀ g, OutputValid rho g

end Consensus.Goldilocks.Generic
