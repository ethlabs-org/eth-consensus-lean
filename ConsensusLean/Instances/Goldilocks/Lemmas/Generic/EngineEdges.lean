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

/-- Public-indexed reductions recover the original regime and its existing excuse. -/
theorem holds_of_forall_public {assumption claim : (Sys F V).Run → Prop}
    (h : ∀ pub : Model.Public, (Sys F V).Holds
      (fun r => Model.pubOf r.1 = pub ∧ assumption r) claim) :
    (Sys F V).Holds assumption claim := by
  intro r hv ha
  exact h (Model.pubOf r.1) r hv ⟨rfl, ha⟩

/-- Unconditional claims remain free of an excuse when public restrictions are removed. -/
theorem holdsAlways_of_forall_public {claim : (Sys F V).Run → Prop}
    (h : ∀ pub : Model.Public, (Sys F V).HoldsAlways
      (fun r => Model.pubOf r.1 = pub → claim r)) :
    (Sys F V).HoldsAlways claim := by
  intro r hv
  exact h (Model.pubOf r.1) r hv rfl

end Consensus.Goldilocks.Generic
