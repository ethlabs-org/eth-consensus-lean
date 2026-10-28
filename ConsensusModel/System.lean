module
public import ConsensusProblem.Claims
public import ConsensusModel.Evidence

@[expose] public section

/-! # The model as a system of the consensus problem (layer ½)

`sysOf F V` is the `Consensus.System` of family `F` with validators `V`: its runs
are pairs of an environment and a run in it; valid runs are valid executions;
reads are the protocol's output ledgers at event cuts; evidence is objects seen;
conviction is slashability under the protocol's rule; the excuse is an observed
hash collision. All are definitions: the model fixes the meaning of every field
that the problem layer leaves abstract. -/

namespace Consensus.Model

open AvailableChain (Time)
open AvailableChain.Generic (Env)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The system of family `F`. -/
def sysOf (F : Family) (V : Type) [Fintype V] [DecidableEq V] : Consensus.System V where
  Run := Σ E : Env V, Run F E
  env r := ⟨r.2.honest, r.2.horizon, r.1.Δ, r.1.t_GST, r.1.awake, r.2.submit⟩
  Valid r := r.2.ExecutionValid
  cuts r := r.2.events.length
  cutTime r := r.2.cutTime
  read r g v i := r.2.readIdx g v i
  Obs := Σ E : Env V, (protoOf F E).Object
  view r v i := {o | ∃ o' ∈ r.2.ViewIdx v i, o = ⟨r.1, o'⟩}
  convicts r A x := r.2.Slashable {o' | ⟨r.1, o'⟩ ∈ A} x
  Excuse r := r.2.HashCollision

end Consensus.Model

end
