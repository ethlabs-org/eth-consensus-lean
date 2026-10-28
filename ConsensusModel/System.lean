module
public import ConsensusProblem
public import ConsensusModel.Evidence

@[expose] public section

/-! # The model as a system of the consensus problem (L1)

`sysOf O F V` is the `Consensus.System` of family `F` (with output schema `O`)
and validators `V`: its schema is `O`; its runs
are pairs of an environment and a run in it; valid runs are valid executions;
reads are the protocol's output ledgers at event cuts; the communication log is
the engine's releases and deliveries (tagged with the environment) and the
inboxes (`sysOf_log_faithful`); evidence is objects seen;
conviction is slashability under the protocol's rule; the excuse is an observed
hash collision. All are definitions: the model fixes the meaning of every field
that the problem layer leaves abstract. -/

namespace Consensus.Model


variable {V : Type} [Fintype V] [DecidableEq V]

/-- The system of family `F`. Reducible by unfolding: `(sysOf O F V).schema`
is `O` by definition. -/
def sysOf (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V] :
    Consensus.System V where
  schema := O
  Run := Σ E : Env V, Run F E
  trace r := ⟨r.2.point, r.2.events.length, r.2.cutTime, r.2.readIdx⟩
  Valid r := r.2.ExecutionValid
  Obs := Σ E : Env V, (protoOf F E).Object
  log r := ⟨fun v m t => ∃ o, m = ⟨r.1, o⟩ ∧ r.2.releases v o t,
    fun v m t => ∃ o, m = ⟨r.1, o⟩ ∧ r.2.receives v o t, r.2.inbox⟩
  view r v i := {o | ∃ o' ∈ r.2.ViewIdx v i, o = ⟨r.1, o'⟩}
  convicts r A x := r.2.Slashable {o' | ⟨r.1, o'⟩ ∈ A} x
  Excuse r := r.2.HashCollision

/-- The execution profile of the model: the execution model fixes partial
synchrony and synchrony up to a time; the shape supplies `progress`. -/
def modelProfile (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V]
    {Prog : Type} (progress : Prog → Time → Time → (sysOf O F V).Run → Prop) :
    ExecProfile (sysOf O F V) Prog :=
  ⟨fun r => r.2.PartialSynchrony, fun b r => r.2.HealthyPrefixDelivery b, progress⟩

end Consensus.Model

end
