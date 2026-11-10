module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.NodeEngine.Representation
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.NodeEngine.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs

@[expose] public section
namespace Consensus.Goldilocks.NodeEngine.Concrete
open AsChainShape (Setup Out)

def traceData : TraceData := ⟨AsChainShape.taggedRoot⟩

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (Shape.compiled (AsChainShape.goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Exact canonical equality, not existence of a trace with a matching contract. -/
def TraceRegression : Prop :=
  simTraceNodeAt (O := AsChainShape.schema) (family S)
    (fun | Out.finalized => true | .confirmed => false)
    (reshape S rho) hn traceData = Simulation.simTraceAt S rho hn

def CutMapRegression : Prop :=
  cutMapNode (O := AsChainShape.schema) (family S)
    (fun | Out.finalized => true | .confirmed => false)
    (reshape S rho) hn traceData = Simulation.cutMap S rho hn

/-- Engine representation is fieldwise; it includes every durable queue and stored clock. -/
def StateRegression : Prop := rho.ExecutionValid → ∀ v i, i ≤ rho.events.length →
  v ∉ rho.faultyAt (rho.cutTime i) →
  engineState (O := AsChainShape.schema) (family S)
    (fun | Out.finalized => true | .confirmed => false)
    (reshape S rho) hn v i = view S (Model.pubOf E) hn (Simulation.stateAt S rho hn v i)

end Consensus.Goldilocks.NodeEngine.Concrete
