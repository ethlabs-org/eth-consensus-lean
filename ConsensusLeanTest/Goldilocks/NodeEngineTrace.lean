module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.NodeEngine.Regression

public section
namespace Consensus.Goldilocks.NodeEngine
open Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {I B : Type} {O : OutputSchema} [DecidableEq I] [Countable I]
  (A : Family I B) (fin : O.Id → Bool)
  (rho : Model.Run (compiled (shapeFamily A fin)) E) (hn : 1 ≤ Fintype.card V) (D : TraceData)

/-- Separate-module consumer: canonical construction is available without a simulation witness. -/
theorem canonical_initial (y : Fin (Fintype.card V)) :
    (simTraceNodeAt A fin rho hn D).init y = Node.init (nodeAC (E := E) A hn) := rfl

theorem canonical_cut_zero : cutMapNode A fin rho hn D 0 = 0 := rfl

/-- The inherited growing contract remains directly consumable, independent of collisions. -/
theorem local_contract (h : NodeRunAt A fin rho hn D (simTraceNodeAt A fin rho hn D)) :
    Growing.LocalRun (proposer A fin rho hn) (digest A fin rho hn D)
      (honestAt A fin rho) (runWire (E := E) A hn).signer (simTraceNodeAt A fin rho hn D)
      (fun _ => (nodeAC (E := E) A hn).initial) :=
  h.toLocalRun

end Consensus.Goldilocks.NodeEngine
