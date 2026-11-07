module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface

public section

/-! # Pending interface of the growing engine endpoints

The collision transport to the canonical growing trace (`Simulation.noCollRun_simTraceAt`, home
`Lemmas/Growing/Simulation`), consumed by the endpoint transports, under its agreed name.
It is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Without an observed hash collision, the canonical growing trace is collision free. -/
theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  sorry

end Consensus.Goldilocks.Simulation

end
