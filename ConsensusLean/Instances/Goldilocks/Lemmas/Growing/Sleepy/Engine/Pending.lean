module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Regimes

public section

/-! # Pending interface of the sleepy engine transport

Statements the engine transport consumes whose home modules are not on this branch yet, under
their final names, so that the engine proofs compose against the final interface:

* the canonical growing trace simulates the engine (`Simulation.simTraceAt_simulates`, home
  `Lemmas/Growing/Simulation/Run`);
* the finite sleepy service from raw synchrony through `b`
  (`Simulation.sleepyServiceBefore_of_syncUntil_at`, home in the endpoint's network files).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The canonical growing trace of a valid engine run simulates it, with the cut map `cutMap`. -/
theorem simTraceAt_simulates (hv : rho.ExecutionValid) :
    SimulatesAt S rho hn (simTraceAt S rho hn) (cutMap S rho hn) := by
  sorry

/-- **The finite sleepy service under growing faults** from raw synchrony through its deadline
bound `b ≤ horizon`: senders honest at their sends, recipients honest at their reading calls
(the growing-fault `sleepyServiceBefore_of_syncUntil`). -/
theorem sleepyServiceBefore_of_syncUntil_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {b : Time} (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b) :
    Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b := by
  sorry

end Consensus.Goldilocks.Simulation

end
