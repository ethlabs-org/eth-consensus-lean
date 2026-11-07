module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.ReceiverService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PoolDelivery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy

public section

/-! # Outage engine part: the engine sleepy results it consumes (stand-ins)

The growing-fault engine sleepy results the outage engine part consumes, stated with their agreed
names and shapes and left open here until the layers that own them prove them; this module is
deleted then, and its importers import the owning modules instead. The simulation inputs (the run
`simTraceAt_goldilocksRun`, `noCollRun_simTraceAt`, `receiverServiceAfterAt_of_psync`,
`outage_pool_delivery_at`), the network input `sleepyServiceBefore_of_syncUntil_at` and the
node layer's `Compose.Growing.sleepy_invariant_at` (`Sleepy/Node/Induction`) are proved in their
own modules and re-exported here.

* `Obligations.Growing.ready_read_cut_at`: for an engine node ready at `t ∈ [0, horizon]`, the
  trace cut of the end-of-`t` engine cut is after `t`, a boundary of the node, with stored clock
  `t`;
* `Obligations.Growing.sleepy_bounds_at`: the L0 sleepy budget with look-ahead `5Δ` on `[0, b]`,
  `b ≤ horizon`, gives the two count shapes through `b` on the canonical trace. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

theorem ready_read_cut_at (hv : rho.ExecutionValid) {c : Time} (hc : 0 ≤ c) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ rho.horizon) (hr : rho.point.Ready c v t) :
    Regimes.CutAfter (simTraceAt S rho hn) (cutMap S rho hn ((chainTrace rho).endCut t)) t ∧
      Regimes.Boundary (simTraceAt S rho hn) (rho.ownKey v)
        (cutMap S rho hn ((chainTrace rho).endCut t)) ∧
      (stateAt S rho hn v ((chainTrace rho).endCut t)).now = t := by
  sorry

theorem sleepy_bounds_at (hv : rho.ExecutionValid) {b : Time} (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 b) :
    Compose.Growing.SleepyBounds (simTraceAt S rho hn) (honestKeysAt S rho) b := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
