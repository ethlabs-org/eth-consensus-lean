module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport

public section

/-! # Outage engine part: the simulation contracts it consumes (stand-ins)

The growing-fault simulation results the outage engine part consumes, stated with their agreed
names and shapes and left open here until the simulation layer proves them; this module is
deleted then, and its importers import the simulation modules instead. The run itself,
`simTraceAt_goldilocksRun`, is the simulation layer's (`Simulation/Run`).

* `noCollRun_simTraceAt`: without an engine hash collision the trace has no collision;
* `sleepyServiceBefore_of_syncUntil_at`: synchrony through `b ≤ horizon` gives the finite Sleepy
  service through `b`;
* `receiverServiceAfterAt_of_psync`: partial synchrony from `g` gives every receiver the receiver
  service after `g`;
* `outage_pool_delivery_at`: under partial synchrony from `g`, an update of slot `m` with
  `g ≤ t_m + Δ` by a node honest at it holds every slot-`m` vote of a node honest at its cast. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

theorem noCollRun_simTraceAt (hv : rho.ExecutionValid) (hnc : ¬ rho.HashCollision) :
    Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn) := by
  sorry

theorem sleepyServiceBefore_of_syncUntil_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {b : Time}
    (hbh : b ≤ rho.horizon) (hnet : rho.log.SyncUntil rho.point b) :
    Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b := by
  sorry

theorem receiverServiceAfterAt_of_psync (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {g : Time}
    (hnet : rho.log.PSync rho.point g) (y : Fin (Fintype.card V)) :
    Compose.Growing.ReceiverServiceAfterAt (honestKeysAt S rho)
      ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) g y
      (simTraceAt S rho hn).projAC := by
  sorry

theorem outage_pool_delivery_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {g : Time}
    (hnet : rho.log.PSync rho.point g) :
    ∀ w c m ℓ, w ∈ honestKeysAt S rho ((simTraceAt S rho hn).time c) →
      SA.UpdateAt (simTraceAt S rho hn).projAC w c m ℓ →
      g ≤ (S.params (pubOf E) hn).ts m + (S.params (pubOf E) hn).Δ →
      ∀ x i e, x ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
        SA.VoteAt (simTraceAt S rho hn).projAC x i e → e.msg.slot = m →
        e.msg ∈ ((simTraceAt S rho hn).state w c).ac.pool m := by
  sorry

end Consensus.Goldilocks.Simulation

end
