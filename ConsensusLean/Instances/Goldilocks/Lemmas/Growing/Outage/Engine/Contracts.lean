module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy

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
  `g ≤ t_m + Δ` by a node honest at it holds every slot-`m` vote of a node honest at its cast.

and the sleepy results it consumes, under the names agreed with the sleepy layer:

* `Compose.Growing.sleepy_invariant_at`: the finite service and the two count shapes through
  `b ≥ 0` give the Sleepy record invariant up to `b`;
* `Compose.Growing.confirmed_read_on_chain_at`: under the invariant up to `b`, the confirmed
  read of a node honest at a read time `t ≤ b` (every earlier cut at a time `≤ t`) is held while
  honest and on the chain of the origins within `b`;
* `Obligations.Growing.sleepy_bounds_at`: the L0 sleepy budget with look-ahead `5Δ` on `[0, b]`,
  `b ≤ horizon`, gives the two count shapes through `b` on the canonical trace. -/

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

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

theorem sleepy_invariant_at {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {ΔF b : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBounds tr H b) :
    SleepyInvariantUpTo tr H b := by
  sorry

theorem confirmed_read_on_chain_at {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {b : Time}
    (hinv : SleepyInvariantUpTo tr H b)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t) (htb : t ≤ b)
    (hy : y ∈ H t) (u : Time) :
    (goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) u ∈
        tr.HonestBlocksAt H ∧
      OnOriginChainWithin tr H
        ((goldilocksNode sp ro).confirmed (tr.state y i).ac (Node.frame (tr.state y i)) u) b := by
  sorry

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

theorem sleepy_bounds_at (hv : rho.ExecutionValid) {b : Time} (hb : b ≤ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 b) :
    Compose.Growing.SleepyBounds (simTraceAt S rho hn) (honestKeysAt S rho) b := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
