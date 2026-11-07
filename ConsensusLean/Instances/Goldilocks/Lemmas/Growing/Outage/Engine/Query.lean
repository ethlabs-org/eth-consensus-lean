module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Contracts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers
import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace

public section

/-! # Outage engine part under growing faults: the query and its network inputs

`OutageQueryAt` packages a valid collision-free engine run and its outage premise, with no
constant-fault field: the trace is `simTraceAt` and the honest set is `honestKeysAt` (the keys
uncompromised at each time). `OutageQuery.toAt` forgets the constant-fault field of a static
query.

* `outage_pre_service_at`: the finite Sleepy service through the outage start, saturating at
  the engine horizon;
* `outage_psync_at`: the engine's partial synchrony from the outage stop;
* `outage_receiver_service_at`: every receiver gets the receiver service after the stop;
* `outage_pool_delivery_query_at`: an update of a restored label, by a node honest at it, holds
  every vote of that slot by a node honest at its cast. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- **An outage query under growing faults**: a valid collision-free run with its outage
premise. -/
structure OutageQueryAt where
  run : (Sys (goldilocks S) V).Run
  hn : 1 ≤ Fintype.card V
  T : Time
  start : Time
  stop : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  outage : (Sys (goldilocks S) V).Outage (K S A) T start stop run

variable {S A V}

/-- A static outage query, with its constant-fault field forgotten. -/
def _root_.Consensus.Goldilocks.Obligations.OutageQuery.toAt (Q : OutageQuery S A V) :
    OutageQueryAt S A V :=
  ⟨Q.run, Q.hn, Q.T, Q.start, Q.stop, Q.valid, Q.noCollision, Q.outage⟩

namespace OutageQueryAt
abbrev params (Q : OutageQueryAt S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : OutageQueryAt S A V) := simTraceAt S Q.run.2 Q.hn
noncomputable abbrev keys (Q : OutageQueryAt S A V) := honestKeysAt S Q.run.2
noncomputable abbrev duration (Q : OutageQueryAt S A V) :=
  (Sys (goldilocks S) V).cDur (K S A) Q.run
end OutageQueryAt

/-- A call of the trace is at or before the engine horizon. -/
theorem OutageQueryAt.call_le_horizon (Q : OutageQueryAt S A V) {y : Fin (Fintype.card V)}
    {j : Nat} (hj : Q.trace.IsCall y j) : Q.trace.time j ≤ Q.run.2.horizon := by
  obtain ⟨l, hl⟩ := hj
  exact simTraceAt_labelled_time_le S Q.run.2 Q.hn Q.valid (by rw [hl.2]; simp)

/-- **Pre-outage service through the start**, saturating at the finite engine horizon: only
labelled recipient cuts require service. -/
theorem outage_pre_service_at (Q : OutageQueryAt S A V) :
    Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start := by
  let b := min Q.start Q.run.2.horizon
  have h0 : Q.run.2.log.SyncUntil Q.run.2.point Q.start :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.2.1.1
  have hnet : Q.run.2.log.SyncUntil Q.run.2.point b :=
    CommLog.Delivers.reindex h0 (f := id) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl)
      (min_le_left _ _)
  have service := sleepyServiceBefore_of_syncUntil_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision)
    (min_le_right Q.start Q.run.2.horizon) hnet
  refine ⟨service.deltaF, ?_, ?_, ?_⟩
  · intro x i m hx hi h0 y j l hy hj hb hd
    exact service.message x i m hx hi h0 y j l hy hj
      (le_min hb (hd.trans (Q.call_le_horizon ⟨_, Compose.projAC_callAt.mp hj⟩))) hd
  · intro x i B hx hi h0 y j l hy hj hb hd hF
    exact service.acRelay x i B hx hi h0 y j l hy hj
      (le_min hb (hd.trans (Q.call_le_horizon ⟨_, Compose.projAC_callAt.mp hj⟩))) hd hF
  · intro x i B hx hi h0 y j hy hj hb hd hF
    exact service.relay x i B hx hi h0 y j hy hj
      (le_min hb (hd.trans (Q.call_le_horizon hj))) hd hF

/-- PSync from the outage's stop on the engine log. -/
theorem outage_psync_at (Q : OutageQueryAt S A V) : Q.run.2.log.PSync Q.run.2.point Q.stop :=
  (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.2.1.2

/-- **The receiver service after the stop**, for every receiver. -/
theorem outage_receiver_service_at (Q : OutageQueryAt S A V) (y : Fin (Fintype.card V)) :
    Compose.Growing.ReceiverServiceAfterAt Q.keys (Q.trace.HonestBlocksAt Q.keys) Q.stop y
      Q.trace.projAC :=
  receiverServiceAfterAt_of_psync S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) (outage_psync_at Q) y

/-- **Post-stop pool delivery**: an update of a slot `m` with `b₁ ≤ t_m + Δ`, by a node honest at
it, holds every slot-`m` vote of a node honest at its cast. -/
theorem outage_pool_delivery_query_at (Q : OutageQueryAt S A V) :
    ∀ w c m ℓ, w ∈ Q.keys (Q.trace.time c) → SA.UpdateAt Q.trace.projAC w c m ℓ →
      Q.stop ≤ Q.params.ts m + Q.params.Δ →
      ∀ x i e, x ∈ Q.keys (Q.trace.time i) → SA.VoteAt Q.trace.projAC x i e → e.msg.slot = m →
        e.msg ∈ (Q.trace.state w c).ac.pool m :=
  outage_pool_delivery_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) (outage_psync_at Q)

end Consensus.Goldilocks.Obligations.Growing

end
