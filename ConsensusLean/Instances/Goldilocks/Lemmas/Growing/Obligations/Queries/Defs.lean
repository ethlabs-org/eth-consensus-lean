module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers

public section

/-! # Growing-fault engine queries

The queries of the obligations endpoint under growing faults: a valid, collision-free engine run
of the compiled Goldilocks family together with the regime premises and the reader of one claim.
Each is its constant-fault counterpart of `Lemmas/Obligations` without the constant-fault field:

* `ConfirmedQueryAt`: a nonfinal (available or stable) liveness query, in the sleepy or the
  healthy regime, or handing over from the healthy to the sleepy regime;
* `SleepySafetyQueryAt`: a sleepy run, for sleepy safety;
* `FinalQueryAt`: a final liveness query in the healthy regime;
* `HealthyPreparationQueryAt`: a run healthy up to a bound with a nonfinal capability, for healed
  safety;
* `OutageQueryAt`: an outage run, for persistence (`OutageQuery.toAt` forgets the constant-fault
  field of a static query).

Each query reads the engine run on the canonical trace `simTraceAt` with the time-indexed honest
keys `honestKeysAt` (accessors `trace`, `keys`). Definitions only. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A nonfinal liveness query: a valid, collision-free run in the sleepy regime with progress on
the whole run, or in the healthy regime, or handing over to the sleepy regime at a time `T` at or
after the heal point (the regime conjuncts of `System.Handover`: healthy up to `T`, sleepy from
`T`), with progress from readiness and a query time at least
the heal point, and a ready reader at the deadline `query + latency·ΔAC ≤ horizon`. -/
structure ConfirmedQueryAt where
  run : (Sys (goldilocks S) V).Run
  hn : 1 ≤ Fintype.card V
  cap : Capability
  nonfinal : cap = .available ∨ cap = .stable
  index : (K S A).Idx
  gst : Time
  query : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  regime :
    ((Sys (goldilocks S) V).Sleepy (K S A) run ∧
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap index
        0 run.2.horizon run ∧ 0 ≤ query) ∨
    ((Sys (goldilocks S) V).Healthy (K S A) gst run ∧
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap index
        ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run ∧
      (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ query) ∨
    (∃ T, ((Sys (goldilocks S) V).log run).PSync ((Sys (goldilocks S) V).pt run) gst ∧
      ((Sys (goldilocks S) V).pt run).HealthyOn (K S A).params.β gst T ∧
      ((Sys (goldilocks S) V).pt run).env.ΔFG ≤
        ((K S A).params.fgDelay : Time) * ((Sys (goldilocks S) V).pt run).env.ΔAC ∧
      ((Sys (goldilocks S) V).pt run).SleepyOn (K S A).params.θ
        ((Sys (goldilocks S) V).cDur (K S A) run) ((Sys (goldilocks S) V).aheadDur (K S A) run) T
        ((Sys (goldilocks S) V).pt run).horizon ∧
      (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ T ∧
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap index
        ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run ∧
      (Sys (goldilocks S) V).heal (K S A) cap index gst run ≤ query)
  bounded : query + ((K S A).params.latency cap index : Time) * run.1.ΔAC ≤ run.2.horizon
  reader : ∃ v, run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) run) v
    (query + ((K S A).params.latency cap index : Time) * run.1.ΔAC)

namespace ConfirmedQueryAt
variable {S A V}
abbrev params (Q : ConfirmedQueryAt S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : ConfirmedQueryAt S A V) := simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn
noncomputable abbrev keys (Q : ConfirmedQueryAt S A V) := honestKeysAt ⟨S, stock⟩ Q.run.2
noncomputable abbrev duration (Q : ConfirmedQueryAt S A V) :=
  (Sys (goldilocks S) V).cDur (K S A) Q.run
noncomputable abbrev deadline (Q : ConfirmedQueryAt S A V) : Time :=
  Q.query + ((K S A).params.latency Q.cap Q.index : Time) * Q.run.1.ΔAC
end ConfirmedQueryAt

/-- A sleepy safety query: a valid, collision-free sleepy run. No progress, query or reader. -/
structure SleepySafetyQueryAt where
  run : (Sys (goldilocks S) V).Run
  hn : 1 ≤ Fintype.card V
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  sleepy : (Sys (goldilocks S) V).Sleepy (K S A) run

namespace SleepySafetyQueryAt
variable {S A V}
abbrev params (Q : SleepySafetyQueryAt S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : SleepySafetyQueryAt S A V) := simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn
noncomputable abbrev keys (Q : SleepySafetyQueryAt S A V) := honestKeysAt ⟨S, stock⟩ Q.run.2
end SleepySafetyQueryAt

/-- A final liveness query: a valid, collision-free healthy run with final progress from
readiness, a query time at least the final heal point, and a ready reader at the deadline
`query + latency·ΔAC ≤ horizon`. -/
structure FinalQueryAt where
  run : (Sys (goldilocks S) V).Run
  hn : 1 ≤ Fintype.card V
  index : (K S A).Idx
  gst : Time
  query : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  healthy : (Sys (goldilocks S) V).Healthy (K S A) gst run
  progress : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) .final index
    ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run
  mature : (Sys (goldilocks S) V).heal (K S A) .final index gst run ≤ query
  bounded : query + ((K S A).params.latency .final index : Time) * run.1.ΔAC ≤ run.2.horizon
  reader : ∃ v, run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) run) v
    (query + ((K S A).params.latency .final index : Time) * run.1.ΔAC)

namespace FinalQueryAt
variable {S A V}
abbrev params (Q : FinalQueryAt S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : FinalQueryAt S A V) := simTraceAt ⟨S, stock⟩ Q.run.2 Q.hn
noncomputable abbrev keys (Q : FinalQueryAt S A V) := honestKeysAt ⟨S, stock⟩ Q.run.2
noncomputable abbrev deadline (Q : FinalQueryAt S A V) : Time :=
  Q.query + ((K S A).params.latency .final Q.index : Time) * Q.run.1.ΔAC
end FinalQueryAt

/-- A healed-safety query: a valid, collision-free run, healthy up to a bound within the horizon
(partial synchrony from GST, fewer than fraction `β` compromised by the bound, full participation
on `[max gst 0, bound]`, the FG delay within its bound), and a nonfinal capability at an index.
Progress is supplied separately, on `[ready, heal]`. At `bound = horizon` the health premise is
`Healthy`. -/
structure HealthyPreparationQueryAt where
  run : (Sys (goldilocks S) V).Run
  hn : 1 ≤ Fintype.card V
  cap : Capability
  nonfinal : cap = .available ∨ cap = .stable
  index : (K S A).Idx
  gst : Time
  bound : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  bound_le : bound ≤ run.2.horizon
  healthy : ((Sys (goldilocks S) V).log run).PSync ((Sys (goldilocks S) V).pt run) gst ∧
    ((Sys (goldilocks S) V).pt run).HealthyOn (K S A).params.β gst bound ∧
    ((Sys (goldilocks S) V).pt run).env.ΔFG ≤
      ((K S A).params.fgDelay : Time) * ((Sys (goldilocks S) V).pt run).env.ΔAC

namespace HealthyPreparationQueryAt
variable {S A V}
abbrev params (Q : HealthyPreparationQueryAt S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : HealthyPreparationQueryAt S A V) := simTraceAt ⟨S, stock⟩
    Q.run.2 Q.hn
noncomputable abbrev keys (Q : HealthyPreparationQueryAt S A V) := honestKeysAt ⟨S, stock⟩ Q.run.2
noncomputable abbrev heal (Q : HealthyPreparationQueryAt S A V) :=
  (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst Q.run
noncomputable abbrev ready (Q : HealthyPreparationQueryAt S A V) :=
  (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run
noncomputable abbrev cut (Q : HealthyPreparationQueryAt S A V) :=
  cutMap ⟨S, stock⟩ Q.run.2 Q.hn ((chainTrace Q.run.2).endCut Q.heal)
end HealthyPreparationQueryAt

/-- **An outage query under growing faults**: a valid collision-free run with its outage
premise. -/
structure OutageQueryAt (S : BoundSetup) (A : ContractAssumptions S.toSetup) (V : Type)
    [Fintype V] [DecidableEq V] where
  run : (Sys (goldilocksWith S) V).Run
  hn : 1 ≤ Fintype.card V
  T : Time
  start : Time
  stop : Time
  valid : (Sys (goldilocksWith S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  outage : (Sys (goldilocksWith S) V).Outage
    (shapeProgress (goldilocksWith S) V).toExternal (K S.toSetup A) T start stop run

variable {S A V}

/-- A static outage query, with its constant-fault field forgotten. -/
def _root_.Consensus.Goldilocks.Obligations.OutageQuery.toAt (Q : OutageQuery S A V) :
    OutageQueryAt ⟨S, stock⟩ A V :=
  ⟨Q.run, Q.hn, Q.T, Q.start, Q.stop, Q.valid, Q.noCollision, Q.outage⟩

namespace OutageQueryAt
variable {S : BoundSetup} {A : ContractAssumptions S.toSetup}
abbrev params (Q : OutageQueryAt S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : OutageQueryAt S A V) := simTraceAt S Q.run.2 Q.hn
noncomputable abbrev keys (Q : OutageQueryAt S A V) := honestKeysAt S Q.run.2
noncomputable abbrev duration (Q : OutageQueryAt S A V) :=
  (Sys (goldilocksWith S) V).cDur (K S.toSetup A) Q.run
end OutageQueryAt

end Consensus.Goldilocks.Obligations.Growing

end
