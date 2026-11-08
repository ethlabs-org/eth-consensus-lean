module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs

public section

/-! # Timing and finite reset schedules for healthy preparation under growing faults -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The base slot's explicit service and expiry margins, at the original heal deadline. -/
structure HealthyBaseTimingAt (Q : HealthyPreparationQueryAt S A V) where
  slot : Nat
  ready_le : Q.ready ≤ Q.params.ts slot
  records : Q.params.ts slot + 6 * Q.params.Δ ≤ Q.heal
  caches : Q.params.ts (slot + 2 : Nat) ≤ Q.heal
  expiry : Q.params.ts (slot + Q.params.k : Nat) ≤ Q.heal
  service : Q.params.ts (slot + 2 : Nat) + 6 * Q.params.Δ ≤ Q.heal

/-- A finite reset seed and repairing opening, with historical origin honesty at its cut. -/
structure HealthyPreparationScheduleAt (Q : HealthyPreparationQueryAt S A V)
    (W : HealthyBaseTimingAt S A V Q) where
  resetTime : Time
  deltaF : Time
  reset : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
    (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst deltaF resetTime Q.bound
  seedNode : Fin Q.params.n
  seedCut : Nat
  seedLabel : Nat
  seed : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  seed_origin : Healing.Growing.HighOrigin Q.trace Q.keys Q.gst
    seedNode seedCut seedLabel seed
  seed_time : Q.trace.time seedCut ≤ resetTime
  seed_label : seedLabel ≤ Q.params.slot resetTime
  query : Time
  lower : max Q.ready (max (Healing.drainTime Q.params resetTime)
    (max (Q.params.ts W.slot) (max (SA.gbar Q.gst + 4 * Q.params.Δ)
      (max 0 (Q.params.ts (seedLabel + 1 : Nat)))))) ≤ query
  reserve : query + (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1

end Consensus.Goldilocks.Obligations.Growing

end
