module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # The read context of a healthy reader under growing faults (definitions)

The read point of a reader after the repair window, with the finite service it reads under: the
read context of healed safety, indexed by the read point `(n, t)` itself (the
reader's state before trace cut `n`, read at its stored clock `t`). The reader is honest, awake
and joined at `t`; the service windows are the static ones of the validators honest at `t` on the
prefix through `t`; the fault bound is charged at `t` against the validators awake and joined at
the latest view's voting time. Definitions only. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The read context of `y` at the read point `(n, t)` after the repair window of `D`. -/
structure HealthyReadContextAt (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) (y : Fin Q.params.n) (n : Nat) (t : Time) where
  label : Nat
  time_nonneg : 0 ≤ t
  time_bound : t ≤ Q.bound
  repaired : D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ < t
  readPoint : Regimes.ReadPoint Q.trace n t
  honest : y ∈ Q.keys t
  awake : Q.trace.awake y t
  joined : Q.trace.JoinedAt y t
  latest : (label : Int) = (SA.latestView Q.params (Q.trace.state y n).ac
    (Node.frame (Q.trace.state y n)) t).2
  reset_le : D.resetTime ≤ Q.params.ts label
  label_le : Q.params.ts label + Q.params.Δ ≤ t
  sync : SyncACWindowBefore (Q.keys t) ((Q.trace.upTo t).HonestBlocks (Q.keys t)) D.resetTime t
    (Q.trace.projAC.upTo t)
  catchup : CatchACWindowBefore (Q.trace.projAC.upTo t) (Q.keys t)
    ((Q.trace.upTo t).HonestBlocks (Q.keys t)) D.resetTime (2 * Q.params.Δ) t
  fault : Q.trace.FaultBoundAt Q.keys (Q.params.ts label + Q.params.Δ) t

end Consensus.Goldilocks.Obligations.Growing

end
