module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # The read context of a healthy reader under growing faults (definitions)

The read point of a reader after a repair opening's update (`RepairReadContext`): read at or after
the update, with its read cut after the update's time, and the finite service it reads under: the
read context of healed safety, indexed by the read point `(n, t)` itself (the reader's state
before trace cut `n`, read at its stored clock `t`). The reader is honest, awake and joined at
`t`; the service windows are the static ones of the validators honest at `t` on the prefix through
`t`; the latest view's slot committee's fault bound is charged at `t` against its members awake
and joined at the latest view's voting time. Definitions only. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

open AC (ACParams Payload)

variable {sp : ACParams}
  {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- The read context of `y` at the read point `(n, t)` after the update of the opening `O` of the
repair schedule `D`: `t` is at or after the update time and cut `n` strictly after it. -/
structure RepairReadContext (D : RepairSchedule tr H proposer dg g b cm βK) (O : RepairOpening D)
    (y : Fin sp.n) (n : Nat) (t : Time) where
  label : Nat
  time_nonneg : 0 ≤ t
  time_bound : t ≤ b
  repaired : sp.ts O.slot + 6 * sp.Δ ≤ t
  repairedCut : sp.ts O.slot + 6 * sp.Δ < tr.time n
  readPoint : Regimes.ReadPoint tr n t
  honest : y ∈ H t
  awake : tr.awake y t
  joined : tr.JoinedAt y t
  latest : (label : Int) = (AC.latestView sp (tr.state y n).ac (Node.frame (tr.state y n)) t).2
  reset_le : D.resetTime ≤ sp.ts label
  label_le : sp.ts label + sp.Δ ≤ t
  sync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) D.resetTime t
    (tr.projAC.upTo t)
  catchup : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t))
    D.resetTime (2 * sp.Δ) t
  fault : AC.FaultBoundK (Generic.dictOfTime sp cm) label tr.projAC (H t) (sp.ts label + sp.Δ)

end Consensus.Goldilocks.Obligations.Growing

end
