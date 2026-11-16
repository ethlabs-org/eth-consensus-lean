module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationDefs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # The healthy repair schedule under growing faults (definitions)

The repair schedule, opening, receiver repair and record cover of a healed run, with honesty read
at the time of each event or observation: a source is honest at its own cut, a proposer `Δ` after
its slot start, a receiver at its update, and blocks are held by nodes honest when they held them
(`HonestBlocksAt`). No honest set is fixed across the run. The schedule, opening, receiver repair
and record cover are stated on any trace with a finite reset record (`RepairSchedule`,
`RepairOpening`, `ReceiverRepair`, `RecordCover`); a healed-safety query's schedule and opening
add its query, the opening's window after it and the reserve before the heal point
(`HealthyRepairScheduleAt`, `HealthyRepairOpeningAt`). Definitions only. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape
open SA (SAParams ReplayOrder Payload)

section Trace

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (proposer : Nat → Fin sp.n)
  (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g b : Time)
  (cm : Time → Finset (Fin sp.n)) (βK : ℚ)

/-- A finite reset with its repair window through the horizon `b`: the clean label of the reset
and an old label at least `2k + 1` past it. -/
structure RepairSchedule where
  resetTime : Time
  deltaF : Time
  reset : Healing.Growing.ResetPremisesUpTo tr H proposer dg g deltaF resetTime b cm βK
  cleanLabel : Nat
  cleanLabel_eq : cleanLabel = Healing.cleanLabel sp resetTime
  oldLabel : Nat
  old_bound : cleanLabel + 2 * sp.k + 1 ≤ oldLabel

variable {tr H proposer dg g b cm βK}

/-- An operational opening: a proposal of the slot's designated proposer, still honest `Δ` after
the slot start, at a slot after the reset's drain, the old label and `ḡ + 4Δ`, with its update
inside the horizon. -/
structure RepairOpening (D : RepairSchedule tr H proposer dg g b cm βK) where
  slot : Nat
  cut : Nat
  block : SA.Blk sp.n (List (FG.Att sp.n))
  drain : Healing.drainTime sp D.resetTime ≤ sp.ts slot
  late : SA.gbar g + 4 * sp.Δ ≤ sp.ts slot
  service : sp.ts slot + 6 * sp.Δ ≤ b
  old_lt : D.oldLabel < slot
  label : block.slot = slot
  proposes : tr.ProposesAt (proposer slot) cut block
  accepts : tr.AcceptAt (proposer slot) cut block
  time : tr.time cut = sp.ts slot
  held : proposer slot ∈ H (sp.ts slot + sp.Δ)

/-- Immediate repair of every receiver honest at the opening's update: its update of the opening's
label, and every record looked up just after it covered by a result or optimistic lock of a node
honest at its own cut, no later than the update and with a label past the old label. -/
def ReceiverRepair (D : RepairSchedule tr H proposer dg g b cm βK) (O : RepairOpening D) : Prop :=
  ∀ y, y ∈ H (sp.ts O.slot + 6 * sp.Δ) → ∃ j ell,
    SA.UpdateAt tr.projAC y j O.slot ell ∧
    tr.time j = sp.ts O.slot + 6 * sp.Δ ∧
    tr.time j ≤ b ∧
    ∀ R, SA.lookup (Node.frame (tr.state y (j + 1)))
      (tr.state y (j + 1)).ac.latestConfirmed = some R →
      ∃ x q s C CV, x ∈ H (tr.time q) ∧
        q ≤ j ∧ tr.time q ≤ tr.time j ∧ D.oldLabel ≤ s ∧
        (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
        Anc (tr.HonestBlocksAt H) R C

variable (tr H)

/-- The record of `y` before cut `n`, read at `t`, is its finalized block or below a result or
optimistic lock of a node honest at its own cut, before `n`, no later than `t`, with a label at
least `2k + 1` past the clean label. -/
def RecordCover (cleanLabel : Nat) (y : Fin sp.n) (n : Nat) (t : Time)
    (R : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  R = (tr.state y n).fg.F ∨ ∃ x q s C CV, x ∈ H (tr.time q) ∧
    q < n ∧ tr.time q ≤ t ∧ cleanLabel + 2 * sp.k + 1 ≤ s ∧
    (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
    Anc (tr.HonestBlocksAt H) R C

variable {tr H}

/-- The receiver repair, without exposing the definition's body. -/
theorem receiverRepair_iff {D : RepairSchedule tr H proposer dg g b cm βK} {O : RepairOpening D} :
    ReceiverRepair D O ↔
      ∀ y, y ∈ H (sp.ts O.slot + 6 * sp.Δ) → ∃ j ell,
        SA.UpdateAt tr.projAC y j O.slot ell ∧
        tr.time j = sp.ts O.slot + 6 * sp.Δ ∧
        tr.time j ≤ b ∧
        ∀ R, SA.lookup (Node.frame (tr.state y (j + 1)))
          (tr.state y (j + 1)).ac.latestConfirmed = some R →
          ∃ x q s C CV, x ∈ H (tr.time q) ∧
            q ≤ j ∧ tr.time q ≤ tr.time j ∧ D.oldLabel ≤ s ∧
            (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
            Anc (tr.HonestBlocksAt H) R C := by
  exact Iff.rfl

/-- The record cover, without exposing the definition's body. -/
theorem recordCover_iff {cleanLabel : Nat} {y : Fin sp.n} {n : Nat} {t : Time}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} :
    RecordCover tr H cleanLabel y n t R ↔
      R = (tr.state y n).fg.F ∨ ∃ x q s C CV, x ∈ H (tr.time q) ∧
        q < n ∧ tr.time q ≤ t ∧ cleanLabel + 2 * sp.k + 1 ≤ s ∧
        (SA.ResultAt tr.projAC x q s C CV ∨ SA.OptimisticLockAt tr.projAC x q s C CV) ∧
        Anc (tr.HonestBlocksAt H) R C := by
  exact Iff.rfl

end Trace

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A query's repair schedule: the trace schedule at the query's canonical run, with its query
after the query's readiness and the reset's drain, and a strict reserve before the heal point
that pays for the opening and its update. -/
structure HealthyRepairScheduleAt (Q : HealthyPreparationQueryAt S A V) extends
    RepairSchedule Q.trace Q.keys (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst Q.bound
      (runCommittee S Q.run.2 Q.hn) (K S A).params.βK where
  query : Time
  lower : max Q.ready (max (Healing.drainTime Q.params resetTime)
    (max (Q.params.ts oldLabel) (max (SA.gbar Q.gst + 4 * Q.params.Δ) 0))) ≤ query
  reserve : query + (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1

/-- A query's operational opening: a trace opening within the progress window after the query. -/
structure HealthyRepairOpeningAt (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) extends RepairOpening D.toRepairSchedule where
  bounded : Q.params.ts slot ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ

end Consensus.Goldilocks.Obligations.Growing

end
