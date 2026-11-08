module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationDefs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # The healthy repair schedule under growing faults (definitions)

The repair schedule, opening, receiver repair and record cover of a healed-safety query, each
the counterpart of `Lemmas/Obligations/HealedSafetyConditional` and `HealedSafety` with honesty
read at the time of each event or observation: a source is honest at its own cut, a proposer or
receiver at its readiness time, and blocks are held by nodes honest when they held them
(`HonestBlocksAt`). No honest set is fixed across the run. Definitions only. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- A finite reset with its repair window: the window pays for the opening and its update, with
a strict reserve before the heal point. -/
structure HealthyRepairScheduleAt (Q : HealthyPreparationQueryAt S A V) where
  resetTime : Time
  deltaF : Time
  reset : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
    (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst deltaF resetTime Q.bound
  cleanLabel : Nat
  cleanLabel_eq : cleanLabel = Healing.cleanLabel Q.params resetTime
  duration_bound : 18 * Q.params.Δ ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run
  oldLabel : Nat
  old_bound : cleanLabel + 2 * Q.params.k + 1 ≤ oldLabel
  query : Time
  lower : max Q.ready (max (Healing.drainTime Q.params resetTime)
    (max (Q.params.ts oldLabel) (max (SA.gbar Q.gst + 4 * Q.params.Δ) 0))) ≤ query
  reserve : query + (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1

/-- An operational opening: a proposal of a proposer ready at its slot start and still honest
`Δ` later (the progress recurrence's proposer hold `1`, which keeps the slot's honest votes on
the proposal), after the query and within the progress window. -/
structure HealthyRepairOpeningAt (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) where
  slot : Nat
  cut : Nat
  block : SA.Blk Q.params.n (List (FG.Att Q.params.n))
  fresh : D.query < Q.params.ts slot
  bounded : Q.params.ts slot ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ
  old_lt : D.oldLabel < slot
  label : block.slot = slot
  proposes : Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn slot) cut block
  accepts : Q.trace.AcceptAt (runProposer S Q.run.2 Q.hn slot) cut block
  time : Q.trace.time cut = Q.params.ts slot
  ready : Regimes.Growing.ReadyAt Q.trace Q.keys
    ((Sys (goldilocks S) V).cDur (K S A) Q.run)
    (runProposer S Q.run.2 Q.hn slot) (Q.params.ts slot)
  held : runProposer S Q.run.2 Q.hn slot ∈ Q.keys (Q.params.ts slot + Q.params.Δ)

/-- Immediate repair of every receiver ready at the opening's update: its update of the opening's
label, and every record looked up just after it covered by a result or optimistic lock of a node
honest at its own cut, no later than the update and with a label past the old label. -/
def HealthyReceiverRepairAt (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) (O : HealthyRepairOpeningAt S A V Q D) : Prop :=
  ∀ y, Regimes.Growing.ReadyAt Q.trace Q.keys
      ((Sys (goldilocks S) V).cDur (K S A) Q.run) y
      (Q.params.ts O.slot + 6 * Q.params.Δ) → ∃ j ell,
    SA.UpdateAt Q.trace.projAC y j O.slot ell ∧
    Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ ∧
    Q.trace.time j ≤ Q.bound ∧
    ∀ R, SA.lookup (Node.frame (Q.trace.state y (j + 1)))
      (Q.trace.state y (j + 1)).ac.latestConfirmed = some R →
      ∃ x q s C CV, x ∈ Q.keys (Q.trace.time q) ∧
        q ≤ j ∧ Q.trace.time q ≤ Q.trace.time j ∧ D.oldLabel ≤ s ∧
        (SA.ResultAt Q.trace.projAC x q s C CV ∨
          SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
        Anc (Q.trace.HonestBlocksAt Q.keys) R C

/-- The record of `y` before cut `n`, read at `t`, is its finalized block or below a result or
optimistic lock of a node honest at its own cut, before `n`, no later than `t`, with a label at
least `2k + 1` past the clean label. -/
def HealthyRecordCoverAt (Q : HealthyPreparationQueryAt S A V) (cleanLabel : Nat)
    (y : Fin Q.params.n) (n : Nat) (t : Time)
    (R : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  R = (Q.trace.state y n).fg.F ∨ ∃ x q s C CV, x ∈ Q.keys (Q.trace.time q) ∧
    q < n ∧ Q.trace.time q ≤ t ∧ cleanLabel + 2 * Q.params.k + 1 ≤ s ∧
    (SA.ResultAt Q.trace.projAC x q s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
    Anc (Q.trace.HonestBlocksAt Q.keys) R C

variable {S A V}

/-- The receiver repair, without exposing the definition's body. -/
theorem healthyReceiverRepairAt_iff {Q : HealthyPreparationQueryAt S A V}
    {D : HealthyRepairScheduleAt S A V Q} {O : HealthyRepairOpeningAt S A V Q D} :
    HealthyReceiverRepairAt S A V Q D O ↔
      ∀ y, Regimes.Growing.ReadyAt Q.trace Q.keys
          ((Sys (goldilocks S) V).cDur (K S A) Q.run) y
          (Q.params.ts O.slot + 6 * Q.params.Δ) → ∃ j ell,
        SA.UpdateAt Q.trace.projAC y j O.slot ell ∧
        Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ ∧
        Q.trace.time j ≤ Q.bound ∧
        ∀ R, SA.lookup (Node.frame (Q.trace.state y (j + 1)))
          (Q.trace.state y (j + 1)).ac.latestConfirmed = some R →
          ∃ x q s C CV, x ∈ Q.keys (Q.trace.time q) ∧
            q ≤ j ∧ Q.trace.time q ≤ Q.trace.time j ∧ D.oldLabel ≤ s ∧
            (SA.ResultAt Q.trace.projAC x q s C CV ∨
              SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
            Anc (Q.trace.HonestBlocksAt Q.keys) R C := Iff.rfl

/-- The record cover, without exposing the definition's body. -/
theorem healthyRecordCoverAt_iff {Q : HealthyPreparationQueryAt S A V} {cleanLabel : Nat}
    {y : Fin Q.params.n} {n : Nat} {t : Time} {R : SA.Blk Q.params.n (List (FG.Att Q.params.n))} :
    HealthyRecordCoverAt S A V Q cleanLabel y n t R ↔
      R = (Q.trace.state y n).fg.F ∨ ∃ x q s C CV, x ∈ Q.keys (Q.trace.time q) ∧
        q < n ∧ Q.trace.time q ≤ t ∧ cleanLabel + 2 * Q.params.k + 1 ≤ s ∧
        (SA.ResultAt Q.trace.projAC x q s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
        Anc (Q.trace.HonestBlocksAt Q.keys) R C := Iff.rfl

end Consensus.Goldilocks.Obligations.Growing

end
