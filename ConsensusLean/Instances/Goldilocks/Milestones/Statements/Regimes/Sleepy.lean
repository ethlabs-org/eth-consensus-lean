module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run

@[expose] public section

/-! # Goldilocks milestone Regimes: the sleepy rows (statements)

Transcribed from `specs/goldilocks/tex/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)", rows R.1 and R.2, over the
Goldilocks run (`GoldilocksRun`, `Compose.NoCollRun`) under `Sleepy` (`SleepyRun`: `Sync[0, ∞)` and
`f < h_t` at the slot points):

* **R.1** (`sleepySafe`, `confirmed_safe_sleepy`): retired as a milestone statement; its finite
  form for ready readers up to a horizon is `Regimes.Growing.sleepy_safe_at`. The prefix form
  `confirmed_safe_sleepy_prefix` has no node-level row: it is the generic prefix result of a good
  protocol, which the family gets through its acceptance.
* **R.2** (`sleepyLive`, `includeSleepy`, `growSleepy`, `confirmed_txLive_sleepy`; uses A1.7,
  F.4): stated over a slot committee as `Regimes.Growing.IncludeSleepy` and `GrowSleepy`
  (`Results/Statements/SleepyGrowth`), with the vocabulary below.

**Vocabulary.** A node is **ready** at `t` (catch-up `c = 18Δ` in the protocol's `Δ`, `sp.Δ`; at
the simulation's `Δp = Δe` this is `18Δe`) when it is
honest and awake throughout `[max(0, t − c − 1), t]` (`ReadyAt`, the model's `Point.Ready`). A
**read** of `y` is its confirmed output at a read point `(j, t)` (`ReadPoint`: the state before cut
`j` is the state at `t`), evaluated at `t` (`readAfter`); at `t = time j` this is `confirmedAt y j`,
and with `CutAfter j t` it is the read after all events at `t` (the model's end-of-time cut).
`CutAfter` restates `Healing.FirstCutAfter` so that the regimes do not import the Healing files.
`ProposerRecurrence c k a b`: every window of `k` consecutive slots whose first slot starts after
`a` and whose last slot starts by `b` has a slot whose proposer is honest and ready at its
start.

The transaction rows (`confirmed_txLive_sleepy`) are not stated over the run: the run model has no
transactions. They follow, in the obligations proof, from `Regimes.Growing.IncludeSleepy` and the
proposals' payloads.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open AC (ACParams Payload)

section Defs

variable {sp : ACParams}
  (tr : GoldilocksTrace sp) (H : Set (Fin sp.n))

/-- Cut `j` is the first cut after the time `t` (the state before it is the state after all
events at `t`). -/
def CutAfter (j : Nat) (t : Time) : Prop := (∀ k < j, tr.time k ≤ t) ∧ t < tr.time j

/-- `(j, t)` is a read point: every cut before `j` is at a time `≤ t` and cut `j` is at a time
`≥ t`, so the state before `j` is the state at `t` (before the cuts at `t` when `t = time j`, after
all events at `t` when `t < time j`). -/
def ReadPoint (j : Nat) (t : Time) : Prop := (∀ k < j, tr.time k ≤ t) ∧ t ≤ tr.time j

/-- The state of `y` before cut `j` is between two of its top-level events: cut `j` is not a later
cut (position `≠ 0`) of an event of `y`. Inside an event the state can be one the model never
reads, e.g. after an accepted `fg_on_block` and before its `ac_on_block`. -/
def Boundary (y : Fin sp.n) (j : Nat) : Prop := tr.IsCall y j → tr.pos j = 0

/-- The catch-up `c = 18Δ` in the protocol's `Δ` (`sp.Δ`; at the simulation's `Δp = Δe` it is
`18Δe`). -/
def catchUp (sp : ACParams) : Time := 18 * sp.Δ

/-- `y` is ready at `t` with catch-up `c`: honest and awake throughout `[max(0, t − c − 1), t]`. -/
def ReadyAt (c : Time) (y : Fin sp.n) (t : Time) : Prop :=
  y ∈ H ∧ ∀ τ, max 0 (t - c - 1) ≤ τ → τ ≤ t → tr.awake y τ

/-- The confirmed output of `y` in its state before cut `j`, read at the time `t`. -/
noncomputable def readAfter (y : Fin sp.n) (j : Nat) (t : Time) :
    AC.Blk sp.n (List (FG.Att sp.n)) :=
  (goldilocksNode sp).confirmed (tr.state y j).ac (Node.frame (tr.state y j)) t

/-- `P` is an honest proposal released at `τ` by a proposer ready at `τ` (catch-up `c`). -/
def ReadyProposalAt (c τ : Time) (P : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ p kP, ReadyAt tr H c p τ ∧ tr.ProposesAt p kP P ∧ tr.time kP = τ

/-- One honest proposer ready at its slot start in every window of `k` consecutive slots whose
first slot starts after `a` and whose last slot starts by `b` (in time, the windows
`(t, t + 4kΔ]`). -/
def ProposerRecurrence (proposer : Nat → Fin sp.n) (c : Time) (k : Nat) (a b : Time) : Prop :=
  ∀ s₀ : Nat, a < sp.ts s₀ → sp.ts (s₀ + k - 1 : Nat) ≤ b →
    ∃ s, s₀ ≤ s ∧ s < s₀ + k ∧ ReadyAt tr H c (proposer s) (sp.ts s)

end Defs

end Consensus.Goldilocks.Regimes

end
