module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run

@[expose] public section

/-! # Goldilocks milestone Regimes: the sleepy rows (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)" (main `5f3adb28`; R.1/R.2 unchanged since `c6653258`), rows R.1 and R.2, over the
Goldilocks run (`GoldilocksRun`, `Compose.NoCollRun`) under `Sleepy` (`SleepyRun`: `Sync[0, ∞)` and
`f < h_t` at the slot points):

* **R.1** (`sleepySafe`, `confirmed_safe_sleepy`; uses A1.2–A1.4, A1.6, C1.1, F.4):
  ready-reader safety of the confirmed output: the confirmed reads of two honest nodes ready at
  their cuts are compatible, and a node's confirmed reads at two cuts where it is ready only
  extend (`SleepySafe`). The prefix form `confirmed_safe_sleepy_prefix` has no node-level row:
  it is the generic prefix result of a good protocol, which the family gets through its
  acceptance.
* **R.2** (`sleepyLive`, `includeSleepy`, `growSleepy`, `confirmed_txLive_sleepy`; uses A1.7,
  F.4): every honest proposal released at `τ` by a ready proposer is in every ready confirmed read
  from `τ + 6Δ` on (`IncludeSleepy`); and with one honest ready proposer in every window of `k`
  slots, joint strict growth of the confirmed output by `t + (4k + 6)Δ` (`GrowSleepy`).

**Vocabulary.** A node is **ready** at `t` (catch-up `c = 18Δ` in the protocol's `Δ`, `sp.Δ`; at
the Refinement's `Δp = Δe` this is `18Δe`, the target's `gc`) when it is
honest and awake throughout `[max(0, t − c − 1), t]` (`ReadyAt`, the model's `Point.Ready`). A
**read** of `y` is its confirmed output at a read point `(j, t)` (`ReadPoint`: the state before cut
`j` is the state at `t`), evaluated at `t` (`readAfter`); at `t = time j` this is `confirmedAt y j`,
and with `CutAfter j t` it is the read after all events at `t` (the model's end-of-time cut).
`CutAfter` restates `Healing.FirstCutAfter` so that the regimes do not import the Healing files.
`ProposerRecurrence c k a b`: every window of `k` consecutive slots whose first slot starts after
`a` and whose last slot starts by `b` has a slot whose proposer is honest and ready at its
start (the target's `gProg` at `k`).

The transaction rows (`confirmed_txLive_sleepy`) are not stated over the run: the run model has no
transactions. They follow, in the Refinement, from `IncludeSleepy` and the proposals' payloads.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

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

/-- The catch-up `c = 18Δ` in the protocol's `Δ` (`sp.Δ`; at the Refinement's `Δp = Δe` it is
`18Δe`, the target's `gc`). -/
def catchUp (sp : SAParams) : Time := 18 * sp.Δ

/-- `y` is ready at `t` with catch-up `c`: honest and awake throughout `[max(0, t − c − 1), t]`. -/
def ReadyAt (c : Time) (y : Fin sp.n) (t : Time) : Prop :=
  y ∈ H ∧ ∀ τ, max 0 (t - c - 1) ≤ τ → τ ≤ t → tr.awake y τ

/-- The confirmed output of `y` in its state before cut `j`, read at the time `t`. -/
noncomputable def readAfter (y : Fin sp.n) (j : Nat) (t : Time) :
    SA.Blk sp.n (List (FG.Att sp.n)) :=
  (goldilocksNode sp ro).confirmed (tr.state y j).ac (Node.frame (tr.state y j)) t

/-- `P` is an honest proposal released at `τ` by a proposer ready at `τ` (catch-up `c`). -/
def ReadyProposalAt (c τ : Time) (P : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ p kP, ReadyAt tr H c p τ ∧ tr.ProposesAt p kP P ∧ tr.time kP = τ

/-- One honest proposer ready at its slot start in every window of `k` consecutive slots whose
first slot starts after `a` and whose last slot starts by `b` (the target's windows
`(t, t + 4kΔ]`). -/
def ProposerRecurrence (proposer : Nat → Fin sp.n) (c : Time) (k : Nat) (a b : Time) : Prop :=
  ∀ s₀ : Nat, a < sp.ts s₀ → sp.ts (s₀ + k - 1 : Nat) ≤ b →
    ∃ s, s₀ ≤ s ∧ s < s₀ + k ∧ ReadyAt tr H c (proposer s) (sp.ts s)

/-- Ready-reader safety of the confirmed output at the read points of times in `[t₀, t₁]` between
the reader's events (`Boundary`):
agreement of the reads of two ready nodes, and monotonicity of a node's reads between two read
points where it is ready. -/
def ReadySafeOn (c t₀ t₁ : Time) : Prop :=
  (∀ y z i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i → Boundary tr z j →
    t₀ ≤ t → t ≤ t₁ → t₀ ≤ t' → t' ≤ t₁ → ReadyAt tr H c y t → ReadyAt tr H c z t' →
    Compatible (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr z j t')) ∧
  ∀ y i j t t', ReadPoint tr i t → ReadPoint tr j t' → Boundary tr y i → Boundary tr y j →
    i ≤ j → t ≤ t' → t₀ ≤ t → t' ≤ t₁ → ReadyAt tr H c y t → ReadyAt tr H c y t' →
    Anc (tr.HonestBlocks H) (readAfter tr y i t) (readAfter tr y j t')

end Defs

/-- **R.1, `sleepySafe` / `confirmed_safe_sleepy`.** Under `Sleepy`, ready-reader safety of the
confirmed output at every read point (catch-up `18Δ`; every bound `t₁`, i.e. on the whole run). -/
def SleepySafe : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr → tr.SleepyRun H ΔF →
    ∀ t₁, ReadySafeOn tr H (catchUp sp) 0 t₁

/-- **R.2, `includeSleepy`.** Under `Sleepy`, every honest proposal released at `τ` by a proposer
ready at `τ` is in the confirmed read of every node ready at `t`, for every `t ≥ τ + 6Δ`. -/
def IncludeSleepy : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr → tr.SleepyRun H ΔF →
    ∀ τ P, ReadyProposalAt tr H (catchUp sp) τ P →
      ∀ y t j, τ + 6 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t → CutAfter tr j t →
        Anc (tr.HonestBlocks H) P (readAfter tr y j t)

/-- **R.2, `growSleepy` / `sleepyLive`.** Under `Sleepy` with one honest ready proposer in every
window of `k ≥ 1` slots up to the read time: for every `t ≥ 0` with a node ready at `t + D`, `D =
(4k + 6)Δ`, some honest proposal `P` released at `τ > t` by a proposer ready at `τ` is a new common
entry at
`t + D`: it is in the read at `t + D` of every node ready then, in none of the reads at `t` of the
nodes ready then, and each of those reads is an ancestor of each ready read at `t + D`. -/
def GrowSleepy : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n) (ΔF : Time) (k : Nat),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr → tr.SleepyRun H ΔF → 1 ≤ k →
    ∀ t, 0 ≤ t → ProposerRecurrence tr H proposer (catchUp sp) k 0 (t + (4 * k + 6) * sp.Δ) →
      (∃ v, ReadyAt tr H (catchUp sp) v (t + (4 * k + 6) * sp.Δ)) →
      ∃ τ P, t < τ ∧ ReadyProposalAt tr H (catchUp sp) τ P ∧
        (∀ y j, ReadyAt tr H (catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
          CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
          Anc (tr.HonestBlocks H) P (readAfter tr y j (t + (4 * k + 6) * sp.Δ))) ∧
        ∀ x jx, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
          ¬ Anc (tr.HonestBlocks H) P (readAfter tr x jx t) ∧
          ∀ y j, ReadyAt tr H (catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
            CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
            Anc (tr.HonestBlocks H) (readAfter tr x jx t)
              (readAfter tr y j (t + (4 * k + 6) * sp.Δ))

/-- The sleepy rows of milestone Regimes (R.1, R.2). -/
structure SleepyStatements : Prop where
  sleepySafe : SleepySafe
  includeSleepy : IncludeSleepy
  growSleepy : GrowSleepy

end Consensus.Goldilocks.Regimes

end
