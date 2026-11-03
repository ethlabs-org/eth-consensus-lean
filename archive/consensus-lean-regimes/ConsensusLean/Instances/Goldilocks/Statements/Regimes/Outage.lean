module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy

@[expose] public section

/-! # Goldilocks milestone Regimes: the outage rows R.5 (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)" (main `5f3adb28`), row R.5 (`persists` / `confirmed_persists`, `outageWindow`,
`outage_final_compatible`; uses A1.2, A1.3, C1.1, and the budget (V) with the lock lifetime
`(4k − 2)Δ`), with the premise `Outage(T, b₀, b₁)` of the claims' premises table: synchrony before
`b₀`, GST `b₁`, the participation of the target's outage regime, and (V)
(goldilocks-round-model.tex, "Outage continuation under (V)"):
`b₁ − b₀ + ((b₀ − 6Δ) mod 4Δ) ≤ L` with `L = (4k − 2)Δ`.

**Vocabulary.** `RecentlyAwake η y t`: honest and awake at some time of `[max(0, t − η), t]`.
`EtaSleepyAt c η t` (the target's `EtaReadyAbove` at `θ = ½`): the ready honest validators are
more than half of the ready, the recently awake honest and the faulty ones together.
`ReadyOfAllAt c t` (`cover = ½`): the ready honest validators are more than half of all.
`OutageWindowTimes`: `0 ≤ T`, the arming lag `T + (4k − 4)Δ ≤ b₀` (the target's `lag`, with its
`lockK` the SA's `k`), `b₀ ≤ b₁` and (V). `ResilienceReader c b₀ b₁ w t` (the target's): `w` is
honest and was caught up before the window and awake since (awake on `[max(0, b₀ − c − 1), t]`),
or caught up after it (`b₁ ≤ t − c − 1` and awake on `[t − c − 1, t]`).

Reads are the confirmed (or finalized) outputs after all events at a time (`readAfter`,
`CutAfter`), as in R.2.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload)

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- `y` is honest and awake at some time of `[max(0, t − η), t]`. -/
def RecentlyAwake (η : Time) (y : Fin sp.n) (t : Time) : Prop :=
  y ∈ H ∧ ∃ τ, max 0 (t - η) ≤ τ ∧ τ ≤ t ∧ tr.awake y τ

/-- η-sleepy participation at `t` (`θ = ½`): the ready honest validators are more than half of
the ready, the recently awake honest and the faulty ones together. -/
def EtaSleepyAt (c η t : Time) : Prop :=
  {y | ReadyAt tr H c y t ∨ RecentlyAwake tr H η y t ∨ y ∉ H}.ncard <
    2 * {y | ReadyAt tr H c y t}.ncard

/-- More than half of all validators are ready at `t` (`cover = ½`). -/
def ReadyOfAllAt (c t : Time) : Prop := sp.n < 2 * {y | ReadyAt tr H c y t}.ncard

/-- The resilience reader `w` at `t` for the window `[b₀, b₁)` (catch-up `c`). -/
def ResilienceReader (c b₀ b₁ : Time) (w : Fin sp.n) (t : Time) : Prop :=
  w ∈ H ∧
    ((∀ τ, max 0 (b₀ - c - 1) ≤ τ → τ ≤ t → tr.awake w τ) ∨
      (b₁ ≤ t - c - 1 ∧ ∀ τ, t - c - 1 ≤ τ → τ ≤ t → tr.awake w τ))

end Defs

/-- The outage times with (V): `0 ≤ T`, `T + (4k − 4)Δ ≤ b₀`, `b₀ ≤ b₁`, and
`b₁ − b₀ + ((b₀ − 6Δ) mod 4Δ) ≤ (4k − 2)Δ`. -/
def OutageWindowTimes (sp : SAParams) (T b₀ b₁ : Time) : Prop :=
  0 ≤ T ∧ T + (4 * (sp.k : Time) - 4) * sp.Δ ≤ b₀ ∧ b₀ ≤ b₁ ∧
    b₁ - b₀ + (b₀ - 6 * sp.Δ) % (4 * sp.Δ) ≤ (4 * (sp.k : Time) - 2) * sp.Δ

/-- **`Outage(T, b₀, b₁)`** over the run (η = `eta·Δ`): the outage times with (V), synchrony for the
recipient deadlines `≤ b₀` (including the latest wake), `GST(b₁)`, η-sleepy participation at every
time, and more than half of all validators ready at `b₀`. -/
def OutageRun {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (ΔF : Time) (eta : Nat)
    (T b₀ b₁ : Time) : Prop :=
  OutageWindowTimes sp T b₀ b₁ ∧ tr.SyncBefore H ΔF b₀ ∧ tr.GSTRun H ΔF b₁ ∧
    (∀ t, 0 ≤ t → EtaSleepyAt tr H (catchUp sp) (eta * sp.Δ) t) ∧
    ReadyOfAllAt tr H (catchUp sp) b₀

/-- **R.5, `persists` / `confirmed_persists`.** Under `Outage(T, b₀, b₁)`: what a node ready at
`T` reads as confirmed (after all events at `T`) is an ancestor of the confirmed read of every
resilience reader at every `t ≥ b₀` (after all events at `t`). -/
def OutagePersists : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time) (eta : Nat) (T b₀ b₁ : Time),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr → OutageRun tr H ΔF eta T b₀ b₁ →
    ∀ v jv, ReadyAt tr H (catchUp sp) v T → CutAfter tr jv T →
      ∀ w t j, b₀ ≤ t → ResilienceReader tr H (catchUp sp) b₀ b₁ w t → CutAfter tr j t →
        Anc (tr.HonestBlocks H) (readAfter tr v jv T) (readAfter tr w j t)

/-- **R.5, `outageWindow`.** With the outage times and the window at most the lock lifetime (`b₁ −
b₀ ≤ (4k − 2)Δ`, not (V): this interval row is the interval-only P1 of goldilocks-round-model.tex,
"The lags … and the budget min(η, L) concern interval-only P1"), synchrony for the sends with
deadline `≤ b₀`, η-sleepy participation on `[0, b₀]` only, and more than half ready at `b₀`, and
**no** premise after `b₀`: what a node ready at `T` reads as confirmed is an ancestor of the
confirmed read of every resilience reader at every `t ∈ [b₀, b₁ − 1]`. -/
def OutageWindow : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time) (eta : Nat) (T b₀ b₁ : Time),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr →
    0 ≤ T → T + (4 * (sp.k : Time) - 4) * sp.Δ ≤ b₀ → b₀ ≤ b₁ →
    b₁ - b₀ ≤ (4 * (sp.k : Time) - 2) * sp.Δ → tr.SyncBefore H ΔF b₀ →
    (∀ t, 0 ≤ t → t ≤ b₀ → EtaSleepyAt tr H (catchUp sp) (eta * sp.Δ) t) →
    ReadyOfAllAt tr H (catchUp sp) b₀ →
    ∀ v jv, ReadyAt tr H (catchUp sp) v T → CutAfter tr jv T →
      ∀ w t j, b₀ ≤ t → t ≤ b₁ - 1 → ResilienceReader tr H (catchUp sp) b₀ b₁ w t →
        CutAfter tr j t → Anc (tr.HonestBlocks H) (readAfter tr v jv T) (readAfter tr w j t)

/-- **R.5, `outage_final_compatible`.** Under `Outage(T, b₀, b₁)`: what a node ready at `T` reads
as confirmed is compatible with the finalized read of every resilience reader at every `t ≥ b₀`
(after all events at `t`). -/
def OutageFinalCompatible : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (ΔF : Time) (eta : Nat) (T b₀ b₁ : Time),
    GoldilocksRun proposer dg H tr → Compose.NoCollRun dg tr → OutageRun tr H ΔF eta T b₀ b₁ →
    ∀ v jv, ReadyAt tr H (catchUp sp) v T → CutAfter tr jv T →
      ∀ w t j, b₀ ≤ t → ResilienceReader tr H (catchUp sp) b₀ b₁ w t → CutAfter tr j t →
        Compatible (tr.HonestBlocks H) (readAfter tr v jv T) (tr.state w j).fg.F

/-- The outage rows of milestone Regimes (R.5). -/
structure OutageStatements : Prop where
  persists : OutagePersists
  window : OutageWindow
  finalCompatible : OutageFinalCompatible

end Consensus.Goldilocks.Regimes

end
