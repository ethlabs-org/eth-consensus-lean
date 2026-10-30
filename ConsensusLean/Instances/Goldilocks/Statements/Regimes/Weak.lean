module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Healed

@[expose] public section

/-! # Goldilocks milestone Regimes: the weak-continuation rows R.6 (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)" (main `5f3adb28`), row R.6 (`weakSafe`, `weakCrossNest`, `weakInclude`, `weakGrow`;
uses R.1–R.3), with the premise `Weak` of the claims' premises table: healthy up to the heal point,
sleepy after it (the target's `WeakPremise`, with no proposer recurrence after the heal point).

**The heal point is a parameter `T ≥ T_heal`**, as for R.3 (docs/decisions.md, "Goldilocks
instance"): R.6 at the target's `gHeal` stays open. The healing premises are those of R.3 cut at
`T` (`WeakPremises`): `GST(g)`, every honest validator awake on `[ḡ, T]`, `3f ≤ n − 1`, the
ready honest validators more than the faulty ones at every `t ≥ T` (`Sleepy` with `θ = ½` from
`T`, as the target's `SleepyOn`), `NoColl`, the `δ_t` bound, `Catch(2Δ)`, the ready-proposer
premise on `[ḡ, T]` only (`PropPlusUntil`), the reset, H.3 (c)'s bridge (named hypothesis) and
`T ≥ T_heal`; for `weakInclude` and `weakGrow` also H.4's open unanimity premises, as for R.3
(`UnanimousFrom`, `UnanimousWithin`). Premises the target lacks, as for R.3: `Catch(2Δ)`, the
ready-proposer premise (the target has `gProg` on `[gReady, gHeal]`), the `δ_t` bound, and the
unanimity premises. Open proof items: those of R.3, and H.4 and R.3 in a form that needs
`Healthy` and the ready-proposer premise only up to `T` (H.4 is stated under `Healthy(g)` and
`Prop⁺(G_p)` on the whole run).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload gbar)
open Healing (CatchRun ReadyProposal IsReset BridgeAt T_heal)

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- The ready-proposer premise `Prop⁺(G_p)` on `[ḡ, T]`: for every trigger `τ ≥ ḡ` with
`τ + G_p ≤ T`, a ready proposal at a slot start in `[τ, τ + G_p]`. -/
def PropPlusUntil (g Gp T : Time) : Prop :=
  ∀ τ, gbar g ≤ τ → τ + Gp ≤ T → ∃ (s : Nat) (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
    1 ≤ s ∧ τ ≤ sp.ts s ∧ sp.ts s ≤ τ + Gp ∧ ReadyProposal tr H (sp.toParams.proposer s) k s B

/-- **`Weak`** with the healing premises cut at the heal point `T`. -/
structure WeakPremises (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF Gp a Tb T : Time) :
    Prop where
  /-- `GST(g)`. -/
  gst : tr.GSTRun H ΔF g
  /-- Every honest validator is awake on `[ḡ, T]`. -/
  awake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ T → tr.awake y t
  /-- `3f ≤ n − 1`. -/
  faults : 3 * Hᶜ.ncard ≤ sp.n - 1
  /-- From `T` on, the ready honest validators are more than the faulty ones. -/
  sleepyAfter : ∀ t, T ≤ t → Hᶜ.ncard < {y | ReadyAt tr H (catchUp sp) y t}.ncard
  /-- `NoColl`. -/
  noColl : Compose.NoCollRun dg tr
  /-- `δ_t ≥ ⌈(6Δ + Δ_F)/(4Δ)⌉`. -/
  timeoutDelay : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time)
  /-- `Catch(2Δ)`. -/
  catchPremise : CatchRun tr H g (2 * sp.Δ)
  /-- The ready-proposer premise on `[ḡ, T]`. -/
  prop : PropPlusUntil tr H g Gp T
  /-- `a` is the reset `a_z`. -/
  reset : IsReset tr H g a
  /-- `T_b ≥ 0`. -/
  offset : 0 ≤ Tb
  /-- H.3 (c)'s bridge for the reset and `T_b` (named hypothesis). -/
  bridge : BridgeAt tr H g a Tb
  /-- The heal point is at or after `T_heal`. -/
  late : T_heal sp g ΔF Gp Tb ≤ T

end Defs

/-- **R.6, `weakSafe`.** Under `Weak` with heal point `T ≥ T_heal`: ready-reader safety of the
confirmed output at every read point from `T` on. -/
def WeakSafe : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T →
    ∀ t₁, ReadySafeOn tr H (catchUp sp) T t₁

/-- **R.6, `weakCrossNest`.** Under `Weak`: from `T` on, every ready finalized read is an ancestor
of every ready confirmed read at the same time. -/
def WeakCrossNest : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T →
    ∀ t x y i j, T ≤ t → ReadPoint tr i t → ReadPoint tr j t →
      Boundary tr x i → Boundary tr y j →
      ReadyAt tr H (catchUp sp) x t → ReadyAt tr H (catchUp sp) y t →
      Anc (tr.HonestBlocks H) (tr.state x i).fg.F (readAfter tr y j t)

/-- **R.6, `weakInclude`.** Under `Weak` and unanimity from `T` (H.4's open `(U_all)` form, as
`IncludeHealed`): every honest proposal released at `τ ≥ T + 8Δ` by a
proposer ready at `τ` is in the confirmed read of every node ready at `t`, for every
`t ≥ τ + 6Δ`. -/
def WeakInclude : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T → UnanimousFrom tr H T →
    ∀ τ P, T + 8 * sp.Δ ≤ τ → ReadyProposalAt tr H (catchUp sp) τ P →
      ∀ y t j, τ + 6 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t → CutAfter tr j t →
        Anc (tr.HonestBlocks H) P (readAfter tr y j t)

/-- **R.6, `weakGrow`.** Under `Weak`, unanimity within `4k'Δ` from `T` (H.4's open `(U_B)` form, as
`GrowHealed`) and one honest ready proposer in every window of `k' ≥ 1`
slots from `T` up to the read time: for every `t ≥ T` with a node ready at `t + D`,
`D = (4k' + 6)Δ`, some honest proposal released at `τ > t` by a proposer ready at `τ` is a new
common confirmed entry at `t + D` above every ready read at `t` (as `GrowSleepy`). -/
def WeakGrow : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time) (k : Nat),
    GoldilocksRun dg H tr → WeakPremises tr H dg g ΔF Gp a Tb T → 1 ≤ k →
    UnanimousWithin tr H T (4 * k * sp.Δ) →
    ∀ t, T ≤ t → ProposerRecurrence tr H (catchUp sp) k T (t + (4 * k + 6) * sp.Δ) →
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

/-- The weak-continuation rows of milestone Regimes (R.6, at a heal point `T ≥ T_heal`). -/
structure WeakStatements : Prop where
  weakSafe : WeakSafe
  weakCrossNest : WeakCrossNest
  weakInclude : WeakInclude
  weakGrow : WeakGrow

end Consensus.Goldilocks.Regimes

end
