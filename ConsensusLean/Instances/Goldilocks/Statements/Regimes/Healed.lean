module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run

@[expose] public section

/-! # Goldilocks milestone Regimes: the healed rows R.3 (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)" (main `5f3adb28`), row R.3 (`healedSafe`, `includeHealed`, `growHealed`,
`crossNest`, `healthyLive` and `confirmed_txLive_healed` for the available output; uses R.1, R.2,
C1.1, H.4; heal point D1), over the Goldilocks run.

**The heal point is a parameter `T` with `T ≥ T_heal`** (H.4's bound, with H.3 (c)'s offset
`T_b`), not the target's `gHeal = max(g, 0) + (29 + B_H^F(k))Δ`: R.3 at `gHeal` stays open
(docs/decisions.md, "Goldilocks instance", 2026-10-30). The premises are H.4's: the HS shared
premises (`HSShared`, with `Healthy(g)`), `Catch(2Δ)` and `Prop⁺(G_p)`, the reset `a_z` (HR.1,
HR.3); and H.4's open premises, named here as hypotheses: H.3 (c)'s bridge `BridgeAt` for the reset
and `T_b` (open in the claims; conditional paper assembly in workbench#21), and, for the inclusion
and growth rows, unanimity of the honest proposals from `T` (`UnanimousFrom`, the `(U_all)` form)
or in every window of `B` from `T` (`UnanimousWithin`, the `(U_B)` form), used through H.4 (i) per
proposal (open in the claims).

**Premises the target lacks** (the Refinement must discharge them or they stay as conditions):
`Catch(2Δ)` and `Prop⁺(G_p)` (the claims' premises table: the target has no accepted-old-block
catch-up, and `gProg` only on `[gReady, gHeal]` without readiness; bridges B1–B3), and two fields of
`HSShared`: the parameter bound `6Δ + Δ_F ≤ 4Δδ_t` and the genesis root (`no honest restart after
ḡ` follows from `Healthy`, `NoColl` from the target's collision excuse).

**Open proof items** (obligations, not premises): the record transfer after the cut (`RecRet`,
for `HealedSafe`); that a read after all events equals the read after the node's last AC call
(for `IncludeHealed`, which reads after all events at `t`, while H.4 concludes after AC calls; see
the mapping, "Reads between AC calls"); and `CrossNest`, which no H node gives (new R.3 work;
its lagged clause needs the finality cache of `y` to advance on the relayed carrier, through
`updateFinality`'s gates, consensus-lean#104).

The transaction rows (`healthyLive`, `confirmed_txLive_healed`) are not stated over the run (no
transactions there): the Refinement derives them from `IncludeHealed`.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload gbar)
open Healing (HSShared CatchRun PropPlus IsReset BridgeAt T_heal Unanimous HonestProposalRun)

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **Unanimity from `T`** (the `(U_all)` form of H.4 (iii), used through H.4 (i)): every honest
proposal of a slot `p` with `t_p ≥ T` has all honest votes of its slot. -/
def UnanimousFrom (T : Time) : Prop :=
  ∀ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), HonestProposalRun tr H p P → T ≤ sp.ts p →
    Unanimous tr H p P

/-- **Unanimity within `B` from `T`** (the `(U_B)` form of H.4 (ii), used through H.4 (i)): for
every `t ≥ T` there is an honest proposal of a slot `p` with `t ≤ t_p ≤ t + B` that has all honest
votes of its slot. -/
def UnanimousWithin (T B : Time) : Prop :=
  ∀ t, T ≤ t → ∃ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts p ∧
    sp.ts p ≤ t + B ∧ HonestProposalRun tr H p P ∧ Unanimous tr H p P

/-- The healing premises of R.3 with heal point `T`: H.4's premises (`HSShared`, `Catch(2Δ)`,
`Prop⁺(G_p)`), the reset `a` (HR.1), H.3 (c)'s bridge for `a` and an offset `T_b ≥ 0` (a named
hypothesis: open in the claims), and `T ≥ T_heal`. -/
structure HealedPremises (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF Gp a Tb T : Time) :
    Prop where
  /-- The HS shared premises, with `Healthy(g)`. -/
  shared : HSShared tr H dg g ΔF
  /-- `Catch(2Δ)`. -/
  catchPremise : CatchRun tr H g (2 * sp.Δ)
  /-- `Prop⁺(G_p)`. -/
  prop : PropPlus tr H g Gp
  /-- `a` is the reset `a_z`. -/
  reset : IsReset tr H g a
  /-- `T_b ≥ 0`. -/
  offset : 0 ≤ Tb
  /-- H.3 (c)'s bridge for the reset and `T_b` (named hypothesis). -/
  bridge : BridgeAt tr H g a Tb
  /-- The heal point is at or after `T_heal`. -/
  late : T_heal sp g ΔF Gp Tb ≤ T

end Defs

/-- **R.3, `healedSafe`** (heal point `T ≥ T_heal`). Under the healing premises, ready-reader safety
of the confirmed output at every read point from `T` on (catch-up `18Δ`). -/
def HealedSafe : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → HealedPremises tr H dg g ΔF Gp a Tb T →
    ∀ t₁, ReadySafeOn tr H (catchUp sp) T t₁

/-- **R.3, `includeHealed`** (heal point `T ≥ T_heal`). Under the healing premises and `(U_all)`
from `T`: every honest proposal released at `τ ≥ T` by a proposer ready at `τ` is in the confirmed
read of every node ready at `t`, for every `t ≥ τ + 6Δ`. -/
def IncludeHealed : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → HealedPremises tr H dg g ΔF Gp a Tb T → UnanimousFrom tr H T →
    ∀ τ P, T ≤ τ → ReadyProposalAt tr H (catchUp sp) τ P →
      ∀ y t j, τ + 6 * sp.Δ ≤ t → ReadyAt tr H (catchUp sp) y t → CutAfter tr j t →
        Anc (tr.HonestBlocks H) P (readAfter tr y j t)

/-- **R.3, `growHealed`** (heal point `T ≥ T_heal`). Under the healing premises, one honest ready
proposer in every window of `k ≥ 1` slots from the ready point `ḡ + 18Δ + 1` (the target's
`gReady`) up to the read time, and `(U_B)` from `T` with
`B = 4kΔ`: for every `t ≥ T` with a node ready at `t + D`, `D = (4k + 6)Δ`, some honest proposal
released at `τ > t` by a proposer ready at `τ` is a new common confirmed entry at `t + D` above
every ready read at `t` (as `GrowSleepy`). -/
def GrowHealed : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time) (k : Nat),
    GoldilocksRun dg H tr → HealedPremises tr H dg g ΔF Gp a Tb T → 1 ≤ k →
    UnanimousWithin tr H T (4 * k * sp.Δ) →
    ∀ t, T ≤ t →
      ProposerRecurrence tr H (catchUp sp) k (gbar g + catchUp sp + 1) (t + (4 * k + 6) * sp.Δ) →
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

/-- **R.3, `crossNest`** (heal point `T ≥ T_heal`; corrected, consensus-lean#104). Under the
healing premises, from `T` on: (1) at one time, the finalized read of every ready node is
compatible with the confirmed read of every ready node; (2) the finalized read of a node ready at
`t` is an ancestor of the confirmed read of every node ready at every `t' ≥ t + Δ` (read points
between the readers' events). Not at the same instant: an honest proposer can finalize by accepting
its own block, which the others receive up to `Δ` later (#104, model run `crossnest-n10-s388`). -/
def CrossNest : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time),
    GoldilocksRun dg H tr → HealedPremises tr H dg g ΔF Gp a Tb T →
    ∀ t t' x y i j, T ≤ t → t ≤ t' → ReadPoint tr i t → ReadPoint tr j t' → Boundary tr x i →
      Boundary tr y j → ReadyAt tr H (catchUp sp) x t → ReadyAt tr H (catchUp sp) y t' →
      (t' = t → Compatible (tr.HonestBlocks H) (tr.state x i).fg.F (readAfter tr y j t')) ∧
      (t + sp.Δ ≤ t' → Anc (tr.HonestBlocks H) (tr.state x i).fg.F (readAfter tr y j t'))

/-- The healed rows of milestone Regimes (R.3, at a heal point `T ≥ T_heal`). -/
structure HealedStatements : Prop where
  healedSafe : HealedSafe
  includeHealed : IncludeHealed
  growHealed : GrowHealed
  crossNest : CrossNest

end Consensus.Goldilocks.Regimes

end
