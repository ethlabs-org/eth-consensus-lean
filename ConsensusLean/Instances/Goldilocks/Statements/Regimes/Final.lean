module
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Healed
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Recovery

@[expose] public section

/-! # Goldilocks milestone Regimes: the final rows R.4 (statements)

Transcribed from fradamt-agent/goldilocks `spec/goldilocks-claims.tex` §"L2: regime theorems
(skeleton)" (main `5ae87546`), row R.4 (`finalFirst`, `finalRecur`, `liveDC`, `healthyLive`
(final), `finalized_txLive`; uses C1.3, G1.9, R.3 and O.1), over the Goldilocks run.

**The heal point is a parameter `T`** with `T ≥ T_heal` (R.3's) and `T ≥ ḡ + T_rec` (node O.1's,
so `Rec(T)` and every C1.3 window from `T` are available), not the target's `gHealFin` or
`finalCut`; the deadlines are C1.3's, not the target's `W_W(gf)`: the coverage of C1.3 requested
at `t + Δ`, `D_fin = 4Δ(W + 1 + M) + 2Δ` (a proposal released in `[t + Δ, t + Δ + 4Δ(W + 1 +
M)]`, covered by `t + D_fin`). **R.4 at the target's numbers stays open** (docs/decisions.md,
"Goldilocks instance", as for R.3). With one deadline for all rows, `finalRecur` is `LiveDC`
without the proposal and `finalFirst` is `finalRecur` at `t = T`: they are not stated apart.

**Premises the target lacks** (the Refinement must discharge them or they stay as conditions):
those of R.3 (`HealedPremises`: `Catch(2Δ)`, `Prop⁺(G_p)`, the `δ_t` bound and genesis root of
`HSShared`, H.3 (c)'s bridge), and node O.1's and C1.3's regime (`PatternPremises`): C1.2's window
parameters `c_F`, `k_F` and **the uniform pattern `UPat(W, M)` with `M ≥ M*`**, which is the regime
node O.1 is proved under, not the contract's proposer premise (`gProg` at `final`, the finality
recurrence of `gf`); R.4 under the contract's premise needs O.1's target, which is open (claims
§"O.1", Status). No unanimity premise is taken: the rows cover one honest proposal per C1.3
window, not every honest proposal.

Reads are after all events at a time (`CutAfter`): the confirmed read `readAfter`, the finalized
read `Σ.F` of the node's state (`(tr.state y j).fg.F`).

**Open proof items** (obligations, not premises): C1.3's proposer is ready at its release (from
`Healthy` and `T ≥ ḡ + T_rec`); no honest read at `t` holds a block of a slot starting after `t`;
`LiveDC`'s last clause from `HealedSafe` and the reader's own nesting `Σ.F ⪯ confirmed` (C0.1)
at `t + D_fin` (so R.4 inherits R.3's open proof items, but not the cross-node `CrossNest`).

The transaction rows (`healthyLive` (final), `finalized_txLive`) are not stated over the run (no
transactions there): the Refinement derives them from `FinalInclude` (a proposal released at
`τ ≥ t + Δ` by a ready proposer, in every ready finalized read from `t + D_fin` on).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Regimes

open SA (SAParams ReplayOrder Payload gbar)
open Healing (PatternPremises T_rec)

/-- The final deadline `D_fin = 4Δ(W + 1 + M) + 2Δ`: C1.3's coverage deadline `4Δ(W + 1 + M) + Δ`
for the coverage requested at `t + Δ`. -/
def D_fin (sp : SAParams) (W M : Nat) : Time := 4 * sp.Δ * ((W : Time) + 1 + M) + 2 * sp.Δ

section Defs

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- The premises of R.4 with heal point `T`: R.3's healing premises at `T`, the premises of node
O.1 and C1.3 (`UPat(W, M)` with `M ≥ M*`), and `T ≥ ḡ + T_rec`. -/
structure FinalPremises (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF Gp a Tb T : Time)
    (W M cF kF : Nat) : Prop where
  /-- R.3's healing premises, with `T ≥ T_heal`. -/
  healed : HealedPremises tr H dg g ΔF Gp a Tb T
  /-- C1.2's premises and `UPat(W, M)` with `M ≥ M*`. -/
  pattern : PatternPremises tr H dg g ΔF Gp W M cF kF
  /-- The heal point is at or after `ḡ + T_rec`. -/
  recovered : gbar g + T_rec sp ΔF Gp W M ≤ T

end Defs

/-- **R.4, `liveDC`** (and `finalRecur`, forgetting the proposal, and `finalFirst`, its instance
`t = T`). Under the final premises with heal point `T`: for every `t ≥ T`, some honest proposal
`P` released at `τ > t` by a proposer ready at `τ` is a new finalized entry at `t + D_fin` above
the ready confirmed reads at `t`: it is in the finalized read at `t + D_fin` of every node ready
then, in none of the confirmed reads at `t` of the nodes ready then, and each of those is an
ancestor of each ready finalized read at `t + D_fin`. -/
def LiveDC : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time) (W M cF kF : Nat),
    GoldilocksRun dg H tr → FinalPremises tr H dg g ΔF Gp a Tb T W M cF kF →
    ∀ t, T ≤ t → ∃ τ P, t < τ ∧ ReadyProposalAt tr H (catchUp sp) τ P ∧
      (∀ y j, ReadyAt tr H (catchUp sp) y (t + D_fin sp W M) → CutAfter tr j (t + D_fin sp W M) →
        Anc (tr.HonestBlocks H) P (tr.state y j).fg.F) ∧
      ∀ x jx, ReadyAt tr H (catchUp sp) x t → CutAfter tr jx t →
        ¬ Anc (tr.HonestBlocks H) P (readAfter tr x jx t) ∧
        ∀ y j, ReadyAt tr H (catchUp sp) y (t + D_fin sp W M) →
          CutAfter tr j (t + D_fin sp W M) →
          Anc (tr.HonestBlocks H) (readAfter tr x jx t) (tr.state y j).fg.F

/-- **R.4, block form of `healthyLive` (final) and `finalized_txLive`.** Under the final premises
with heal point `T`: for every `t ≥ T`, some honest proposal `P` released at
`τ ∈ [t + Δ, t + Δ + 4Δ(W + 1 + M)]` by a proposer ready at `τ` is in the finalized read of every
node ready at `t'`, for every `t' ≥ t + D_fin`. -/
def FinalInclude : Prop :=
  ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
    (tr : GoldilocksTrace sp ro) (g ΔF Gp a Tb T : Time) (W M cF kF : Nat),
    GoldilocksRun dg H tr → FinalPremises tr H dg g ΔF Gp a Tb T W M cF kF →
    ∀ t, T ≤ t → ∃ τ P, t + sp.Δ ≤ τ ∧ τ ≤ t + sp.Δ + 4 * sp.Δ * ((W : Time) + 1 + M) ∧
      ReadyProposalAt tr H (catchUp sp) τ P ∧
      ∀ y t' j, t + D_fin sp W M ≤ t' → ReadyAt tr H (catchUp sp) y t' → CutAfter tr j t' →
        Anc (tr.HonestBlocks H) P (tr.state y j).fg.F

/-- The final rows of milestone Regimes (R.4, at a heal point `T ≥ T_heal`, `T ≥ ḡ + T_rec`, under
`UPat(W, M)`). -/
structure FinalStatements : Prop where
  liveDC : LiveDC
  finalInclude : FinalInclude

end Consensus.Goldilocks.Regimes

end
