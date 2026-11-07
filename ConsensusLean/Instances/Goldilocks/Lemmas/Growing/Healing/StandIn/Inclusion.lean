module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing

public section

/-! # Temporary A4 inclusion and growth interfaces for Healing

These two stand-ins have the planned A4 signatures. They deliberately live outside
`Regimes.Growing` to avoid clashing with A4's exports. Replace them with
`Regimes.Growing.include_sleepy_at` and `Regimes.Growing.grow_sleepy_at` from
`Growing/Sleepy/Service/Inclusion` when that module lands. The two sorry proofs are the
only obligations in this file; none of the regime or finite-service definitions is stubbed.
-/

namespace Consensus.Goldilocks.Healing.Growing.StandIn

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- Stand-in for A4's finite-service inclusion theorem, with honesty at the read time. -/
theorem include_sleepy_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore tr H ΔF b)
    (hB : Compose.Growing.SleepyBounds tr H b) {τ : Time}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposalAt tr H (Regimes.catchUp sp) τ (hold sp) P)
    {y : Fin sp.n} {t : Time} {j : Nat} (hmargin : τ + 6 * sp.Δ ≤ t)
    (htb : t ≤ b) (hy : ReadyAt tr H (Regimes.catchUp sp) y t)
    (hj : Regimes.CutAfter tr j t) :
    Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y j t) := by
  sorry

/-- Stand-in for A4's finite-service growth theorem, retaining both read-time guards. -/
theorem grow_sleepy_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore tr H ΔF b)
    (hB : Compose.Growing.SleepyBounds tr H b) {k : Nat} (hk : 1 ≤ k)
    {t : Time} (ht : 0 ≤ t) (htb : t + (4 * k + 6) * sp.Δ ≤ b)
    (hrec : ProposerRecurrence tr H proposer (Regimes.catchUp sp) k (hold sp) 0
      (t + (4 * k + 6) * sp.Δ)) :
    ∃ τ P, t < τ ∧ ReadyProposalAt tr H (Regimes.catchUp sp) τ (hold sp) P ∧
      (∀ y j, ReadyAt tr H (Regimes.catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
        Regimes.CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
        Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y j (t + (4 * k + 6) * sp.Δ))) ∧
      (∀ x jx, ReadyAt tr H (Regimes.catchUp sp) x t → Regimes.CutAfter tr jx t →
        ¬ Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr x jx t)) ∧
      ∀ x jx y j, ReadyAt tr H (Regimes.catchUp sp) x t → Regimes.CutAfter tr jx t →
        ReadyAt tr H (Regimes.catchUp sp) y (t + (4 * k + 6) * sp.Δ) →
        Regimes.CutAfter tr j (t + (4 * k + 6) * sp.Δ) →
        Anc (tr.HonestBlocksAt H) (Regimes.readAfter tr x jx t)
          (Regimes.readAfter tr y j (t + (4 * k + 6) * sp.Δ)) := by
  sorry

end Consensus.Goldilocks.Healing.Growing.StandIn

end
