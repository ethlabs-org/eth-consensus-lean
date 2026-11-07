module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowAnchorsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.WindowAnchorRoute

public section

/-! # The anchor route to window coverage, under growing faults

The growing form of the trace part of `Obligations/WindowAnchorRoute`; the store-level lemmas
(`Store.coverage_of_anchor_window` and its helpers) are reused unchanged.

* `anchor_window_advance_at`: three anchor steps give `σ[P₀].h + 3 ≤ σ[P₃].h` at every store
  holding the four anchors of a node honest at an observation time after the store's cuts;
* `cacheCoverage_of_anchor_window_upTo_at`: for such a holder of `P₃`, the block `F` of root
  `σ[P₃].F` is held and `P₀ ⪯ F` in the honest blocks. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The anchor window advance** under growing faults. Three anchor steps `P i → P (i+1)` give
`σ[P₀].h + 3 ≤ σ[P₃].h` at every store holding the four anchors of a node honest at an
observation time `t` after the store's cuts. -/
theorem anchor_window_advance_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hmem : ∀ i, P i ∈ (tr.state y k).fg.tree)
    (hstep : ∀ i : Fin 3, AnchorStepAt tr H (P i.castSucc) (P i.succ)) :
    ((tr.state y k).fg.σ (P 0).root).h + 3 ≤ ((tr.state y k).fg.σ (P 3).root).h := by
  have key : ∀ i : Fin 3, ((tr.state y k).fg.σ (P i.castSucc).root).h + 1 ≤
      ((tr.state y k).fg.σ (P i.succ).root).h := by
    intro i
    obtain ⟨z, j, j', hz, hz', hA, hX, hl⟩ := anchorStepAt_iff.mp (hstep i)
    rw [Healing.Growing.σ_eq_honest_at hrun hnc ht hle hy (hrun.time_nonneg j)
        (fun _ hq => hrun.time_mono hq.le) hz (hmem _) hA,
      Healing.Growing.σ_eq_honest_at hrun hnc ht hle hy (hrun.time_nonneg j')
        (fun _ hq => hrun.time_mono hq.le) hz' (hmem _) hX]
    exact hl
  have h0 : ((tr.state y k).fg.σ (P 0).root).h + 1 ≤ ((tr.state y k).fg.σ (P 1).root).h :=
    key 0
  have h1 : ((tr.state y k).fg.σ (P 1).root).h + 1 ≤ ((tr.state y k).fg.σ (P 2).root).h :=
    key 1
  have h2 : ((tr.state y k).fg.σ (P 2).root).h + 1 ≤ ((tr.state y k).fg.σ (P 3).root).h :=
    key 2
  omega

/-- **Window coverage from an anchor window, through a horizon**, under growing faults. Four
honest anchors `P i` at strictly increasing slots `s i` (guards of
`window_anchors_chain_upTo_at`), three anchor steps, and `(P 3).slot ≤ (P 0).slot + δt`. For a
holder `y` of `P 3` at cut `k`, honest at an observation time `t` after its earlier cuts, the
block `F` of root `σ[P₃].F` is held by `y` and `P₀ ⪯ F` in the honest blocks. -/
theorem cacheCoverage_of_anchor_window_upTo_at {g ΔF a b : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s : Fin 4 → Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.Growing.HonestProposalRun tr H proposer (s i) (P i)) (hs : StrictMono s)
    (hR : Healing.drainTime sp a ≤ sp.ts (s 0)) (hb : sp.ts (s 3) ≤ b)
    (hadj : s 3 = s 2 + 1 → sp.ts (s 2) + 6 * sp.Δ ≤ b)
    (hstep : ∀ i : Fin 3, AnchorStepAt tr H (P i.castSucc) (P i.succ))
    (hsl : (P 3).slot ≤ (P 0).slot + sp.toParams.fg.δt) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    (hB₃ : P 3 ∈ (tr.state y k).fg.tree) :
    ∃ F, (tr.state y k).fg.blocks ((tr.state y k).fg.σ (P 3).root).F = some F ∧
      Anc (tr.HonestBlocksAt H) (P 0) F := by
  have hch := window_anchors_chain_upTo_at hp hc hP hs hR hb hadj
  have hmem : ∀ i, P i ∈ (tr.state y k).fg.tree := fun i =>
    Healing.Growing.mem_of_honest_anc_at hp.run hp.noColl ht hle hy (hch i 3 (Fin.le_last i)) hB₃
  obtain ⟨F, hF, hAF⟩ := Store.coverage_of_anchor_window
    (Healing.Growing.fg_reachable_at hp.run ht hle hy) hB₃
    (Healing.Growing.store_anc_of_honest_anc_at hp.run hp.noColl ht hle hy
      (hch 0 3 (by decide)) hB₃)
    (anchor_window_advance_at hp.run hp.noColl ht hle hy hmem hstep) hsl
  exact ⟨F, hF, Healing.Growing.honest_anc_of_store_anc_at ht hle hy hAF⟩

end Consensus.Goldilocks.Obligations.Growing

end
