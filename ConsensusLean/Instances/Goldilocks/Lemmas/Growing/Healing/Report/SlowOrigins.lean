module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks

public section

/-! # Historical results supporting a slow selection

The writer's saved results are recovered only on its own honest execution prefix.
Their ancestry is then retained in the historical block universe.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Every saved slot used by a slow selection has an actual result written while honest. -/
theorem slow_window_results_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {c s : Nat}
    (hx : x ∈ H (tr.time c)) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsl : SA.SlowLockAt tr.projAC x c s D) :
    ∀ j : Nat, (s : Int) - sp.k < j → j ≤ s →
      ∃ k R CV, x ∈ H (tr.time k) ∧ SA.ResultAt tr.projAC x k j R CV ∧
        Anc (tr.HonestBlocksAt H) D R := by
  have hd := hrun.time_nonneg c
  have hr := (acRun_upTo hrun hnc hd).localRun
  obtain ⟨ell, C, hu, hconf, hdeep⟩ := hsl
  have hs := projAC_upTo_state hrun (y := x) (le_refl (tr.time c))
  have hsl' : SA.SlowLockAt (tr.projAC.upTo (tr.time c)) x c s D := by
    refine ⟨ell, C, (sa_updateAt_upTo hrun.time_mono).mpr ⟨le_rfl, hu⟩, ?_, ?_⟩
    · rwa [hs]
    · simpa only [hs, Trace.upTo_time] using hdeep
  intro j hj hjs
  obtain ⟨k, R, CV, hR, hDR⟩ := SA.slow_window_results hr hx hsl' j hj hjs
  obtain ⟨hkc, hR⟩ := (sa_resultAt_upTo hrun.time_mono).mp hR
  exact ⟨k, R, CV, hrun.antitone hkc hx, hR,
    hDR.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono hd)⟩

/-- A stored lock has an actual earlier result or optimistic origin at the same node. -/
theorem stored_lock_below_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks,
      ∃ L ∈ tr.HonestBlocksAt H, L.root = l.block ∧
        ∃ O, Anc (tr.HonestBlocksAt H) L O ∧ ∃ k < i, ∃ CV,
          y ∈ H (tr.time k) ∧
          (SA.ResultAt tr.projAC y k l.slot O CV ∨
            SA.OptimisticLockAt tr.projAC y k l.slot O CV) := by
  have hd := hrun.time_nonneg i
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hs := projAC_upTo_state hrun (y := y) (le_refl (tr.time i))
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  intro l hl
  obtain ⟨L, hL, hLr, O, hLO, k, hki, CV, ho⟩ :=
    SA.lock_below_origin hr hy i l (by rwa [hs])
  refine ⟨L, hsub hL, hLr, O, hLO.mono hsub, k, hki, CV,
    hrun.antitone (hrun.time_mono hki.le) hy, ?_⟩
  rcases ho with ho | ho
  · exact Or.inl ((sa_resultAt_upTo hrun.time_mono).mp ho).2
  · exact Or.inr ((sa_optimisticLockAt_upTo hrun.time_mono).mp ho).2

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
