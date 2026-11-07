module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.SlowOrigins
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.SlowComparison

public section

/-! # Stored locks compared with a historical slow selection -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A live stored lock in the slow window compares with the writer's saved result of its slot. -/
theorem slow_stored_locks_service_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    {x : Fin sp.n} {c s : Nat} (hx : x ∈ H (tr.time c))
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hsl : SA.SlowLockAt tr.projAC x c s D)
    (hm : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks, sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y D := by
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  intro l hl hlive hle Y hY hYr
  obtain ⟨L, hL, hLr, O, hLO, k, -, CV, hyk, hO⟩ :=
    stored_lock_below_origin_at hrun hnc hy l hl
  obtain rfl : Y = L := hU.1 hY hL (hYr.trans hLr.symm)
  obtain ⟨kx, R, CVx, hxk, hR, hDR⟩ :=
    slow_window_results_at hrun hnc hx hsl l.slot (by omega) hle
  have hj : gbar g ≤ sp.ts l.slot := hm.trans ((SA.ts_le_iff sp).mpr (by omega))
  have hc : Compatible (tr.HonestBlocksAt H) O R := by
    rcases hO with hO | hO
    · exact result_result_compatible_service_at hrun hnc hsvc hj hyk hxk hO hR
    · exact (result_optimistic_compatible_service_at hrun hnc hsvc hj hxk hyk hR hO).symm
  rcases hc with hc | hc
  · exact Anc.total hU (hLO.trans hc) hDR
  · exact Anc.total hU hLO (hDR.trans hc)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
