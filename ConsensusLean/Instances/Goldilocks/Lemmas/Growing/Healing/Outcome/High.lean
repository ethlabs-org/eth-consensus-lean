module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RowSource

public section

/-! # Height above an independently observed high origin -/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g : Time}

/-- The stored block of a high origin is held at its actual honest write. -/
theorem high_origin_mem_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    B ∈ (tr.state x i).fg.tree := by
  obtain ⟨CV, ell, D, hc, hfl, he⟩ := ho.2.2.1
  have ht := hrun.time_nonneg i
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt x i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) _ proposer
    (hrun.upTo ht) (hnc.upTo _)).localRun
  have hPhi := (SA.frameIn_of_callAt hr ho.1 hc').1
  have hD : D ∈ ell.frame.tree := by
    rcases hfl with ⟨ell', C, ⟨hc', -⟩, -, hD, -⟩ | ⟨ell', A, ⟨hc', -⟩, -, hs, -⟩
    · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
      exact (SA.deepest_mem hD).1.1.1
    · obtain rfl : ell' = ell := Option.some.inj (hc'.2.symm.trans hc.2)
      unfold SA.optimisticSelect at hs
      dsimp only at hs
      split_ifs at hs
      exact (SA.deepest_mem hs).1.1
  have hB := (SA.viableAncestor_anc hPhi hD).1
  rw [← he, frame_of_call hrun ho.1 hc] at hB
  exact hB.1

/-- A held descendant is high even when the source writer was later compromised. -/
theorem high_of_anc_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x z : Fin sp.n} {i j k : Nat} {t : Time}
    {B W : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hz : z ∈ H t)
    (hW : W ∈ (tr.state z k).fg.tree) (hBW : Anc (tr.HonestBlocksAt H) B W) :
    HZ tr H g + 1 ≤ ((tr.state z k).fg.σ W.root).h := by
  have hBx := high_origin_mem_at hrun hnc ho
  have hBz := mem_of_honest_anc_at hrun hnc ht hle hz hBW hW
  have hh := Healing.h_le_of_store_anc (fg_reachable_at hrun ht hle hz)
    (store_anc_of_honest_anc_at hrun hnc ht hle hz hBW hW)
  have he := σ_eq_honest_at hrun hnc (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) ho.1 ht hle hz hBx hBz
  rw [← he] at hh
  exact ho.2.2.2.trans hh

end Consensus.Goldilocks.Healing.Growing.Outcome

end
