module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows

public section

/-! # Store ancestry and state agreement at independently honest observations

Only node-local reachability is retained. The historical block universe is coherent without
requiring a block's original holder to remain honest at another observation.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Reachability at a held-state observation, not necessarily the time of cut `i`. -/
theorem fg_reachable_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) :
    (tr.state y i).fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  simpa only [Trace.upTo_state tr y hle] using
    Compose.fg_reachable (hrun.upTo ht).toLocalRun hy i

/-- Historical ancestry descends into the reader's actual held tree. -/
theorem store_anc_of_honest_anc_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {A C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocksAt H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    (tr.state y k).fg.Anc A C := by
  have hs := Trace.upTo_state tr y hle
  have hc : C ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, k, by rwa [hs]⟩
  have hanc := RunTrace.anc_upTo_of_right hrun.toLocalRun hnc ht hc h
  rw [← hs]
  exact Healing.store_anc_of_honest_anc (hrun.upTo ht)
    (Compose.NoCollRun.upTo hnc t) hy hanc (by rwa [hs])

/-- Ancestry in a tree observed while honest lies in the historical honest universe. -/
theorem honest_anc_of_store_anc_at {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {A C : SA.Blk sp.n (List (FG.Att sp.n))} (h : (tr.state y k).fg.Anc A C) :
    Anc (tr.HonestBlocksAt H) A C :=
  h.mono fun _ hB => ⟨y, k, t, ht, hle, hy, hB⟩

/-- Parent closure at a held-state observation. -/
theorem mem_of_honest_anc_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t)
    {A C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Anc (tr.HonestBlocksAt H) A C) (hC : C ∈ (tr.state y k).fg.tree) :
    A ∈ (tr.state y k).fg.tree := by
  by_cases he : A = C
  · exact he ▸ hC
  · exact (Anc.mem (store_anc_of_honest_anc_at hrun hnc ht hle hy h hC) he).1

/-- A held block's replay state is identical at two independently honest observations.
This is deterministic replay and root coherence, so it needs no quorum premise. -/
theorem σ_eq_honest_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y i).fg.tree) (hBz : B ∈ (tr.state z j).fg.tree) :
    (tr.state y i).fg.σ B.root = (tr.state z j).fg.σ B.root :=
  Store.σ_eq_of_mem (fg_reachable_at hrun ht hle hy) (fg_reachable_at hrun hu hle' hz)
    (Compose.Growing.honest_blocks_coherent hrun hnc).1
    (fun _ hX => ⟨y, i, t, ht, hle, hy, hX⟩)
    (fun _ hX => ⟨z, j, u, hu, hle', hz, hX⟩) hBy hBz

end Consensus.Goldilocks.Healing.Growing

end
