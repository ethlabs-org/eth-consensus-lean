module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorGlobal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Outage under growing faults: the store of a node at a read time

Facts about the store of a node `y` at cut `i`, read at a time `d ≥ 0` at which `y` is honest
and after every cut before `i` (the read-time form): each is the static fact on the prefix through
`d`, where the node's states up to `i` are the run's.

* `tree_held_at`: the tree is held while honest;
* `tree_mono_at`, `F_mono_at`: the tree grows and `Σ.F` only extends, from an earlier cut;
* `held_anc_at`: ancestry inside the blocks held while honest, ending in the tree, is ancestry in
  the store;
* `frameOK_at`, `reachable_at`: the frame is well formed and the store reachable;
* `floor_frame_transport_at`, `frame_mem_of_tree_at`: frame blocks above a block stay in a later
  frame that holds it. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {y : Fin sp.n} {i : Nat} {d : Time}

theorem tree_held_at (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
  fun _ hB => ⟨y, i, d, hd, hi, hy, hB⟩

theorem reachable_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    (tr.state y i).fg.Reachable (goldilocksNode sp ro).genesisPayload := by
  have h := fg_reachable (hrun.upTo hd).toLocalRun hy i
  rwa [Trace.upTo_state tr y hi] at h

theorem frameOK_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) :
    FrameOK (Node.frame (tr.state y i)) := by
  have h := frameOK_state (hrun.upTo hd).toLocalRun hy i
  rwa [Trace.upTo_state tr y hi] at h

theorem tree_mono_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) {k : Nat} (hki : k ≤ i) :
    (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree := by
  have h := tree_mono (hrun.upTo hd).toLocalRun hy hki
  rwa [Trace.upTo_state tr y hi, Trace.upTo_state tr y fun k' hk' => hi k' (by omega)] at h

theorem F_mono_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d) {k : Nat} (hki : k ≤ i) :
    Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F (tr.state y i).fg.F := by
  have h := Healing.run_F_mono (hrun.upTo hd).toLocalRun hy hki
  rw [Trace.upTo_state tr y hi, Trace.upTo_state tr y fun k' hk' => hi k' (by omega)] at h
  exact h.mono (upTo_subset hrun hd)

theorem held_anc_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d)
    {A W : SA.Blk sp.n (List (FG.Att sp.n))} (h : Anc (tr.HonestBlocksAt H) A W)
    (hW : W ∈ (tr.state y i).fg.tree) : (tr.state y i).fg.Anc A W := by
  have hst := Trace.upTo_state tr y hi
  have hWU : W ∈ (tr.upTo d).HonestBlocks (H d) := ⟨y, hy, i, by rw [hst]; exact hW⟩
  have h' := honest_held_anc (hrun.upTo hd) (hnc.upTo _) hy (i := i)
    (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hWU h) (by rw [hst]; exact hW)
  rwa [hst] at h'

theorem frame_mem_of_tree_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) (hd : 0 ≤ d) (hy : y ∈ H d) (hi : ∀ k < i, tr.time k ≤ d)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y i).fg.tree)
    (hF : Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F B) :
    B ∈ (tr.state y i).fg.toFrame.tree :=
  ⟨hB, held_anc_at hrun hnc hd hy hi hF hB⟩

theorem floor_frame_transport_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) (hd : 0 ≤ d)
    (hy : y ∈ H d) {i' : Nat} (hi' : ∀ k < i', tr.time k ≤ d) (hii' : i ≤ i')
    {B₀ B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB0 : B₀ ∈ (tr.state y i').fg.toFrame.tree) (hB : B ∈ (tr.state y i).fg.toFrame.tree)
    (h : (tr.state y i).fg.toFrame.Anc B₀ B) :
    B ∈ (tr.state y i').fg.toFrame.tree ∧ (tr.state y i').fg.toFrame.Anc B₀ B := by
  have hst' := Trace.upTo_state tr y hi'
  have hst := Trace.upTo_state tr y (i := i) fun k hk => hi' k (by omega)
  have h' := floor_frame_transport (hrun.upTo hd) hy hii' (B₀ := B₀) (B := B)
    (by rw [hst']; exact hB0) (by rw [hst]; exact hB) (by rw [hst]; exact h)
  rwa [hst'] at h'

end Consensus.Goldilocks.Compose.Growing

end
