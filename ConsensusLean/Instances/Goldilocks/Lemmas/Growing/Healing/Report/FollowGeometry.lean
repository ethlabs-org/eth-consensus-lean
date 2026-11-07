module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs

public section

/-! # Replay floor bounds at independently honest observations -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

/-- A source's replay floor passes to a descendant held at an independently honest cut. -/
theorem floor_le_of_honest_ancestor_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x z : Fin sp.n} {i c : Nat}
    (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    {X W : SA.Blk sp.n (List (FG.Att sp.n))} {floor : Nat}
    (hX : X ∈ (tr.state z c).fg.tree) (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    floor ≤ ((tr.state x i).fg.σ W.root).h := by
  have hti := hrun.time_nonneg i
  have hbi : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hXt := mem_of_honest_anc_at hrun hnc hti hbi hx hXW hW
  have ha := store_anc_of_honest_anc_at hrun hnc hti hbi hx hXW hW
  have hle := Healing.h_le_of_store_anc (fg_reachable_at hrun hti hbi hx) ha
  rw [← σ_eq_honest_at hrun hnc (hrun.time_nonneg c)
    (fun q hq => hrun.time_mono hq.le) hz hti hbi hx hX hXt] at hle
  exact hh.trans hle

/-- An accepted descendant makes a floor-viable historical source a viable frame head. -/
theorem floor_ancestor_mem_frame_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {j c : Nat}
    (hy : y ∈ H (tr.time j)) (hz : z ∈ H (tr.time c))
    (hf : (H (tr.time j))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {X W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : (tr.state y j).fg.headHeightFloor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 →
      ¬(tr.state y j).fg.Contest → Anc (tr.HonestBlocksAt H) (tr.state y j).fg.J X)
    (hW : W ∈ (tr.state y j).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    X ∈ (Node.frame (tr.state y j)).tree ∧
      (Node.frame (tr.state y j)).Anc (Node.frame (tr.state y j)).fcRoot X ∧
      X ∈ (Node.frame (tr.state y j)).viableHeads := by
  have ht := hrun.time_nonneg j
  have hb : ∀ q < j, tr.time q ≤ tr.time j := fun q hq => hrun.time_mono hq.le
  have hXt := mem_of_honest_anc_at hrun hnc ht hb hy hXW hW
  have hh' : (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ X.root).h := by
    rw [← σ_eq_honest_at hrun hnc (hrun.time_nonneg c)
      (fun q hq => hrun.time_mono hq.le) hz ht hb hy hX hXt]
    exact hh
  have hs := Trace.upTo_state tr y hb
  have hXt' : X ∈ ((tr.upTo (tr.time j)).state y j).fg.tree := by rwa [hs]
  have hh'' : ((tr.upTo (tr.time j)).state y j).fg.headHeightFloor ≤
      (((tr.upTo (tr.time j)).state y j).fg.σ X.root).h := by rwa [hs]
  obtain ⟨-, htree, hroot, -, hv⟩ := Healing.viable_head_of_floor (hrun.upTo ht)
    (hnc.upTo _) hf hy hXt' hh'' (fun hm hc => by
      rw [hs] at hm hc ⊢
      exact store_anc_of_honest_anc_at hrun hnc ht hb hy (hJ hm hc) hXt)
  rw [hs] at htree hroot hv
  have hΦ := (Store.frame_realization _ _ _ _ (fg_reachable_at hrun ht hb hy)).1
  have hsub : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, j, tr.time j, ht, hb, hy, h.1⟩
  exact ⟨htree, SA.anc_tree_of_anc_U (Compose.Growing.honest_blocks_coherent hrun hnc)
    hΦ hsub hΦ.fcRoot_mem (honest_anc_of_store_anc_at ht hb hy hroot) htree, hv⟩

end Consensus.Goldilocks.Healing.Growing

end
