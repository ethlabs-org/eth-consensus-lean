module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.FrameWindow

public section

/-! # Finality below floor-viable descendants across honest cuts -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Floor comparison needs a quorum bound at the later observation, not persistent readers. -/
theorem finalized_below_floor_held_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i m : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time m))
    (hf : (H (max (tr.time i) (tr.time m)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state z m).fg.tree)
    (hheight : (tr.state y i).fg.headHeightFloor ≤ ((tr.state z m).fg.σ W.root).h)
    (hJ : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬(tr.state y i).fg.Contest → Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J W) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F W := by
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have htm := hrun.time_nonneg m
  have hbm : ∀ q < m, tr.time q ≤ tr.time m := fun q hq => hrun.time_mono hq.le
  have hr := fg_reachable_at hrun ht hb hy
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun _ h => ⟨y, i, tr.time i, ht, hb, hy, h⟩
  have hcoh := hU.mono hsub
  obtain ⟨hF, hJm, hFJ, ⟨Bj, hBj, hBjJ, _⟩, hmax, -, X, hX, hXF⟩ :=
    Store.cache_invariants _ _ _ _ hr
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest
  · exact (hFJ.mono hsub).trans (hJ hk.1 hk.2)
  have hg := Store.genesis_mem hr
  have hgen : (tr.state y i).fg.F.root = sp.toParams.genesisRoot →
      Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F W := fun he => by
    rw [hcoh.1 hF hg he]
    exact ((Store.accepted_tree _ _ _ _ (fg_reachable_at hrun htm hbm hz)).2.2.2 W hW).mono
      (fun _ h => ⟨z, m, tr.time m, htm, hbm, hz, h⟩)
  rcases Store.fin_pair_entry hr hX with he | ⟨E, hE, hEr, _⟩
  · exact hgen (hXF.symm.trans he)
  obtain rfl : E = (tr.state y i).fg.F := hcoh.1 hE hF (hEr.trans hXF)
  obtain ⟨J, hJt, hJr, -, hcase⟩ := Store.J_entry_of_reachable hr hBj
  obtain rfl : J = (tr.state y i).fg.J := hcoh.1 hJt hJm (hJr.trans hBjJ)
  rcases hcase with he | ⟨hJh, -⟩
  · have hgF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hF
    rw [he] at hFJ
    exact hgen (congrArg Block.root (Anc.antisymm hcoh hFJ hgF))
  have hFh := Healing.h_le_of_store_anc hr hFJ
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ hr Bj hBj
  have hjlt := (FG.chain_invariants _ _ _ hc).2.2.1
  have hmaxBj := hmax Bj hBj
  have hstrict : ((tr.state y i).fg.σ X.root).hF < ((tr.state z m).fg.σ W.root).h := by
    by_cases hcon : (tr.state y i).fg.Contest
    · simp only [Store.headHeightFloor, ite_eq_left hcon] at hheight
      omega
    · have hne : (tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1 :=
        fun he => hk ⟨he, hcon⟩
      simp only [Store.headHeightFloor, ite_eq_right hcon] at hheight
      omega
  exact finalized_anc_obs hrun hnc ht hb hy htm hbm hz hf hX hF hXF.symm hW hstrict

/-- A window's common floor places its finalized tip below an independently held descendant. -/
theorem FrameWindow.finalized_below_descendant_at {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x z : Fin sp.n} {j i c : Nat}
    (hy : y ∈ H (tr.time j)) (hx : x ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (max (tr.time j) (tr.time i)))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hjlo : lo ≤ tr.time j) (hjhi : tr.time j ≤ hi)
    {X W : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hW : W ∈ (tr.state x i).fg.tree) (hXW : Anc (tr.HonestBlocksAt H) X W) :
    Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F W := by
  apply finalized_below_floor_held_at hrun hnc hy hx hf hW
  · rw [hframe.floor_eq y j hy hjlo hjhi]
    exact floor_le_of_honest_ancestor_at hrun hnc hx hz hX hh hW hXW
  · intro hm hc
    have hk := (hframe.kind_iff y j hy hjlo hjhi).mp ⟨hm, hc⟩
    rw [hframe.root_eq y j hy hjlo hjhi hk]
    exact (hJ hk).trans hXW

end Consensus.Goldilocks.Healing.Growing

end
