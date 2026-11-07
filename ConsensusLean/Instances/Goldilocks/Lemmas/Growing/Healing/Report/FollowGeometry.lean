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

end Consensus.Goldilocks.Healing.Growing

end
