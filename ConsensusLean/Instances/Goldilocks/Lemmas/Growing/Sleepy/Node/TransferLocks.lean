module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing

public section

/-! # Goldilocks under `Sleepy` with growing faults: the live locks at a vote

`vote_locks_compatible_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, every live
lock block is compatible with a block `B` that is compatible with every origin within `b` of label
at most `s` and that the earlier slot-`(s+1)` votes of nodes honest at them extend. A lock of slot
at most `s` sits below an origin of its slot; one of slot `s + 1` is optimistic, and its check at a
cut `c ≤ i` is counted with `2 f < n` at that cut (`hB.two`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The live locks at a slot-`(s+1)` vote are compatible with `B`** under growing faults. -/
theorem vote_locks_compatible_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hB : SleepyBounds tr H b) {s : Nat} {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end
