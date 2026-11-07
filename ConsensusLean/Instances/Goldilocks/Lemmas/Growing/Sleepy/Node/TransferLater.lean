module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.VoteFrame

public section

/-! # Goldilocks under `Sleepy` with growing faults: the later transfer step

`later_transfer_step_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, a block `B`
held while honest, compatible with every origin within `b` of label at most `s`, that every
slot-`s` vote of a node honest at it extends and that the earlier slot-`(s+1)` votes of nodes
honest at them extend, is extended by the vote (`vote_frame_at`, `vote_locks_compatible_at`, and
the batch counted at the voter's cut, `vote_extends_of_batch_at`). -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **Later batch under growing faults**. -/
theorem later_transfer_step_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBounds tr H b) {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b) {y : Fin sp.n}
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C)
    (hall : ∀ x k e', HVoteAt tr H x k e' → e'.msg.slot = s →
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B)
    (hE : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) i (s + 1) B) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end
