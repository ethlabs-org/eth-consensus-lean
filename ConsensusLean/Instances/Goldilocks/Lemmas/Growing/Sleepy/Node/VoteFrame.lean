module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame

public section

/-! # Goldilocks under `Sleepy` with growing faults: the frozen witness at a vote

`vote_frame_at`: at a slot-`(s+1)` vote of a node honest at its cut `i ≤ b`, a block `B` held
while honest, compatible with every origin within `b` of label at most `s` and extended by a
slot-`s` vote of a node honest at it, is in the viable tree of the voter block tree or at or below
`fc_root`. The honest rows of the voter's tree are classified at `i` (`2 f < n` at `tr.time i`);
each witnessing head is relayed from its voter, honest at its acceptance, to the voter, honest at
`i`, before the freeze. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **S3 at votes under growing faults (the frozen witness)**. -/
theorem vote_frame_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {b : Time} (hb : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b) (hB : SleepyBounds tr H b)
    {s : Nat} (hP : OriginsBelowUpTo tr H (s + 1) b) {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBU : B ∈ tr.HonestBlocksAt H)
    (hBc : ∀ C j, OriginWithin tr H C j b → j ≤ s → Compatible (tr.HonestBlocksAt H) B C)
    (hw : ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot := by
  sorry

end Consensus.Goldilocks.Compose.Growing

end
