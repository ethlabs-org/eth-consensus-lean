module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run

public section

/-! # Goldilocks under `Sleepy`: frame geometry and the frozen witness

workbench#11 §3 (S3). With the source origins relevant at a cut compatible with an origin `C` and
with each other, every target or progress quorum has an honest row (`q > f`), whose named entry is
on the origin chain; comparable sources of one height name one entry, so there is no contest from
genesis, the floor is `max(1, h_max − 1)`, and `fc_root` (`Σ.J` or `Σ.F`) is compatible with `C`.

Both are stated for a block `B` with the hypotheses the argument uses, not only for origins, so
that the proposal-adoption bootstrap (workbench#12 §4, S3P) applies them to the protected
proposal.

* **Full reads** (`held_origin_viable`): a held block compatible with every origin, above
  `fc_root`, is in the full viable tree: it is viable itself, or a maximal-height carrier extends
  the named entry of an honest crossing source above it.
* **Votes** (`vote_frame`): at an honest slot-`(s+1)` vote, a block compatible with the origins of
  labels `≤ s` and extended by an honest slot-`s` vote is in the viable tree of the voter block
  tree, or at or below `fc_root` (inside the honest blocks). The
  sources the voter's FG has seen have labels at most `s` (a label-`(s+1)` source is reported at
  the earliest in the tick at `t_{s+1} + Δ`, after the votes there), so `P_{s+1}` compares them;
  the frozen witness is an honest head (of a crossing source when the floor is above `B`, the
  honest slot-`s` head extending `B` otherwise), accepted before the freeze. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- **S3 at full reads**: once all origins compare, a block `B` that an honest node holds and that
is compatible with every origin (an origin itself, or a protected proposal once it is) is at or
below its `fc_root` or in its full viable tree. -/
theorem held_origin_viable (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) (hP : ∀ s, OriginsBelow tr H s) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, Origin tr H C s → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  sorry

/-- **S3 at votes (the frozen witness)**: at an honest slot-`(s+1)` vote, a block `B` of the honest
blocks that is compatible with every origin of label at most `s` and that some honest slot-`s`
vote extends (an origin of label `s` by its honest supporter, an older one by `V_s`, a protected
proposal by its common batch) is in the viable tree of the voter block tree, or at or below
`fc_root` (inside the honest blocks). -/
theorem vote_frame (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {s : Nat} (hP : OriginsBelow tr H (s + 1)) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocks H)
    (hBc : ∀ C j, Origin tr H C j → j ≤ s → Compatible (tr.HonestBlocks H) B C)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame (s + 1)) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

end Consensus.Goldilocks.Compose

end
