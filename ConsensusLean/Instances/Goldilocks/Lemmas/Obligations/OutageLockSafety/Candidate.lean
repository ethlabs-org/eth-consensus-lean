module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameCandidate

public section

/-! # Outage lock safety: a held block stays a viable-ancestor candidate without pairwise sources

`held_viable_of` (`Sleepy/FrameLabels.lean`) excludes every contest through pairwise compatible
sources. In the outage two honest sources can be siblings above the protected block, so a contest
can occur; `held_candidate_of_rows` shows that a contest never removes the candidacy of a held
block `B` compatible with every source: `B` is at or below `fc_root`, or in the full viable
tree. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **A held block compatible with every honest source stays a candidate**: with
`f < n/2` and the honest attestations of `y`'s tree sourced by `G`, a block `B` of the frame's tree
compatible with every `G`-source is at or below `fc_root` or in the full viable tree. No pairwise
premise on the sources. -/
theorem held_candidate_of_rows (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  apply FrameGeometry.held_candidate_of_rows hrun.toLocalRun (projFG_localRun hrun hnc)
    hf hy i _ hGB hBt
  exact FrameGeometry.honestRowsSourced_iff.2 fun X hX a ha hav => by
    obtain ⟨D, hD, hDs⟩ := honestRowsSourced_iff.1 hsrc X hX a ha hav
    exact ⟨D, hD, FrameGeometry.isHonestSource_iff.2 (isHonestSource_iff.1 hDs)⟩

end Consensus.Goldilocks.Compose

end
