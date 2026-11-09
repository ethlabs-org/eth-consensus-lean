module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.FamilyInstance
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

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

/-- The entry an honest source names is compatible with a block compatible with the source. -/
private theorem entry_compatible (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {D E B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hDs : IsHonestSource tr H D E.root) (hE : E ∈ (tr.state y i).fg.tree)
    (hDB : Compatible (tr.HonestBlocks H) D B) : Compatible (tr.HonestBlocks H) E B := by
  have hU := (projFG_localRun hrun hnc).coherent
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E D := hED.mono (fg_tree_subset_honest hx k)
  rcases hDB with h | h
  · exact Or.inl (hEDU.trans h)
  · exact Anc.total hU hEDU h

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
  exact FamilySafety.held_candidate_of_rows_instance hrun hnc hf hy i hsrc hGB hBt

end Consensus.Goldilocks.Compose

end
