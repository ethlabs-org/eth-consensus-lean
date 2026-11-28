module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPointLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Pre-advance frame windows

`FrameWindow` fixes explicit F-independent frame data on a finite interval: the honest
head-height floor and the kind of the justified block `J`. `floor_ancestor_mem_frame` puts a
floor-viable source in the receiver's P-U frame (frame root `Σ.F`). The stock-window persistence
and vote-head classification chain (`viableHead_persists` and its consumers) is retired: its floor
bound fails under P-U viability in a contest (adoption A3). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF b : Time}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- Explicit F-independent frame data on a finite interval. F itself need not agree. -/
structure FrameWindow (lo hi : Time) (floor : Nat) (kindJ : Prop)
    (J : AC.Blk sp.n (List (FG.Att sp.n))) : Prop where
  floor_eq : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi →
    (tr.state y i).fg.headHeightFloor = floor
  kind_iff : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi →
    (((tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest) ↔ kindJ)
  root_eq : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i ≤ hi → kindJ →
    (tr.state y i).fg.J = J

/-- An accepted descendant puts a floor-viable source in the receiver's frame, even when
the source was originally witnessed at a later cut. -/
theorem floor_ancestor_mem_frame (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {j c : Nat}
    {X W : AC.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state z c).fg.tree)
    (hh : (tr.state y j).fg.headHeightFloor ≤ ((tr.state z c).fg.σ X.root).h)
    (hJ : (tr.state y j).fg.hmax = (tr.state y j).fg.hj + 1 →
      ¬(tr.state y j).fg.Contest → Anc (tr.HonestBlocks H) (tr.state y j).fg.J X)
    (hW : W ∈ (tr.state y j).fg.tree) (hXW : Anc (tr.HonestBlocks H) X W) :
    X ∈ (Node.frame (tr.state y j)).tree ∧
      (Node.frame (tr.state y j)).Anc (Node.frame (tr.state y j)).fcRoot X ∧
      X ∈ (Node.frame (tr.state y j)).viableHeads := by
  have hXt := mem_of_honest_anc hrun hnc hy hXW hW
  have hh' : (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ X.root).h := by
    rw [← σ_eq_honest hrun hnc hz hy hX hXt]
    exact hh
  -- the P-U frame root is `Σ.F` (not the analysis root `Store.fcRoot`)
  obtain ⟨hFX, hframe, -, -, hv⟩ := viable_head_of_floor hrun hnc hf hy hXt hh'
    (fun hm hc => Compose.honest_held_anc hrun hnc hy (hJ hm hc) hXt)
  have hΦ := (Goldilocks.Store.frame_realization _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hy j)).1
  have hsub : (Node.frame (tr.state y j)).tree ⊆ tr.HonestBlocks H :=
    fun B hB => ⟨y, hy, j, hB.1⟩
  refine ⟨hframe, AC.anc_tree_of_anc_U
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc) hΦ hsub hΦ.fcRoot_mem
    (hFX.mono (fun B hB => ⟨y, hy, j, hB⟩)) hframe, hv⟩

end Consensus.Goldilocks.Healing

end
