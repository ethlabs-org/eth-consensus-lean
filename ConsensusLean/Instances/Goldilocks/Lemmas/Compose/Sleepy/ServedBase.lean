module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.CommitteeRun
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Unlock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Service

public section

/-! # Goldilocks under `Sleepy`: the latest view's votes at a read

The facts on the latest view that the served head (`Compose/Sleepy/Served`) and its steps
(`Compose/Sleepy/ServedSteps`) share: slot-pool votes appear in the latest view
(`mem_latest_votes`), the FG tree grows (`fg_grows`), and the latest view's votes and
support are characterized by their stamps (`latestView_mem`). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams Vote Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- A vote of the slot-`L` pool of an honest node is a vote of its latest view, of slot `L`. -/
theorem mem_latest_votes {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i L : Nat} {t : Time}
    (hL : (L : Int) = (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    {u : Vote sp.n} (hu : u ∈ (tr.projAC.state y i).pool L) :
    u ∈ (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hus : u.slot = L := AC.state_pool_slotU sp hr.toU hrun.vstart hy i L u hu
  have hst : (tr.projAC.state y i).voteStamp u < ⊤ := by
    rcases AC.pool_origin hr hrun.vstart hy i u (hus ▸ hu) with
      ⟨k, -, -, h, -⟩ | ⟨k, -, -, -, -, h, -⟩ <;>
      rw [h] <;> exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  rw [projAC_state hrun.toLocalRun hy] at hu hst
  simp only [AC.latestView] at hL ⊢
  rw [← hL]
  simp [AC.voteView, AC.voteViewList, AC.View.ofLists, AC.ACState.poolAt, hu, hst]

/-- The FG state of an honest node only grows: its tree, and its finalized tip, to a descendant. -/
theorem fg_grows {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j i : Nat}
    (h : j ≤ i) : (tr.state y j).fg.tree ⊆ (tr.state y i).fg.tree ∧
      Anc (tr.HonestBlocks H) (tr.state y j).fg.F (tr.state y i).fg.F := by
  induction i, h using Nat.le_induction with
  | base => exact ⟨subset_rfl, .refl⟩
  | succ i _ ih =>
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      obtain ⟨-, hT, hF⟩ := chain_fg y (.cons (hrun.cutLaw y hy i c hc) (.nil _))
        (fg_reachable hrun.toLocalRun hy i)
      rw [tr.state_succ_of_call hc]
      refine ⟨ih.1.trans hT, ih.2.trans (hF.mono fun X hX => ⟨y, hy, i + 1, ?_⟩)⟩
      rwa [tr.state_succ_of_call hc]
    · rw [tr.state_succ_of_not fun c h => hc ⟨c, h⟩]
      exact ih

/-- The votes and the support of the latest view, of slot `L`. -/
theorem latestView_mem {A : AC.ACState sp.n} {Φ : AC.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {L : Nat} (hL : (L : Int) = (AC.latestView sp A Φ t).2) (v : Vote sp.n) :
    (v ∈ (AC.latestView sp A Φ t).1.votes ↔ v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧
      (v ∈ (AC.latestView sp A Φ t).1.support ↔
        (v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧ AC.resolutionTime A Φ v < ⊤) := by
  simp only [AC.latestView] at hL ⊢
  rw [← hL]
  simp only [AC.voteView, AC.voteViewList, AC.View.ofLists, AC.ACState.poolAt, Set.mem_ofPred_eq,
    List.mem_filter, decide_eq_true_eq, Int.natCast_nonneg, not_lt.2, ↓reduceIte, Int.toNat_natCast,
    and_assoc, true_and]

end Consensus.Goldilocks.Compose

end
