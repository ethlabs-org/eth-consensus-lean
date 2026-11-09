module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Sleepy
import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
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

public section

/-! # Goldilocks under `Sleepy`: the latest view's votes at a read

The facts on the latest view that the served head (`Compose/Sleepy/Served`) and its steps
(`Compose/Sleepy/ServedSteps`) share: the votes of the latest view are honest slot votes
(`mem_latest_votes`), the FG tree grows (`fg_grows`), the latest view is in the frame
(`latestView_mem`), and its honest supporter of a target with honest votes
(`latest_honest_supporter_of_target_votes`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- A vote of the slot-`L` pool of an honest node is a vote of its latest view, of slot `L`. -/
theorem mem_latest_votes (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i L : Nat} {t : Time}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    {u : Vote sp.n} (hu : u ∈ (tr.projAC.state y i).pool L) :
    u ∈ (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1.votes := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hus : u.slot = L := SA.state_pool_slot sp hr hy i L u hu
  have hst : (tr.projAC.state y i).voteStamp u < ⊤ := by
    rcases SA.pool_origin hr hy i u (hus ▸ hu) with ⟨k, -, -, h, -⟩ | ⟨k, -, -, -, -, h, -⟩ <;>
      rw [h] <;> exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  rw [projAC_state hrun.toLocalRun hy] at hu hst
  simp only [SA.latestView] at hL ⊢
  rw [← hL]
  simp [SA.voteView, SA.voteViewList, SA.View.ofLists, SA.SAState.poolAt, hu, hst]

/-- The FG state of an honest node only grows: its tree, and its finalized tip, to a descendant. -/
theorem fg_grows (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {j i : Nat}
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
theorem latestView_mem {A : SA.SAState sp.n} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {t : Time} {L : Nat} (hL : (L : Int) = (SA.latestView sp A Φ t).2) (v : Vote sp.n) :
    (v ∈ (SA.latestView sp A Φ t).1.votes ↔ v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧
      (v ∈ (SA.latestView sp A Φ t).1.support ↔
        (v ∈ A.pool L ∧ A.voteStamp v < ⊤) ∧ SA.resolutionTime A Φ v < ⊤) := by
  simp only [SA.latestView] at hL ⊢
  rw [← hL]
  simp only [SA.voteView, SA.voteViewList, SA.View.ofLists, SA.SAState.poolAt, Set.mem_ofPred_eq,
    List.mem_filter, decide_eq_true_eq, Int.natCast_nonneg, not_lt.2, ↓reduceIte, Int.toNat_natCast,
    and_assoc, true_and]

/-- Honest latest-view voters support a held target when their votes extend it and their
heads are relayed with finite stamps. The target-vote and relay premises are independent of
the invariant and service window used to establish them. -/
theorem latest_honest_supporter_of_target_votes (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {t : Time}
    {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ (Node.frame (tr.state y i)).tree) {L : Nat}
    (hL : (L : Int) = (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (hvotes : ∀ z ∈ H, ∀ q < i, ∀ e, SA.VoteAt tr.projAC z q e → e.msg.slot = L →
      SA.VoteExtends (tr.HonestBlocks H) e.msg R)
    (hrelay : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = L →
      ∀ Hd ∈ tr.HonestBlocks H, Hd.root = e.msg.head →
        Anc (tr.HonestBlocks H) (tr.state y i).fg.F Hd →
        Hd ∈ (Node.frame (tr.state y i)).tree ∧ (tr.projAC.state y i).blockStamp Hd.root < ⊤) :
    ∀ w ∈ SA.voters (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
        t).1.votes, w ∈ H →
      w ∈ SA.supporters (Node.frame (tr.state y i))
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).1
        (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2 R := by
  intro w ⟨v, hvV, hvw⟩ hwH
  subst hvw
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hΦ : FrameOK (Node.frame (tr.state y i)) :=
    (Store.frame_realization _ _ _ _ (fg_reachable hrun.toLocalRun hy i)).1
  have hΦU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX.1⟩
  have hst := projAC_state hrun.toLocalRun hy i
  have hpool : ∀ u ∈ (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i))
      t).1.votes, u ∈ (tr.projAC.state y i).pool L ∧ u.slot = L := fun u hu => by
    have h := ((latestView_mem hL u).1.1 hu).1
    rw [← hst] at h
    exact ⟨h, SA.state_pool_slot sp hr hy i L u h⟩
  obtain ⟨hvp, hvs⟩ := hpool v hvV
  -- the vote is `v.val`'s own, of slot `L`, and extends `R` (S2)
  obtain ⟨j', hj', e, hve, hev⟩ := hrun'.honest.pool_vote y hy i L v hvp hwH
  obtain ⟨Hd, hHdU, hHdr, hRHd⟩ := hvotes v.val hwH j' hj' e hve (by rw [hev, hvs])
  have hF : Anc (tr.HonestBlocks H) (tr.state y i).fg.F Hd :=
    ((hΦ.rooted.2 R hR).mono hΦU).trans hRHd
  obtain ⟨hHdΦ, hbst⟩ := hrelay v.val hwH j' e hve (by rw [hev, hvs]) Hd hHdU hHdr hF
  obtain ⟨Hd₂, hHd₂, hHd₂r, hHd₂s⟩ := SA.honest_head hrun' hwH hve
  obtain rfl : Hd = Hd₂ := hU.1 hHdU hHd₂ (hHdr.trans hHd₂r.symm)
  rw [hev] at hHdr hHd₂s
  -- the vote is resolved
  have hvst : (tr.state y i).ac.voteStamp v < ⊤ := ((latestView_mem hL v).1.1 hvV).2
  have hres : SA.resolutionTime (tr.state y i).ac (Node.frame (tr.state y i)) v < ⊤ := by
    unfold SA.resolutionTime
    rw [← hHdr, SA.lookup_of_mem hΦ hHdΦ]
    dsimp only
    simp only [not_lt.2 hHd₂s, ↓reduceIte]
    rw [← hst] at hvst ⊢
    exact max_lt hvst hbst
  -- an honest validator does not equivocate
  have hne : v.val ∉ SA.equivocators (SA.latestView sp (tr.state y i).ac
      (Node.frame (tr.state y i)) t).1.votes := by
    rintro ⟨a, ha, b, hb, hab, hav, hbv⟩
    obtain ⟨hap, has⟩ := hpool a ha
    obtain ⟨hbp, hbs⟩ := hpool b hb
    obtain ⟨ja, -, ea, hea, hea'⟩ := hrun'.honest.pool_vote y hy i L a hap (by rw [hav]; exact hwH)
    obtain ⟨jb, -, eb, heb, heb'⟩ := hrun'.honest.pool_vote y hy i L b hbp (by rw [hbv]; exact hwH)
    rw [hav] at hea
    rw [hbv] at heb
    obtain ⟨-, rfl⟩ := SA.one_vote_per_slot sp _ ro H _ _ hr v.val hwH ja jb ea eb hea heb
      (by rw [hea', heb', has, hbs])
    exact hab (hea'.symm.trans heb')
  refine ⟨hne, v, (latestView_mem hL v).2.2 ⟨(latestView_mem hL v).1.1 hvV, hres⟩, rfl,
    by rw [hvs]; exact hL, Hd, hHdΦ, hHdr, SA.anc_tree_of_anc_U hU hΦ hΦU hR hRHd hHdΦ⟩

end Consensus.Goldilocks.Compose

end
