module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ViewsAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SuffixFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SuffixTransfer
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A best child on the proposal-parent path stays best at the voter, under growing faults

`reset_suffix_best_at`, the growing form of `Healing.ResetPremisesUpTo.reset_suffix_best`
(`Healing/Outcome/SupplierViews`), from the frame step `Healing.suffix_best_of_views`
(`Healing/Outcome/SuffixTransfer`): the winner is transported through the viable proposal
(`reset_winner_voter_tree_at`), competitors reflect through guarded relay
(`reset_competitor_reflect_at`), and the views agree (`reset_views_agree_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {fgHold : Time}

/-- **A best child on the proposal-parent path stays best at the voter.** The winner is
transported through the viable proposal, while competitors reflect through guarded relay. -/
theorem reset_suffix_best_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK fgHold)
    {p y : Fin sp.n} {k i j s : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts (s + 1 : Nat) + hold sp))
    (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H (tr.time j)) {e : AC.Em sp (List (FG.Att sp.n))}
    (hcy : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPv : P ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : AC.gbar g ≤ sp.ts s)
    (hgi : AC.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : AC.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {X C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hQt : d.head ∈ ellp.frame.tree) (hXQ : ellp.frame.Anc X d.head)
    (hne : X ≠ d.head) (hXv : X ∈ ellp.frame.viableHeads)
    (hCQ : ellp.frame.Anc C d.head)
    (haX : Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint elly.frame (tr.time j)) X)
    (hC : AC.IsBest sp (AC.headScore sp ellp.frame (AC.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        AC.headEligible sp ellp.frame (tr.time i) (AC.View.ofLists pay) s B} C) :
    AC.IsBest sp (AC.headScore sp elly.frame
      (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (AC.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some X.root ∧ AC.headEligible sp elly.frame (tr.time j)
          (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hc := hp.catchUp
  have hrun := hp.run
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by
    rw [hti]
    change sp.ts (s + 1 : Nat) ≤ sp.ts (s + 1 : Nat) + sp.Δ
    linarith [sp.toParams.hΔ]) hpH
  have hPhi := Outcome.frame_realized hrun hpi hci
  have hPhiU := Outcome.frame_tree_subset hrun hpi hci
  have hPsiU := Outcome.frame_tree_subset hrun hy hcy.1
  exact suffix_best_of_views hU hPhi hPhiU hPsiU (fun _ hB => hB.1.1) hti
    (hp.reset_views_agree_at hpH hdesignated hactual hPs hci hcall hd hti hpay hy hcy hes hib
      hjb hPv.1.1 hg hgi hgj hjoi hjoj)
    hQt hPQ hPs hPv.1.1 hXQ hne hXv hCQ
    (fun hCP hXC => hp.reset_winner_voter_tree_at hy hcy hes hPv hCP (haX.trans hXC))
    (fun B hB hBP hBX => hp.reset_competitor_reflect_at hpH hdesignated hactual hPs hci hti hy
      hcy hes hib hgi hjoi hQt hPQ hXQ hBP hXv hBX hB) hC

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
