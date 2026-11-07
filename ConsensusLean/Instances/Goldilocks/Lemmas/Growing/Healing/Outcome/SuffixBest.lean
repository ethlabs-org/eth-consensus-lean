module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ViewsAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SuffixFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A best child on the proposal-parent path stays best at the voter, under growing faults

`reset_suffix_best_at`, the growing form of `Healing.ResetPremisesUpTo.reset_suffix_best`
(`Healing/Outcome/SupplierViews`): the winner is transported through the viable proposal
(`reset_winner_voter_tree_at`), competitors reflect through guarded relay
(`reset_competitor_reflect_at`), and the scores agree (`reset_views_agree_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **A best child on the proposal-parent path stays best at the voter.** The winner is
transported through the viable proposal, while competitors reflect through guarded relay. -/
theorem reset_suffix_best_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p y : Fin sp.n} {k i j s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts (s + 1 : Nat) + hold sp))
    (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H (tr.time j)) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPv : P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQt : d.head ∈ ellp.frame.tree) (hXQ : ellp.frame.Anc X d.head)
    (hne : X ≠ d.head) (hXv : X ∈ ellp.frame.viableHeads)
    (hCQ : ellp.frame.Anc C d.head)
    (haX : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint elly.frame (tr.time j)) X)
    (hC : SA.IsBest sp (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp ellp.frame (tr.time i) (SA.View.ofLists pay) s B} C) :
    SA.IsBest sp (SA.goldfishScore sp elly.frame
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some X.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hrun := hp.run
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hpi : p ∈ H (tr.time i) := hrun.antitone (by
    rw [hti]
    change sp.ts (s + 1 : Nat) ≤ sp.ts (s + 1 : Nat) + sp.Δ
    linarith [sp.toParams.hΔ]) hpH
  have hPhi := Outcome.frame_realized hrun hpi hci
  have hPhiU := Outcome.frame_tree_subset hrun hpi hci
  have hPsiU := Outcome.frame_tree_subset hrun hy hcy.1
  obtain ⟨heq, hvot, hsup⟩ := hp.reset_views_agree_at hc hpH hdesignated hactual hPs
    hci hcall hd hti hpay hy hcy hes hib hjb hPv.1.1 hg hgi hgj hjoi hjoj
  have hQP : Anc (tr.HonestBlocksAt H) d.head P :=
    .single ⟨hPhiU hQt, hPsiU hPv.1.1, hPQ⟩
  have hXC : Anc (tr.HonestBlocksAt H) X C :=
    .single ⟨hPhiU (SA.mem_of_anc hXQ hQt), hPhiU hC.1.1.1, hC.1.2.1⟩
  have hCy := hp.reset_winner_voter_tree_at hy hcy hes hPv
    ((hCQ.mono hPhiU).trans hQP) (haX.trans hXC)
  have hCs : C.slot < s + 1 := by
    have h1 := (Anc.slot_le hPhi.coherent hCQ).1
    have h2 := hU.2 d.head (hPhiU hQt) P (hPsiU hPv.1.1) hPQ
    omega
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  apply SA.isBest_transfer hXv (by omega) hvot ?_ (fun B hB => hB.1)
    (fun B hB => hB.1.1) hCy ?_ hC
  · intro B hBp hBy
    simp only [SA.goldfishScore, heq, hsup B hBp hBy]
  · intro B hB hBX
    have hBP : B ≠ P := by
      rintro rfl
      exact hne (hU.1 (hPhiU (SA.mem_of_anc hXQ hQt)) (hPhiU hQt)
        (Option.some_injective _ (hBX.symm.trans hPQ)))
    exact hp.reset_competitor_reflect_at hc hpH hdesignated hactual hPs hci hti hy hcy hes
      hib hgi hjoi hQt hPQ hXQ hBP hXv hBX hB

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
