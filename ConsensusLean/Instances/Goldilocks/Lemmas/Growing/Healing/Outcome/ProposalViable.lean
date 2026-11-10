module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalPasses
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A held actual proposal is viable at a post-drain cast, under growing faults

`ResetPremisesUpTo.reset_proposal_viable_at`, the growing form of the static
`reset_proposal_viable` (`Healing/Outcome/SupplierViews`): the proposer honest through
`t_u + hold`, the voter at its cast. The cast's `fc_root` is below the proposal
(`reset_vote_root_below_proposal_at`), the proposal is in the voter's block tree as a current-slot
block, and its height reaches the voter's floor (`reset_vote_floor_above_old_at`): every earlier
high origin is below the proposal's parent (`reset_proposal_passes_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- (`Healing.ResetPremisesUpTo.reset_proposal_viable`, Outcome/SupplierViews.) -/
theorem reset_proposal_viable_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p y : Fin sp.n} {k i j u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + hold sp))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root)
    (hy : y ∈ H (tr.time j)) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    (hPy : P ∈ elly.frame.tree) :
    P ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame u) := by
  have hrun := hp.run
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have hpi : p ∈ H (tr.time i) :=
    hrun.antitone (by rw [hti]; have := sp.toParams.hΔ; simp only [hold]; linarith) hpH
  have hPhi := Outcome.frame_realized hrun hpi hci
  have hPhiU := Outcome.frame_tree_subset hrun hpi hci
  have hPsi := Outcome.frame_realized hrun hy hcy.1
  have hPsiU := Outcome.frame_tree_subset hrun hy hcy.1
  have hroot := hp.reset_vote_root_below_proposal_at hc hpH hactual hPs hR hci hcall hd hti hib hPQ
    hy hcy hes hjb
  have hroot' := SA.anc_tree_of_anc_U hU hPsi hPsiU hPsi.fcRoot_mem hroot hPy
  have hPt : P ∈ SA.voterBlockTree sp e.readPoint elly.frame u :=
    ⟨hPy, Or.inr ⟨P, hPy, hPs, .refl⟩⟩
  have hfr := Outcome.frame_of_call hrun hy hcy.1
  have hPyStore : P ∈ (tr.state y j).fg.tree := by
    rw [hfr] at hPy
    exact hPy.1
  have hfloor := hp.reset_vote_floor_above_old_at hy hR hcy hes hjb hPyStore
    (fun x r l O ho ht _ => by
      have hOQ := hp.reset_proposal_passes_at hc hpi hR hci hcall hd hti hib O ⟨x, r, l, ho, ht⟩
      obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
      have hQt : d.head ∈ ellp.frame.tree := by
        rcases eq_or_ne d.start d.head with he | he
        · exact he ▸ hst
        · exact (Anc.mem hsQ he).2
      exact hOQ.trans (.single ⟨hPhiU hQt, hPsiU hPy, hPQ⟩))
  refine ⟨hPt, hroot', P, hPt, ?_, .refl⟩
  rw [hfr] at hPy hroot' ⊢
  exact ⟨hPy.1, hPy.2, hroot'.mono (fun X hX => hX.1), hfloor⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
