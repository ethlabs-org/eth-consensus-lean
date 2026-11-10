module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SuffixBest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalPasses
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ParentStop

public section

/-! # Parent viability at an honest cast under growing faults -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Two distinct viable children place their parent above the reader's root and height floor.
The children and their common parent lie in the historical honest-block universe. -/
theorem reset_parent_viable_of_children_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j)) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    {Q P B : SA.Blk sp.n (List (FG.Att sp.n))} (hQU : Q ∈ tr.HonestBlocksAt H)
    (hPQ : P.parent = some Q.root) (hBQ : B.parent = some Q.root) (hBP : B ≠ P)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hBv : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame u))
    (hQold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocksAt H) O Q) : Q ∈ ell.frame.viableHeads := by
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hPhi := Outcome.frame_realized hp.run hy hc.1
  have hPhiU := Outcome.frame_tree_subset hp.run hy hc.1
  obtain ⟨hQt, hfQ'⟩ := parent_mem_frame_of_children hU hPhi hPhiU hQU hPQ hBQ hBP
    hPv.1.1 hPv.2.1 hBv.1.1 hBv.2.1
  rw [Outcome.frame_of_call hp.run hy hc.1] at hQt hfQ' ⊢
  exact ⟨hQt.1, hQt.2, hfQ'.mono (fun X hX => hX.1),
    hp.reset_vote_floor_above_old_at hy hR hc hes hjb hQt.1 hQold⟩

open Regimes.Growing (hold)

/-- View agreement preserves an old child's lack of a strict majority. -/
theorem reset_old_child_ineligible_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts (s + 1 : Nat) + hold sp)) (hdesignated : p = proposer (s + 1))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hPQ : P.parent = some d.head.root) (hy : y ∈ H (tr.time j))
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j elly e)
    (hes : e.msg.slot = s + 1) (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i) (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hQt : d.head ∈ ellp.frame.tree) (hQv : d.head ∈ ellp.frame.viableHeads)
    (hQvy : d.head ∈ elly.frame.viableHeads)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)))
    (hBQ : B.parent = some d.head.root) (hBs : B.slot < s + 1) :
    ¬ SA.goldfishEligible sp elly.frame (tr.time j)
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B := by
  have hpI : p ∈ H (tr.time i) := hp.run.antitone
    (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hPhi := Outcome.frame_realized hp.run hpI hci
  have hBP : B ≠ P := by rintro rfl; omega
  have hBv := hp.reset_competitor_reflect_at hc hpH hdesignated hactual hPs hci hti hy hcy
    hes hib hgi hjoi hQt hPQ .refl hBP hQv hBQ hB
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  obtain ⟨heq, hvot, hsup⟩ := hp.reset_views_agree_at hc hpH hdesignated hactual hPs
    hci hcall hd hti hpay hy hcy hes hib hjb hPy hg hgi hgj hjoi hjoj
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg j)
  have hcy' := SA.upTo_castAt.mpr (And.intro le_rfl hcy)
  have hsj : sp.slot (tr.time j) = s + 1 :=
    ((SA.castAt_spec hr hy hcy').2.1).symm.trans hes
  exact old_child_ineligible_of_views hPhi hd hslot heq hvot hsup hsj hQvy hBv hB.1.1 hBQ hBs

/-- At the proposal parent the actual proposal is the unique eligible child, and has no
eligible child itself. Each reader is honest only at its own observation. -/
theorem reset_stop_at_parent_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p y : Fin sp.n} {k i j s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts (s + 1 : Nat) + hold sp))
    (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1) (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
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
    (hQt : d.head ∈ ellp.frame.tree) (hQv : d.head ∈ ellp.frame.viableHeads) :
    (P ∈ {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} ∧
      ∀ B ∈ {B | B ∈ elly.frame.viableTree
          (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B}, B = P) ∧
    ¬ ∃ C, SA.IsBest sp (SA.goldfishScore sp elly.frame
      (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s)
      {B | B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp elly.frame (tr.time j)
          (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B} C := by
  have hpI : p ∈ H (tr.time i) := hp.run.antitone
    (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hac.localRun.upTo (hp.run.time_nonneg j)
  have hcy' := SA.upTo_castAt.mpr (And.intro le_rfl hcy)
  have hsj : sp.slot (tr.time j) = s + 1 :=
    ((SA.castAt_spec hr hy hcy').2.1).symm.trans hes
  have hPhiU := Outcome.frame_tree_subset hp.run hpI hci
  have hPsi := Outcome.frame_realized hp.run hy hcy.1
  have hPsiU := Outcome.frame_tree_subset hp.run hy hcy.1
  have hU := hac.localRun.coherent
  have hslot : ∀ B ∈ elly.frame.tree, B.slot ≤ sp.slot (tr.time j) :=
    SA.frame_slot_le sp hr hy hcy'.1
  have old : ∀ B ∈ elly.frame.viableTree (SA.voterBlockTree sp e.readPoint elly.frame (s + 1)),
      B.parent = some d.head.root → B.slot < s + 1 →
      ¬ SA.goldfishEligible sp elly.frame (tr.time j)
        (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s B := by
    intro B hB hBQ hBs
    have hBP : B ≠ P := by rintro rfl; omega
    have hQvy := hp.reset_parent_viable_of_children_at hy hR hcy hes hjb (hPhiU hQt) hPQ hBQ
      hBP hPv hB (fun x r l O ho ht _ => hp.reset_proposal_passes_at hc hpI hR hci hcall hd
        hti hib O ⟨x, r, l, ho, ht⟩)
    exact hp.reset_old_child_ineligible_at hc hpH hdesignated hactual hPs hci hcall hd hti
      hpay hPQ hy hcy hes hib hjb hPv.1.1 hg hgi hgj hjoi hjoj hQt hQv hQvy hB hBQ hBs
  refine ⟨⟨⟨hPv, hPQ, Or.inr (Or.inl (hPs.trans hsj.symm))⟩, ?_⟩, ?_⟩
  · intro B hB
    rcases Nat.lt_or_ge B.slot (s + 1) with hlt | hge
    · exact False.elim (old B hB.1 hB.2.1 hlt hB.2.2)
    have hBs : B.slot = s + 1 := le_antisymm (hsj ▸ hslot B hB.1.1.1) hge
    have hj : tr.time j ≤ sp.ts (s + 1 : Nat) + hold sp := by
      have hbound : tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ :=
        SA.vote_time_le hr hy ⟨elly, hcy'⟩
      simpa only [hsj, hold] using hbound
    exact Outcome.proposal_unique_before_hold hp.run hp.noColl hpH hdesignated hactual hPs
      (by omega) hy hcy.1 hj hB.1.1.1 hBs
  · rintro ⟨C, ⟨⟨hCv, hCP, _⟩, _⟩⟩
    have h1 := hU.2 P (hPsiU hPv.1.1) C (hPsiU hCv.1.1) hCP
    have h2 := hslot C hCv.1.1
    omega

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
