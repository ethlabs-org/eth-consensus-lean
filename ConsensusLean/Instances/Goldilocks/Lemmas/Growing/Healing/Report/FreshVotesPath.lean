module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ParentStop
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalPath
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Following the actual proposal walk at an independently honest cast -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Above both anchors, the proposer's actual winner remains the voter's winner. -/
theorem FrameWindow.proposal_suffix_before_at {g ΔF b : Time} {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hstartX : ellp.frame.Anc d.start X) (hXQ : ellp.frame.Anc X d.head) (hne : X ≠ d.head)
    (hanchorX : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hC : SA.IsBest sp (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s B} C)
    (hstock : sp.committeeSize = sp.n) :
    SA.IsBest sp (SA.goldfishScore sp ell.frame
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)
      {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some X.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B} C := by
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hri := (hac.upTo (hr.time_nonneg i)).localRun
  have hPhi := SA.frameIn_of_callAt hri hy hci
  have hz' : z ∈ H (tr.time ip) := hr.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg ip)).localRun hz' hcp'
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      have hs := (SA.castAt_spec hri hy ⟨hci, hc.2⟩).2.1.symm.trans hes
      change sp.slot (tr.time i) = s + 1 at hs
      rw [hs])
  have hipb : sp.ts (s + 1 : Nat) ≤ b := hlo.trans hib
  have hviable : ∀ X ∈ ellp.frame.tree, X ∈ ell.frame.viableHeads →
      X ∈ ellp.frame.viableHeads := by
    intro X hXt hXv
    have hiplo : sp.ts s₀ ≤ tr.time ip := by
      rw [hti]; exact (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
    have hiphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
      rw [hti]; linarith only [sp.toParams.hΔ]
    rw [(hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc.1) hy).1] at hXv
    rw [(hrun.cutLaw z ip _ (Compose.projAC_callAt.mp hcp) hz').1] at hXt ⊢
    exact hframe.viableHead_transfer_at hrun hnc hz' hy
      (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hr.time_nonneg ip) (hti ▸ hipb)))
      hiplo hiphi (hiplo.trans (hti ▸ hlo)) hhigh hXv hXt
  exact suffix_best_of_proposal_walk hac.localRun.coherent hPhip.1 hPhip.2 hPhi.1 hPhi.2
    (SA.proposal_slot (tr := tr.projAC) hti) (proposal_walk_end_at hrun hnc hz' hcp hpay) hPs
    hparent hPv
    (proposal_views_agree_before_at hrun hnc hsvc hawake hf hcatch hnr hm hz
      hdesignated hactual hPs ⟨hcp, hcall, d, hpay⟩ hti hpayload hy hc hes hPv.1.1 hib hstock)
    (fun X B hXt hrootX hBX hne hB => hframe.frozen_competitor_reflect_at hrun hnc hsvc hcatch
      hnr hf hm hs₀ hz hdesignated hactual hPs hcp hcall hti hpay hparent hy hc hes hhigh hipb
      hXt hrootX hBX hne hB)
    hviable hstartX hXQ hne hanchorX hC

/-- The voter takes the proposal at its parent and has no eligible child beyond it. -/
theorem FrameWindow.proposal_stop_before_at {g ΔF b : Time} {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (hrootQ : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot d.head)
    (hstock : sp.committeeSize = sp.n) :
    (P ∈ {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B} ∧
      ∀ B ∈ {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B}, B = P) ∧
    ¬ ∃ C, SA.IsBest sp
      (SA.goldfishScore sp ell.frame (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)
      {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B} C := by
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hri := hac.upTo (hr.time_nonneg i)
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hPhi := SA.frameIn_of_callAt hri.localRun hy hci
  have hz' : z ∈ H (tr.time ip) := hr.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg ip)).localRun hz' hcp'
  have hslot : sp.slot (tr.time ip) = s + 1 := SA.proposal_slot (tr := tr.projAC) hti
  obtain ⟨hst, hroot, hw⟩ := proposal_walk_end_at hrun hnc hz' hcp hpay
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      have hs := (SA.castAt_spec hri.localRun hy ⟨hci, hc.2⟩).2.1.symm.trans hes
      change sp.slot (tr.time i) = s + 1 at hs
      rw [hs])
  have hipb : tr.time ip ≤ b := hti ▸ hlo.trans hib
  have hvQ := proposal_parent_viable_full_frame_at hrun hnc hz'
    (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hr.time_nonneg ip) hipb)) hcp hcall
    (s := s + 1) (by rw [sp.slotTime_eq]; simpa only [SAParams.ts] using hti) hpay
  have hQt := hPhip.1.viableHeads_subset hvQ
  have hQP : Anc (tr.HonestBlocksAt H) d.head P :=
    .single ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  have hQy := SA.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2 hPv.1.1 hQP
    ((hPhi.1.F_anc_fcRoot.mono hPhi.2).trans hrootQ)
  have hiplo : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have hiphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hti]; linarith only [sp.toParams.hΔ]
  have hvQ' : d.head ∈ (Node.frame (tr.state z ip)).viableHeads := by
    rw [← (hrun.cutLaw z ip _ (Compose.projAC_callAt.mp hcp) hz').1]
    exact hvQ
  have hQy' : d.head ∈ (Node.frame (tr.state y i)).tree := by
    rw [← (hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc.1) hy).1]
    exact hQy
  have hvQy := hframe.viableHead_transfer_at hrun hnc hy hz'
    (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hr.time_nonneg i) hib))
    (hiplo.trans (hti ▸ hlo)) hhigh hiplo hiphi hvQ' hQy'
  rw [← (hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc.1) hy).1] at hvQy
  have hng : ∀ B ∈ ell.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hB hpar hg
    obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hri.localRun hy i ell hci
    have he := hac.localRun.coherent.1 (hPhi.2 hB) hG (hg.trans hGr.symm)
    exact hpar (he ▸ hGp)
  have hv := proposal_views_agree_before_at hrun hnc hsvc hawake hf hcatch hnr hm hz
    hdesignated hactual hPs ⟨hcp, hcall, d, hpay⟩ hti hpayload hy hc hes hPv.1.1 hib hstock
  have hpH : P.proposer ∈ H (tr.time i) := hactual.2.1 ▸ hr.antitone hhigh hz
  have hcore := SA.stop_core hri hy ⟨hci, hc.2⟩ hes hPs hparent hpH hng hPv
  change _ at hcore
  simp only [show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hcore
  apply hcore
  intro B hB hBQ hBs
  have hsi := (SA.castAt_spec hri.localRun hy ⟨hci, hc.2⟩).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hsi
  exact old_child_ineligible_of_views hPhip.1 hpay hslot hv.1 hv.2.1 hv.2.2 hsi hvQy
    (hframe.frozen_competitor_reflect_at hrun hnc hsvc hcatch hnr hf hm hs₀ hz
      hdesignated hactual hPs hcp hcall hti hpay hparent hy hc hes hhigh (hlo.trans hib)
      hQt (hroot.trans (hw.anc (fun X hX => hX.1) hst)) hBQ
      (fun he => by rw [he, hPs] at hBs; omega) hB) hB.1.1 hBQ hBs

/-- Reaching the actual proposal-parent path determines the cast's head. -/
theorem FrameWindow.vote_head_eq_of_path_at {g ΔF b : Time} {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hstartX : ellp.frame.Anc d.start X) (hXQ : ellp.frame.Anc X d.head)
    (haX : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hXE : ell.frame.Anc X (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s))
    (hstock : sp.committeeSize = sp.n) : e.msg.head = P.root := by
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hri := (hac.upTo (hr.time_nonneg i)).localRun
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hPhi := SA.frameIn_of_callAt hri hy hci
  have hz' : z ∈ H (tr.time ip) := hr.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg ip)).localRun hz' hcp'
  have hrootQ : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot d.head :=
    (Anc.mono hPhi.2 ((SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)).trans haX)).trans
      (hXQ.mono hPhip.2)
  obtain ⟨hstepP, hstopP⟩ := hframe.proposal_stop_before_at hrun hnc hsvc hawake hf hcatch
    hnr hm hs₀ hz hdesignated hactual hPs hcp hcall hti hpay hpayload hparent
    hy hc hes hhigh hib hPv hrootQ hstock
  have heq := getHead_eq_of_proposal_path hPhip.1 hPhip.2 hPhi.1 hPhi.2
    (SA.proposal_slot (tr := tr.projAC) hti) (proposal_walk_end_at hrun hnc hz' hcp hpay)
    (fun _ _ hSX hXQ' hne haX' hC => hframe.proposal_suffix_before_at hrun hnc hsvc hawake hf
      hcatch hnr hm hs₀ hz hdesignated hactual hPs hcp hcall hti hpay hpayload hparent hy hc
      hes hhigh hib hPv hSX hXQ' hne haX' hC hstock)
    hstepP hstopP hstartX hXQ haX hXE
  have hspec := SA.castAt_head_of_viable hri hy ⟨hci, hc.2⟩ (hes ▸ ⟨P, hPv⟩)
  change e.msg.head = _ at hspec
  simp only [hes, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hspec
  exact hspec.trans (congrArg Block.root heq)

/-- A deeper anchor already lies on the proposal path; a shallower one uses a prefix supplier. -/
theorem FrameWindow.vote_head_eq_of_start_prefix_at {g ΔF b : Time} {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haP : Anc (tr.HonestBlocksAt H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) P)
    (hprefix : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) d.start →
      ell.frame.Anc d.start (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
        (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s))
    (hstock : sp.committeeSize = sp.n) : e.msg.head = P.root := by
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hPhi := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg i)).localRun hy hci
  have hz' : z ∈ H (tr.time ip) := hr.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg ip)).localRun hz' hcp'
  rcases anchor_on_proposal_path hac.localRun.coherent hPhip.1 hPhip.2 hPhi.1 hPhi.2
      (proposal_walk_end_at hrun hnc hz' hcp hpay) hPv.1.1 hparent haP hprefix with
    he | ⟨X, hSX, hXQ, haX, hXE⟩
  · exact vote_head_eq_of_anchor_eq_at hrun hnc hy hc (hPs.trans hes.symm) hPv.1.1 he
  · exact hframe.vote_head_eq_of_path_at hrun hnc hsvc hawake hf hcatch hnr hm hs₀ hz
      hdesignated hactual hPs hcp hcall hti hpay hpayload hparent hy hc hes hhigh hib hPv
      hSX hXQ haX hXE hstock

end Consensus.Goldilocks.Healing.Growing

end
