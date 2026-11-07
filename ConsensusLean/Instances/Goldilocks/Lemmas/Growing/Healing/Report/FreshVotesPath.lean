module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
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
        SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s B} C) :
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
  have hslot : sp.slot (tr.time ip) = s + 1 := SA.proposal_slot (tr := tr.projAC) hti
  have ⟨hst, hroot, hw⟩ := proposal_walk_end_at hrun hnc hz' hcp hpay
  simp only [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hw
  have hT : ellp.frame.viableTree ellp.frame.tree ⊆ ellp.frame.tree := fun _ h => h.1
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hw.anc hT hst) he).2
  have hXt := SA.mem_of_anc hXQ hQt
  have hCQ : ellp.frame.Anc C d.head := by
    obtain ⟨f, hwalk, _⟩ := SA.walkEnd_iff.1 (hw.of_anc hPhip.1.coherent hT hstartX hXQ)
    cases f with
    | zero => exact (hne hwalk).elim
    | succ f =>
      rw [show f + 1 = 1 + f from Nat.add_comm f 1, SA.ghost_add,
        SA.ghost_succ_of_best 0 X hC] at hwalk
      exact hwalk ▸ SA.anc_ghost hT f (hT hC.1.1)
  have hCP : Anc (tr.HonestBlocksAt H) C P :=
    (hCQ.mono hPhip.2).tail ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  have hXC : Anc (tr.HonestBlocksAt H) X C :=
    .single ⟨hPhip.2 hXt, hPhip.2 hC.1.1.1, hC.1.2.1⟩
  have hfX := ((SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)).mono hPhi.2).trans hanchorX
  have hfC := hfX.trans hXC
  have hCt := SA.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2 hPv.1.1 hCP
    ((hPhi.1.F_anc_fcRoot.mono hPhi.2).trans hfC)
  have hCPy := SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hCt hCP hPv.1.1
  have hCy : C ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) :=
    ⟨⟨hCt, Or.inr ⟨P, hPv.1.1, hPs, hCPy⟩⟩,
      SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hPhi.1.fcRoot_mem hfC hCt,
      hPv.2.2.choose, hPv.2.2.choose_spec.1, hPv.2.2.choose_spec.2.1,
      hCPy.trans hPv.2.2.choose_spec.2.2⟩
  have hXy := SA.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2 hCt hXC
    ((hPhi.1.F_anc_fcRoot.mono hPhi.2).trans hfX)
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      have hs := (SA.castAt_spec hri hy ⟨hci, hc.2⟩).2.1.symm.trans hes
      change sp.slot (tr.time i) = s + 1 at hs
      rw [hs])
  have hipb : sp.ts (s + 1 : Nat) ≤ b := hlo.trans hib
  have hv := proposal_views_agree_before_at hrun hnc hsvc hawake hf hcatch hnr hm hz
    hdesignated hactual hPs ⟨hcp, hcall, d, hpay⟩ hti hpayload hy hc hes hPv.1.1 hib
  have hsc : ∀ B ∈ ellp.frame.tree, B ∈ ell.frame.tree →
      SA.goldfishScore sp ell.frame (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B =
        SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s B := by
    intro B hBp hBy
    simp only [SA.goldfishScore, hv.1, hv.2.2 B hBp hBy]
  have hrefl : ∀ B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)),
      B.parent = some X.root → B ∈ ellp.frame.viableTree ellp.frame.tree := by
    intro B hB hBX
    apply hframe.frozen_competitor_reflect_at hrun hnc hsvc hcatch hnr hf hm hs₀ hz hdesignated
      hactual hPs hcp hcall hti hpay hparent hy hc hes hhigh hipb hXt (hroot.trans hstartX) hBX _ hB
    intro he
    subst B
    exact hne (hPhip.1.coherent.1 hXt hQt (Option.some.inj (hBX.symm.trans hparent)))
  by_cases hXv : X ∈ ellp.frame.viableHeads
  · have hCs : C.slot ≠ sp.slot (tr.time ip) := by
      have hle := (Anc.slot_le hPhip.1.coherent hCQ).1
      have hlt := hac.localRun.coherent.2 d.head (hPhip.2 hQt) P (hPhi.2 hPv.1.1) hparent
      omega
    exact SA.isBest_transfer hXv hCs hv.2.1 hsc hT (fun _ h => h.1.1) hCy hrefl hC
  · have hXnv : X ∉ ell.frame.viableHeads := by
      intro hXv'
      have hiplo : sp.ts s₀ ≤ tr.time ip := by
        rw [hti]; exact (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
      have hiphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
        rw [hti]; linarith only [sp.toParams.hΔ]
      have hvX : X ∈ (Node.frame (tr.state y i)).viableHeads := by
        rw [← (hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc.1) hy).1]
        exact hXv'
      have htX : X ∈ (Node.frame (tr.state z ip)).tree := by
        rw [← (hrun.cutLaw z ip _ (Compose.projAC_callAt.mp hcp) hz').1]
        exact hXt
      have hvp := hframe.viableHead_transfer_at hrun hnc hz' hy
        (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hr.time_nonneg ip) (hti ▸ hipb)))
        hiplo hiphi (hiplo.trans (hti ▸ hlo)) hhigh hvX htX
      rw [← (hrun.cutLaw z ip _ (Compose.projAC_callAt.mp hcp) hz').1] at hvp
      exact hXv hvp
    refine SA.isBest_transfer_low (fun W hW hr => hXv ?_) (fun W hW hr => hXnv ?_)
      hsc hT (fun _ h => h.1.1) hCy hrefl hC
    · rwa [hPhip.1.coherent.1 (hPhip.1.viableHeads_subset hW) hXt hr] at hW
    · rwa [hPhi.1.coherent.1 (hPhi.1.viableHeads_subset hW) hXy hr] at hW

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
    (hrootQ : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot d.head) :
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
  simp only [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hw
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
    hdesignated hactual hPs ⟨hcp, hcall, d, hpay⟩ hti hpayload hy hc hes hPv.1.1 hib
  have hstop := (SA.walkEnd_iff.1 hw).choose_spec.2
  have hpH : P.proposer ∈ H (tr.time i) := hactual.2.1 ▸ hr.antitone hhigh hz
  have hcore := SA.stop_core hri hy ⟨hci, hc.2⟩ hes hPs hparent hpH hng hPv
  change _ at hcore
  simp only [show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hcore
  apply hcore
  intro B hB hBQ hBs hel
  have hBp := hframe.frozen_competitor_reflect_at hrun hnc hsvc hcatch hnr hf hm hs₀ hz
    hdesignated hactual hPs hcp hcall hti hpay hparent hy hc hes hhigh (hlo.trans hib)
    hQt (hroot.trans (hw.anc (fun X hX => hX.1) hst)) hBQ
    (fun he => by rw [he, hPs] at hBs; omega) hB
  have hsc : SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s B =
      SA.goldfishScore sp ell.frame (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B := by
    simp only [SA.goldfishScore, hv.1, hv.2.2 B hBp.1 hB.1.1]
  have help : SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s B := by
    rcases hel with hn | hs | hmj
    · exact (hn ⟨d.head, hvQy, hBQ⟩).elim
    · have hsi := (SA.castAt_spec hri.localRun hy ⟨hci, hc.2⟩).2.1.symm.trans hes
      change sp.slot (tr.time i) = s + 1 at hsi
      change B.slot = sp.slot (tr.time i) at hs
      omega
    · exact Or.inr (Or.inr (by rw [hv.2.1, hsc]; exact hmj))
  exact hstop (SA.exists_isBest hPhip.1
    (S := {C | C ∈ ellp.frame.viableTree ellp.frame.tree ∧ C.parent = some d.head.root ∧
      SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s C})
    (fun C hC => hC.1.1) ⟨B, hBp, hBQ, help⟩ _)

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
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)) : e.msg.head = P.root := by
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
  have hslot : sp.slot (tr.time ip) = s + 1 := SA.proposal_slot (tr := tr.projAC) hti
  obtain ⟨hst, _, hw⟩ := proposal_walk_end_at hrun hnc hz' hcp hpay
  simp only [hslot, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hw
  have hTp : ellp.frame.viableTree ellp.frame.tree ⊆ ellp.frame.tree := fun _ h => h.1
  have hTy : ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ⊆
      ell.frame.tree := fun _ h => h.1.1
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hw.anc hTp hst) he).2
  have hXt := SA.mem_of_anc hXQ hQt
  have hrootQ : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot d.head :=
    (Anc.mono hPhi.2 ((SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)).trans haX)).trans
      (hXQ.mono hPhip.2)
  obtain ⟨hstepP, hstopP⟩ := hframe.proposal_stop_before_at hrun hnc hsvc hawake hf hcatch
    hnr hm hs₀ hz hdesignated hactual hPs hcp hcall hti hpay hpayload hparent
    hy hc hes hhigh hib hPv hrootQ
  obtain ⟨f, hwalk, hstop⟩ := SA.walkEnd_iff.1 (hw.of_anc hPhip.1.coherent hTp hstartX hXQ)
  have hfollow := SA.ghost_follow f X hwalk hstop (fun m hm' hne C hC => by
    have hXm := SA.anc_ghost (score := SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      (eligible := SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s) hTp m hXt
    have hmt : SA.ghost sp (ellp.frame.viableTree ellp.frame.tree)
        (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
        (SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s) m X ∈
        ellp.frame.tree := by
      rcases eq_or_ne X (SA.ghost sp (ellp.frame.viableTree ellp.frame.tree)
        (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
        (SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s) m X) with he | he
      · exact he ▸ hXt
      · exact (Anc.mem hXm he).2
    have hmQ : ellp.frame.Anc
        (SA.ghost sp (ellp.frame.viableTree ellp.frame.tree)
          (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
          (SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s) m X) d.head := by
      have hend := hwalk
      rw [show f = m + (f - m) by omega, SA.ghost_add] at hend
      exact hend ▸ SA.anc_ghost hTp (f - m) hmt
    exact hframe.proposal_suffix_before_at hrun hnc hsvc hawake hf hcatch hnr hm hs₀ hz
      hdesignated hactual hPs hcp hcall hti hpay hpayload hparent hy hc hes hhigh hib hPv
      (hstartX.trans hXm) hmQ hne ((haX.mono hPhi.2).trans (hXm.mono hPhip.2)) hC)
    hstepP hstopP
  let sc := SA.goldfishScore sp ell.frame (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s
  let el := SA.goldfishEligible sp ell.frame (tr.time i)
    (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s
  have hvoter : SA.WalkEnd (sp := sp)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1))) sc el
      (SA.getAnchor sp e.readPoint ell.frame (tr.time i))
      (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
        (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) :=
    SA.walkEnd_ghost hPhi.1.coherent hTy (hPhi.1.finite.subset hTy)
      (Set.ncard_le_ncard hTy hPhi.1.finite) _
  have heq := (hvoter.of_anc hPhi.1.coherent hTy haX hXE).unique
    (SA.walkEnd_iff.2 ⟨f + 1, hfollow, hstopP⟩)
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
        (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)) : e.msg.head = P.root := by
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hPhi := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg i)).localRun hy hci
  have hz' : z ∈ H (tr.time ip) := hr.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg ip)).localRun hz' hcp'
  obtain ⟨hst, _, hw⟩ := proposal_walk_end_at hrun hnc hz' hcp hpay
  have hstartQ := hw.anc (fun X hX => hX.1) hst
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hstartQ he).2
  have hQP : Anc (tr.HonestBlocksAt H) d.head P :=
    .single ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  let A := SA.getAnchor sp e.readPoint ell.frame (tr.time i)
  have hAt : A ∈ ell.frame.tree := by
    by_cases he : ell.frame.fcRoot = A
    · exact he ▸ hPhi.1.fcRoot_mem
    · exact (Anc.mem (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)) he).2
  by_cases he : A = P
  · exact vote_head_eq_of_anchor_eq_at hrun hnc hy hc (hPs.trans hes.symm) hPv.1.1 he
  have hAQ : Anc (tr.HonestBlocksAt H) A d.head := by
    rcases Relation.ReflTransGen.cases_tail haP with heq | ⟨Y, hAY, hYP⟩
    · exact (he heq.symm).elim
    have hYQ : Y = d.head := hac.localRun.coherent.1 hYP.1 (hPhip.2 hQt)
      (Option.some.inj (hYP.2.2.symm.trans hparent))
    exact hYQ ▸ hAY
  rcases Anc.total hac.localRun.coherent hAQ (Anc.mono hPhip.2 hstartQ) with hAS | hSA
  · have hSt := SA.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2 hPv.1.1
      ((Anc.mono hPhip.2 hstartQ).trans hQP)
      ((Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans
        (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)))).trans hAS)
    have hASf := SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hAt hAS hSt
    exact hframe.vote_head_eq_of_path_at hrun hnc hsvc hawake hf hcatch hnr hm hs₀ hz
      hdesignated hactual hPs hcp hcall hti hpay hpayload hparent hy hc hes hhigh hib hPv
      .refl hstartQ hASf (hprefix hASf)
  · have hApt := SA.frame_mem_of_between sp hac.localRun.coherent hPhip.1 hPhip.2 hQt hAQ
      (Anc.mono hPhip.2 (hPhip.1.F_anc_fcRoot.trans
        (proposal_walk_end_at hrun hnc hz' hcp hpay).2.1) |>.trans hSA)
    have hSAf := SA.anc_tree_of_anc_U hac.localRun.coherent hPhip.1 hPhip.2 hst hSA hApt
    have hAQf := SA.anc_tree_of_anc_U hac.localRun.coherent hPhip.1 hPhip.2 hApt hAQ hQt
    have hAE : ell.frame.Anc A (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
        (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
      unfold SA.getHead
      exact SA.anc_ghost (fun X hX => hX.1.1) _ hAt
    exact hframe.vote_head_eq_of_path_at hrun hnc hsvc hawake hf hcatch hnr hm hs₀ hz
      hdesignated hactual hPs hcp hcall hti hpay hpayload hparent hy hc hes hhigh hib hPv
      hSAf hAQf .refl hAE

end Consensus.Goldilocks.Healing.Growing

end
