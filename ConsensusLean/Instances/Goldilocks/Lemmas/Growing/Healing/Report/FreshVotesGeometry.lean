module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowGeometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Viable heads across independently honest warm observations -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A viable head transfers between warm frames whenever the receiving tree holds it. -/
theorem FrameWindow.viableHead_transfer_at {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i c : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hv : Q ∈ (Node.frame (tr.state z c)).viableHeads)
    (hQ : Q ∈ (Node.frame (tr.state y i)).tree) :
    Q ∈ (Node.frame (tr.state y i)).viableHeads := by
  apply (floor_ancestor_mem_frame_at hrun hnc hy hz hf hv.1 _ _ hQ.1
    (Relation.ReflTransGen.refl)).2.2
  · rw [hframe.floor_eq y i hy hilo hihi, ← hframe.floor_eq z c hz hclo hchi]
    exact hv.2.2.2
  · intro hm hc
    have hk := (hframe.kind_iff y i hy hilo hihi).mp ⟨hm, hc⟩
    have hzk := (hframe.kind_iff z c hz hclo hchi).mpr hk
    have hroot : (tr.state z c).fg.fcRoot = (tr.state z c).fg.J := ite_eq_left hzk
    rw [hframe.root_eq y i hy hilo hihi hk,
      ← hframe.root_eq z c hz hclo hchi hk, ← hroot]
    exact hv.2.2.1.mono (fun B hB =>
      ⟨z, c, tr.time c, hrun.time_nonneg c, (fun q hq => hrun.time_mono hq.le), hz, hB⟩)

/-- A frozen competing child reflects into the actual proposer's full viable tree. -/
theorem FrameWindow.frozen_competitor_reflect_at {g ΔF b : Time} {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (SA.gbar g))
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hm : SA.gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hpb : sp.ts (s + 1 : Nat) ≤ b)
    {X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ ellp.frame.tree) (hrootX : ellp.frame.Anc ellp.frame.fcRoot X)
    (hBX : B.parent = some X.root) (hne : B ≠ P)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hri := (hac.upTo (hr.time_nonneg i)).localRun
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hPhi := SA.frameIn_of_callAt hri hy hci
  have hz' : z ∈ H (tr.time ip) := hr.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hrp := (hac.upTo (hr.time_nonneg ip)).localRun
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := SA.frameIn_of_callAt hrp hz' hcp'
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      have hs := (SA.castAt_spec hri hy ⟨hci, hc.2⟩).2.1.symm.trans hes
      change sp.slot (tr.time i) = s + 1 at hs
      rw [hs])
  have hipl : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have hil : sp.ts s₀ ≤ tr.time i := hipl.trans (hti ▸ hlo)
  have hiph : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hti]; linarith only [sp.toParams.hΔ]
  have hvQ := proposal_parent_viable_full_frame_at hrun hnc hz'
    (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hr.time_nonneg ip) (hti ▸ hpb))) hcp hcall
    (s := s + 1) (by rw [sp.slotTime_eq]; simpa only [SAParams.ts] using hti) hpay
  have hQt := hPhip.1.viableHeads_subset hvQ
  obtain ⟨⟨hBt, _⟩, _, W, hWV, hvW, hBW⟩ := hB
  have hFB : Anc (tr.HonestBlocksAt H) ellp.frame.F B :=
    ((hPhip.1.rooted.2 X hX).mono hPhip.2).trans
      (.single ⟨hPhip.2 hX, hPhi.2 hBt, hBX⟩)
  obtain ⟨W', hW't, hW'v, hBW'⟩ : ∃ W' ∈ ellp.frame.tree,
      W' ∈ ellp.frame.viableHeads ∧ Anc (tr.HonestBlocksAt H) B W' := by
    rcases hWV.2 with hstamp | ⟨P', hP', hP's, hWP'⟩
    · have hFW := hFB.trans (hBW.mono hPhi.2)
      have hWp : W ∈ ellp.frame.tree := by
        have hread := SA.readPoint_blockStamp_eq hri hy ⟨hci, hc.2⟩
        rw [hread] at hstamp
        rcases Healing.stamp_origin hri hy i ell hci W hWV.1 with hg | ⟨q, hqi, ellq, hcq, hWq, hsq⟩
        · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hrp hz' ip ellp hcp'
          obtain rfl : W = G := hac.localRun.coherent.1 (hPhi.2 hWV.1) hGU (hg.trans hGr.symm)
          rcases Relation.ReflTransGen.cases_tail hFW with he | ⟨C, _, hp⟩
          · exact he ▸ hPhip.1.rooted.1
          · exact (Option.some_ne_none _ (hp.2.2.symm.trans hGp)).elim
        have hqt : tr.time q < sp.ts s + 3 * sp.Δ := by
          rw [hsq] at hstamp
          have ht := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hstamp)
          change tr.time q < SA.freeze sp (s + 1) at ht
          simpa only [SA.freeze, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] using ht
        exact frame_relay_before_at hrun hnc hsvc hcatch hnr
          (hr.antitone (hr.time_mono hqi) hy) hz' ((Trace.upTo_callAt _).mp hcq).2 hcp hWq
          (by rw [hti, hts]; linarith only [hm, sp.toParams.hΔ])
          (by rw [hti, hts]; linarith only [hqt]) hFW
      have hvW' : W ∈ (Node.frame (tr.state y i)).viableHeads := by
        rw [← (hrun.cutLaw y i _ (Compose.projAC_callAt.mp hc.1) hy).1]
        exact hvW
      have hWp' : W ∈ (Node.frame (tr.state z ip)).tree := by
        rw [← (hrun.cutLaw z ip _ (Compose.projAC_callAt.mp hcp) hz').1]
        exact hWp
      have hv := hframe.viableHead_transfer_at hrun hnc hz' hy
        (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hr.time_nonneg ip) (hti ▸ hpb)))
        hipl hiph hil hhigh hvW' hWp'
      have hv' : W ∈ ellp.frame.viableHeads := by
        rw [← (hrun.cutLaw z ip _ (Compose.projAC_callAt.mp hcp) hz').1] at hv
        exact hv
      exact ⟨W, hWp, hv', hBW.mono hPhi.2⟩
    · obtain rfl := proposal_frame_unique_at hrun hnc hz hdesignated hactual hPs
        (by omega) hy hc.1 hhigh hP' hP's
      rcases Relation.ReflTransGen.cases_tail (hBW.trans hWP') with he | ⟨Y, hBY, hYP⟩
      · exact (hne he.symm).elim
      · obtain rfl : Y = d.head := hac.localRun.coherent.1 (hPhi.2 hYP.1) (hPhip.2 hQt)
          (Option.some.inj (hYP.2.2.symm.trans hparent))
        exact ⟨d.head, hQt, hvQ, Anc.mono hPhi.2 hBY⟩
  have hBp := SA.frame_mem_of_between sp hac.localRun.coherent hPhip.1 hPhip.2 hW't hBW' hFB
  exact ⟨hBp, hrootX.tail ⟨hX, hBp, hBX⟩, W', hW't, hW'v,
    SA.anc_tree_of_anc_U hac.localRun.coherent hPhip.1 hPhip.2 hBp hBW' hW't⟩

end Consensus.Goldilocks.Healing.Growing

end
