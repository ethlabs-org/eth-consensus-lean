module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Viable heads across independently honest warm observations -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
variable {hold : Time}

/-- A frozen competing child reflects into the actual proposer's full viable tree, over any run
core, from a viable-head transfer across the window (`hT`) and the proposer's parent viability
(`hPV`). -/
theorem Core.frozen_competitor_reflect_at {g ΔF b : Time} {s₀ s : Nat}
    {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (AC.gbar g))
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hm : AC.gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    (hT : ∀ {x w : Fin sp.n} {j q : Nat} {ellx ellw : ACLabel (goldilocksNode sp)}
      {W : AC.Blk sp.n (List (FG.Att sp.n))}, x ∈ H (tr.time j) → w ∈ H (tr.time q) →
      (H (tr.time j))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n →
      sp.ts s₀ ≤ tr.time j → tr.time j ≤ sp.ts (s + 1 : Nat) + sp.Δ →
      sp.ts s₀ ≤ tr.time q → tr.time q ≤ sp.ts (s + 1 : Nat) + sp.Δ →
      tr.projAC.CallAt x j ellx → tr.projAC.CallAt w q ellw →
      W ∈ ellw.frame.viableHeads → W ∈ ellx.frame.tree → W ∈ ellx.frame.viableHeads)
    (hPV : ∀ {x : Fin sp.n} {j σ : Nat} {ell : ACLabel (goldilocksNode sp)}
      {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n},
      x ∈ H (tr.time j) → (H (tr.time j))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n →
      tr.projAC.CallAt x j ell → ell.call = .proposal → tr.time j = sp.toParams.slotTime σ →
      (AC.acProposal sp (tr.projAC.state x j) ell.frame (tr.time j)).2 = some (d, pay) →
      d.head ∈ ell.frame.viableHeads)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hpb : sp.ts (s + 1 : Nat) ≤ b)
    {X B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ ellp.frame.tree) (hrootX : ellp.frame.Anc ellp.frame.fcRoot X)
    (hBX : B.parent = some X.root) (hne : B ≠ P)
    (hB : B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hac := rc.acRun hnc
  have hri := (hac.upTo (rc.time_nonneg i)).localRun
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hPhi := AC.frameIn_of_callAt hri hy hci
  have hz' : z ∈ H (tr.time ip) := rc.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hrp := (hac.upTo (rc.time_nonneg ip)).localRun
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := AC.frameIn_of_callAt hrp hz' hcp'
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := AC.ts_succ s
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (rc.time_nonneg i) _).2 (by
      have hs := (AC.castAt_specU hri.toU hy ⟨hci, hc.2⟩).2.1.symm.trans hes
      change sp.slot (tr.time i) = s + 1 at hs
      rw [hs])
  have hipl : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (AC.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have hil : sp.ts s₀ ≤ tr.time i := hipl.trans (hti ▸ hlo)
  have hiph : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hti]; linarith only [sp.toParams.hΔ]
  have hvQ := hPV hz'
    (sp.toParams.fg.faults_lt_quorum_margin (hf _ (rc.time_nonneg ip) (hti ▸ hpb))) hcp hcall
    (σ := s + 1) (by rw [sp.slotTime_eq]; simpa only [ACParams.ts] using hti) hpay
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
        have hread := AC.readPoint_blockStamp_eqU hri.toU hy ⟨hci, hc.2⟩
        rw [hread] at hstamp
        rcases Healing.stamp_origin hri hy i ell hci W hWV.1 with hg | ⟨q, hqi, ellq, hcq, hWq, hsq⟩
        · obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hrp.toU hz' ip ellp hcp'
          obtain rfl : W = G := hac.localRun.coherent.1 (hPhi.2 hWV.1) hGU (hg.trans hGr.symm)
          rcases Relation.ReflTransGen.cases_tail hFW with he | ⟨C, _, hp⟩
          · exact he ▸ hPhip.1.rooted.1
          · exact (Option.some_ne_none _ (hp.2.2.symm.trans hGp)).elim
        have hqt : tr.time q < sp.ts s + 3 * sp.Δ := by
          rw [hsq] at hstamp
          have ht := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hstamp)
          change tr.time q < AC.freeze sp (s + 1) at ht
          simpa only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] using ht
        exact Core.frame_relay_before_at rc hnc hsvc hcatch
          (rc.antitone (rc.time_mono hqi) hy) hz'
          (fun r hr' hrs => hnr _ r (rc.antitone (rc.time_mono hr') hz') hrs)
          ((Trace.upTo_callAt _).mp hcq).2 hcp hWq
          (by rw [hti, hts]; linarith only [hm, sp.toParams.hΔ])
          (by rw [hti, hts]; linarith only [hqt]) hFW
      have hv' : W ∈ ellp.frame.viableHeads := hT hz' hy
        (sp.toParams.fg.faults_lt_quorum_margin (hf _ (rc.time_nonneg ip) (hti ▸ hpb)))
        hipl hiph hil hhigh hcp hc.1 hvW hWp
      exact ⟨W, hWp, hv', hBW.mono hPhi.2⟩
    · obtain rfl := Core.proposal_frame_unique_at rc hnc hz hdesignated hactual hPs
        (by omega) hy hc.1 hhigh hP' hP's
      rcases Relation.ReflTransGen.cases_tail (hBW.trans hWP') with he | ⟨Y, hBY, hYP⟩
      · exact (hne he.symm).elim
      · obtain rfl : Y = d.head := hac.localRun.coherent.1 (hPhi.2 hYP.1) (hPhip.2 hQt)
          (Option.some.inj (hYP.2.2.symm.trans hparent))
        exact ⟨d.head, hQt, hvQ, Anc.mono hPhi.2 hBY⟩
  have hBp := AC.frame_mem_of_between sp hac.localRun.coherent hPhip.1 hPhip.2 hW't hBW' hFB
  exact ⟨hBp, hrootX.tail ⟨hX, hBp, hBX⟩, W', hW't, hW'v,
    AC.anc_tree_of_anc_U hac.localRun.coherent hPhip.1 hPhip.2 hBp hBW' hW't⟩

end Consensus.Goldilocks.Healing.Growing

end
