module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowGeometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FullFrameWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.EarlyWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

/-! # Fresh-vote geometry over the shadow run and `Generic.FrameWindow`

The stock `FreshVotesGeometry` endpoints restated over `Growing.GoldilocksRun'` and the P-U window
`Generic.FrameWindow … M isTop J`: a P-U viable head transfers between readers of the window
(`WindowWitness`), and a frozen competitor reflects into the proposer's full viable tree. -/

public section

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
variable {hold : Time}

/-- A viable head transfers between warm frames whenever the receiving tree holds it.
(`FrameWindow.viableHead_transfer_at` over the shadow run and `Generic.FrameWindow`). -/
theorem viableHead_transfer_at {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y z : Fin sp.n} {i c : Nat}
    (hy : y ∈ H (tr.time i)) (hz : z ∈ H (tr.time c))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    {Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hv : Q ∈ (Node.frame (tr.state z c)).viableHeads)
    (hQ : Q ∈ (Node.frame (tr.state y i)).tree) :
    Q ∈ (Node.frame (tr.state y i)).viableHeads := by
  have hct := hrun.time_nonneg c
  have hbc : ∀ q < c, tr.time q ≤ tr.time c := fun q hq => hrun.time_mono hq.le
  rw [Node.frame_eq, Store.toFrame_viableHeads] at hv
  obtain ⟨hQz, -, hvz⟩ := hv
  have hwz := (tr.state z c).fg.viable_witness (hframe.M_eq z c hz hclo hchi)
    (hframe.top_iff z c hz hclo hchi) (hframe.root_eq z c hz hclo hchi) hvz
  have hW := Healing.windowWitness_of_frameWindow hrun hnc hframe hz hQz
    ⟨hwz.1, fun ht he => (hwz.2 ht he).mono (Compose.Growing.tree_held_at hct hz hbc)⟩
  rw [Node.frame_eq, Store.toFrame_tree] at hQ
  rw [Node.frame_eq, Store.toFrame_viableHeads]
  exact ⟨hQ.1, hQ.2, (hW.held y i hy hilo hihi hf hQ.1).2⟩

/-- `viableHead_transfer_at` between the frames of two calls inside the window. -/
theorem viableHead_transfer_call_at {lo hi : Time} {M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H lo hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {x w : Fin sp.n} {j q : Nat}
    {ellx ellw : ACLabel (goldilocksNode sp)} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time j)) (hw : w ∈ H (tr.time q))
    (hm : (H (tr.time j))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hjl : lo ≤ tr.time j) (hjh : tr.time j ≤ hi) (hql : lo ≤ tr.time q) (hqh : tr.time q ≤ hi)
    (hcx : tr.projAC.CallAt x j ellx) (hcw : tr.projAC.CallAt w q ellw)
    (hv : W ∈ ellw.frame.viableHeads) (hW : W ∈ ellx.frame.tree) :
    W ∈ ellx.frame.viableHeads := by
  rw [Compose.Growing.frame_of_projAC_at hrun hx hcx] at hW ⊢
  rw [Compose.Growing.frame_of_projAC_at hrun hw hcw] at hv
  exact viableHead_transfer_at hframe hrun hnc hx hw hm hjl hjh hql hqh hv hW

/-- A frozen competing child reflects into the actual proposer's full viable tree.
(`FrameWindow.frozen_competitor_reflect_at` over the shadow run and `Generic.FrameWindow`). -/
theorem frozen_competitor_reflect_at {g ΔF b : Time} {s₀ s M : Nat}
    {isTop : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (AC.gbar g))
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hm : AC.gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
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
  have rc := hrun.toCore
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
  have hvQ := Healing.Growing.proposal_parent_viable_full_frame_at hrun hnc hz'
    (sp.toParams.fg.faults_lt_quorum_margin (hf _ (rc.time_nonneg ip) (hti ▸ hpb))) hcp hcall
    (s := s + 1) (by rw [sp.slotTime_eq]; simpa only [ACParams.ts] using hti) hpay
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
      have hv' : W ∈ ellp.frame.viableHeads := viableHead_transfer_call_at hframe hrun hnc hz' hy
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

end Consensus.Goldilocks.Healing.Growing.Shadow

end
