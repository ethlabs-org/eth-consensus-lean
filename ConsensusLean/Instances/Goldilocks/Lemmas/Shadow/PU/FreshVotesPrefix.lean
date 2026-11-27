module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FreshVotesFinality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ProposalLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ProposalStart
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The warm proposal start is a prefix of every primed vote head -/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {hold : Time}

/-- Primed finality and the actual proposal's live lock put its start below the cast head. -/
theorem proposal_start_prefix_at {s₀ s M : Nat}
    {isTop : Prop} {J P : AC.Blk sp.n (List (FG.Att sp.n))} {g ΔF b : Time}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hk : 0 < sp.k)
    (hmargin : s₀ + 2 * sp.k ≤ s + 1)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdes : z = proposer (s + 1)) {ip : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hPv : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (hvP : P ∈ ell.frame.viableHeads)
    (haS : ell.frame.Anc (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) d.start)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ell.frame.Anc d.start (AC.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (AC.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hri := (hac.upTo (hrun.time_nonneg i)).localRun
  have hcast : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  have hPhi := AC.frameIn_of_callAt hri hy hci
  have hz' : z ∈ H (tr.time ip) :=
    hrun.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := AC.frameIn_of_callAt (hac.upTo (hrun.time_nonneg ip)).localRun hz' hcp'
  obtain ⟨hst, _, hw⟩ := Core.proposal_walk_end_at hrun.toCore hnc hz' hcp hpay
  have hSQ := hw.anc (fun X hX => hX.1) hst
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hSQ he).2
  have hSP : Anc (tr.HonestBlocksAt H) d.start P :=
    (Anc.mono hPhip.2 hSQ).tail ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  have hPv' := hPv
  rw [← hes] at hPv'
  have hSv := Core.frozen_viable_of_anchor_path_at hrun.toCore hnc hy hc hPv'
    (Anc.mono hPhi.2 haS) hSP
  rw [hes] at hSv
  have hslot := (AC.castAt_specU hri.toU hy hcast).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have hlo : sp.ts s₀ ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hslot]; omega)
  have hhi := AC.vote_time_leU hri.toU hy ⟨ell, hcast⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
  rw [hslot] at hhi
  have hplo : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (AC.ts_le_iff sp).2 (by omega)
  have hphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hti]; linarith [sp.toParams.hΔ]
  have hfmax : (H (max (tr.time ip) (tr.time i)))ᶜ.ncard <
      2 * sp.toParams.fg.q - sp.n :=
    sp.toParams.fg.faults_lt_quorum_margin (hf _
      (le_max_of_le_left (hrun.time_nonneg ip)) ((max_le hphi hhi).trans hmb))
  have hroot (hSr : Anc (tr.HonestBlocksAt H) d.start ellp.frame.fcRoot) := by
    have hrootE := fcRoot_anc_head_at_cast_at hframe hrun hnc hz' hy hfmax
      hplo hphi hlo hhi hcp hc (hes ▸ hPv.1) hvP ((Anc.mono hPhi.2 haS).trans hSr)
    have hSE := hSr.trans hrootE
    rw [hes, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hSE
    exact AC.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hSv.1.1 hSE
      (AC.getHead_mem hPhi.1 (fun X hX => hX.1.1) _ _ _ _)
  rcases Core.actual_proposal_start_live_origin_at hrun.toCore hnc
    (fun ht => Healing.actual_proposal_start_live_origin (hrun.upTo ht) (hnc.upTo _))
    (by
      have ht : sp.ts s₀ ≤ sp.ts (s + 1 : Nat) := (AC.ts_le_iff sp).2 (by omega)
      linarith [sp.toParams.hΔ]) (hphi.trans hmb) (by omega)
    (by omega : s₀ + sp.k ≤ s + 1) (hdes ▸ hz')
    (hdes ▸ hcp) hcall hti (hdes ▸ hpay) hK with he | ⟨l, hl, _, hold, B, hB, hBr, hSB⟩
  · exact hroot (he ▸ .refl)
  have hlive : s + 1 ≤ l.slot + sp.k := by
    have hs := Trace.upTo_state tr.projAC (proposer (s + 1)) (d := tr.time ip) (i := ip)
      (fun q hq => hrun.time_mono hq.le)
    have hl' : l ∈ AC.liveLocks sp
        ((tr.projAC.upTo (tr.time ip)).state (proposer (s + 1)) ip).locks
        ellp.frame (tr.time ip) := by rw [hs]; exact hl
    have hcap :=
      (AC.locksWF_state (hac.upTo (hrun.time_nonneg ip)).localRun hrun.vstart
      (hdes ▸ hz') ip).slot_le_of_live hl'
    have hsl : sp.slot (tr.time ip) = s + 1 := AC.proposal_slot (tr := tr.projAC) hti
    rw [hsl] at hcap
    exact hcap
  rcases KernelProof.proposal_lock_prefix_cases_window_at hframe hrun hnc hsvc hawake hf hcatch
    hnr hm hmb hz' hcp hti (hdes.symm ▸ hl) (by omega) (by omega) (by omega) hold hB hBr hSB
    hK with hbelow | hheads | ⟨a, _, D, CV, hza, hop, hSD⟩
  · exact hroot hbelow
  · exact Core.honest_prefix_of_finality_before_at hrun.toCore hnc hsvc hawake hf hcatch hnr
      (by
        have ht : sp.ts s₀ ≤ sp.ts s := (AC.ts_le_iff sp).2 (by omega)
        linarith) hmb hheads hy hc hes hSv haS hK
  · have hFD : Anc (tr.HonestBlocksAt H) ell.frame.F D :=
      (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans hSv.2.1)).trans hSD
    exact KernelProof.Core.optimistic_prefix_before_at hrun.toCore hnc hsvc hawake hcatch
      (by
        have ht : sp.ts s₀ ≤ sp.ts s := (AC.ts_le_iff sp).2 (by omega)
        linarith [sp.toParams.hΔ]) hza hy hop hSD hc hes (hhi.trans hmb) hFD hSv haS hK

end Consensus.Goldilocks.Healing.Growing.Shadow

end
