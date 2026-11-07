module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesFinality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRegularBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.OptimisticService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ProposalLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.CarryPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Prior honest votes force a cast's prefix on its read horizon -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Proposal-start provenance is local to the proposer's own honest call. -/
theorem actual_proposal_start_live_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {s₀ p i : Nat}
    (hf : 3 * (H (tr.time i))ᶜ.ncard ≤ sp.n - 1)
    (hp : 1 ≤ p) (hmargin : s₀ + sp.k ≤ p)
    {ell : ACLabel (goldilocksNode sp ro)} (hz : proposer p ∈ H (tr.time i))
    (hc : tr.projAC.CallAt (proposer p) i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts p)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (SA.acProposal sp (tr.projAC.state (proposer p) i) ell.frame (tr.time i)).2 =
      some (d, pay)) :
    d.start = ell.frame.fcRoot ∨
      ∃ l ∈ SA.liveLocks sp (tr.projAC.state (proposer p) i).locks ell.frame (tr.time i),
        s₀ ≤ l.slot ∧ l.slot < p ∧ ∃ B ∈ ell.frame.tree,
          B.root = l.block ∧ ell.frame.Anc d.start B := by
  have hs := Trace.upTo_state tr.projAC (proposer p) (d := tr.time i) (i := i)
    (fun q hq => hrun.time_mono hq.le)
  have hc' : (tr.upTo (tr.time i)).projAC.CallAt (proposer p) i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hpay' : (SA.acProposal sp ((tr.upTo (tr.time i)).projAC.state (proposer p) i)
      ell.frame (tr.time i)).2 = some (d, pay) := by
    simpa only [RunTrace.upTo_projAC, hs] using hpay
  have h := Healing.actual_proposal_start_live_origin (hrun.upTo (hrun.time_nonneg i))
    (hnc.upTo _) hf hp hmargin hz hc' hcall hti hpay'
  simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using h

/-- Prior-slot heads from validators honest at their own casts force the receiving walk.
Only the healthy AC base on the receiver's read prefix is used. -/
theorem honest_prefix_of_finality_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hheads : ∀ x j ev, x ∈ H (tr.time j) → SA.VoteAt tr.projAC x j ev →
      ev.msg.slot = s → SA.VoteExtends (tr.HonestBlocksAt H) ev.msg B)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (haB : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) B) :
    ell.frame.Anc B (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg i
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hri := (hac.upTo hd).localRun
  have hcast : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  have hslot := (SA.castAt_spec hri hy hcast).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have ht := SA.vote_time_le hri hy ⟨ell, hcast⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
  rw [hslot] at ht
  have hstart : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp hd _).2 (by rw [hslot])
  have hstep : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch hd
    (ht.trans hmb)
  have hPhi := SA.frameIn_of_callAt hS.run.localRun hy hci
  have hheads' : ∀ x ∈ H (tr.time i), ∀ j ev,
      SA.VoteAt (tr.projAC.upTo (tr.time i)) x j ev → ev.msg.slot = s →
      SA.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) ev.msg B := by
    intro x hx j ev hv hs
    obtain ⟨ellx, hcx, hex⟩ := hv
    obtain ⟨hjd, hcx'⟩ := (Trace.upTo_callAt _).mp hcx
    obtain ⟨R, hR, hRr, _⟩ := SA.honest_head hS.run hx ⟨ellx, hcx, hex⟩
    obtain ⟨R', hR', hR'r, hBR⟩ := hheads x j ev (hr.antitone hjd hx) ⟨ellx, hcx', hex⟩ hs
    have he : R' = R := hac.localRun.coherent.1 hR'
      (RunTrace.honestBlocks_upTo_subset hr.time_mono hd hR) (hR'r.trans hRr.symm)
    exact ⟨R, hR, hRr, RunTrace.anc_upTo_of_right hr hnc hd hR (he ▸ hBR)⟩
  have hnr' : Healing.NoRestartAfter (tr.upTo (tr.time i)) (H (tr.time i)) (gbar g) := by
    intro x hx q hq
    obtain ⟨hqd, hq⟩ := (RunTrace.upTo_restartAt _).mp hq
    exact hnr x q (hr.antitone hqd hx) hq
  have hrestarts : ∀ x ∈ H (tr.time i), ∀ q,
      ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) x q → tr.time q ≤ gbar g := by
    intro x hx q hq
    rw [← RunTrace.upTo_projAC] at hq
    exact hnr' x hx q (Compose.projAC_restartAt.mp hq)
  have hcarry := SA.honest_batch_carry_before hS hy hcast hes hm
    (by change sp.ts s + 2 * sp.Δ ≤ tr.time i
        rw [hstep] at hstart; linarith [sp.toParams.hΔ]) le_rfl
    (fun k hk t ht => by
      rw [← RunTrace.upTo_projAC]
      apply Compose.ac_deadline_le_of_restarts (a := sp.ts s)
      intro r _ hrs
      have := hnr' y hy r (Compose.projAC_restartAt.mp hrs)
      change tr.time r ≤ gbar g at this
      change tr.time r ≤ _
      linarith [sp.toParams.hΔ])
    (fun k hk hrs => by
      have := hrestarts y hy k hrs
      change tr.time k < _
      linarith [sp.toParams.hΔ])
    (fun x hx j ev hv hs R hR hRr => by
      obtain ⟨R', hR', hR'r, hBR⟩ := hheads' x hx j ev hv hs
      have he : R' = R := hS.run.localRun.coherent.1 hR' hR (hR'r.trans hRr.symm)
      exact (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans hB.2.1)).trans (he ▸ hBR))
  have hex := SA.honest_votes_in_slot_before hS hm
    (by rw [hstep] at hstart; linarith [sp.toParams.hΔ])
    (fun x hx r ht hrs => by
      have := hrestarts x hx r hrs
      rw [SA.ts_sub_one]
      change tr.time r ≤ _
      linarith)
  have hf' : 3 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have hbound := hf _ hd (ht.trans hmb)
    have hn := sp.toParams.hn
    clear * - hbound hn
    change 0 < sp.n at hn
    omega
  rw [← SA.viableTree_voteDomain_eq_of_viable ⟨B, hB⟩]
  exact SA.honest_prefix_of_carry sp hS.run hf' hy hcast hes hheads'
    (fun x hx => by obtain ⟨j, ev, hv, hs, _⟩ := hex x hx; exact ⟨j, ev, hv, hs⟩)
    hcarry (SA.viableTree_voterBlockTree_subset_voteDomain hB) haB

/-- The actual warm proposal's start is reached by every shallower honest cast. -/
theorem FrameWindow.proposal_start_prefix_at {s₀ s floor : Nat}
    {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))} {g ΔF b : Time}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
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
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 = some (d, pay))
    (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (hvP : P ∈ ell.frame.viableHeads)
    (haS : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) d.start) :
    ell.frame.Anc d.start (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s) := by
  have hr := hrun.toLocalRun
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hri := (hac.upTo (hr.time_nonneg i)).localRun
  have hcast : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  have hPhi := SA.frameIn_of_callAt hri hy hci
  have hz' : z ∈ H (tr.time ip) := hr.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hcp⟩
  have hPhip := SA.frameIn_of_callAt (hac.upTo (hr.time_nonneg ip)).localRun hz' hcp'
  obtain ⟨hst, _, hw⟩ := proposal_walk_end_at hrun hnc hz' hcp hpay
  have hSQ := hw.anc (fun X hX => hX.1) hst
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hSQ he).2
  have hSP : Anc (tr.HonestBlocksAt H) d.start P :=
    (Anc.mono hPhip.2 hSQ).tail ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  have hPv' := hPv
  rw [← hes] at hPv'
  have hSv := frozen_viable_of_anchor_path_at hrun hnc hy hc hPv'
    (Anc.mono hPhi.2 haS) hSP
  rw [hes] at hSv
  have hslot := (SA.castAt_spec hri hy hcast).2.1.symm.trans hes
  change sp.slot (tr.time i) = s + 1 at hslot
  have hlo : sp.ts s₀ ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
      rw [hslot]; omega)
  have hhi := SA.vote_time_le hri hy ⟨ell, hcast⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
  rw [hslot] at hhi
  have hplo : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (SA.ts_le_iff sp).2 (by omega)
  have hphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by rw [hti]; linarith [sp.toParams.hΔ]
  have hfmax : (H (max (tr.time ip) (tr.time i)))ᶜ.ncard <
      2 * sp.toParams.fg.q - sp.n :=
    sp.toParams.fg.faults_lt_quorum_margin (hf _
      (le_max_of_le_left (hr.time_nonneg ip)) ((max_le hphi hhi).trans hmb))
  have hroot (hSr : Anc (tr.HonestBlocksAt H) d.start ellp.frame.fcRoot) := by
    have hrootE := hframe.fcRoot_anc_head_at_cast_at hrun hnc hz' hy hfmax hplo hphi hlo hhi
      hcp hc (hes ▸ hPv.1) hvP ((Anc.mono hPhi.2 haS).trans hSr)
    have hSE := hSr.trans hrootE
    rw [hes, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] at hSE
    exact SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hSv.1.1 hSE
      (SA.getHead_mem hPhi.1 (fun X hX => hX.1.1) _ _ _ _)
  rcases actual_proposal_start_live_origin_at hrun hnc
    (hf _ (hr.time_nonneg ip) (hphi.trans hmb)) (by omega)
    (by omega : s₀ + sp.k ≤ s + 1) (hdes ▸ hz')
    (hdes ▸ hcp) hcall hti (hdes ▸ hpay) with he | ⟨l, hl, _, hold, B, hB, hBr, hSB⟩
  · exact hroot (he ▸ .refl)
  have hlive : s + 1 ≤ l.slot + sp.k := by
    have hs := Trace.upTo_state tr.projAC (proposer (s + 1)) (d := tr.time ip) (i := ip)
      (fun q hq => hr.time_mono hq.le)
    have hl' : l ∈ SA.liveLocks sp
        ((tr.projAC.upTo (tr.time ip)).state (proposer (s + 1)) ip).locks
        ellp.frame (tr.time ip) := by rw [hs]; exact hl
    have hcap := (SA.locksWF_state (hac.upTo (hr.time_nonneg ip)).localRun
      (hdes ▸ hz') ip).slot_le_of_live hl'
    have hsl : sp.slot (tr.time ip) = s + 1 := SA.proposal_slot (tr := tr.projAC) hti
    rw [hsl] at hcap
    exact hcap
  rcases KernelProof.proposal_lock_prefix_cases_at hframe hrun hnc hsvc hawake hf hcatch hnr
    hm hmb hz' hcp hti (hdes.symm ▸ hl) (by omega) (by omega) (by omega) hold hB hBr hSB with
    hbelow | hheads | ⟨a, _, D, CV, hza, hop, hSD⟩
  · exact hroot hbelow
  · exact honest_prefix_of_finality_before_at hrun hnc hsvc hawake hf hcatch hnr
      (by
        have ht : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by omega)
        linarith) hmb hheads hy hc hes hSv haS
  · have hFD : Anc (tr.HonestBlocksAt H) ell.frame.F D :=
      (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans hSv.2.1)).trans hSD
    exact KernelProof.optimistic_prefix_before_at hrun hnc hsvc hawake hf hcatch
      (by
        have ht : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by omega)
        linarith [sp.toParams.hΔ]) hza hy hop hSD hc hes (hhi.trans hmb) hFD hSv haS

end Consensus.Goldilocks.Healing.Growing

end
