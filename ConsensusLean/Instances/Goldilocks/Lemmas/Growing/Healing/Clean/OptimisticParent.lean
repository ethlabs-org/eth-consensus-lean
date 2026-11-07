module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Domain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Compatibility
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalDelivery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.LockWriter
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Healing.Proposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The clean optimistic source and the next proposal, under growing faults

The growing form of `Healing.ResetPremisesUpTo.clean_optimistic_proposal_parent`. The proposer is
honest at its call: its locks and frame are read on the prefix through the call. The source's
writer is honest at its write only. Its counted votes reach the proposer through the release
service owed at each release (`heldAtProposal_of_writer_at`), and the optimistic count is read
across the two cuts (`optimistic_first_proposal_anc_at`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A clean optimistic source, written at a cut of a node honest at it, extends the duty head of
the next honest proposal call, within the finite horizon. -/
theorem clean_optimistic_proposal_parent_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {x p : Fin sp.n} {r s i : Nat}
    (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) B d.head := by
  have hm := hp.run.time_mono
  have ht0 := hp.run.time_nonneg i
  have hS := healthy_base_of_reset_catch_before_at hp hc ht0 hib
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hU := hac.localRun.coherent
  have subU := RunTrace.honestBlocks_upTo_subset hm (H := H) ht0
  have hcp := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
  have hst : (tr.projAC.upTo (tr.time i)).state p i = tr.projAC.state p i :=
    Trace.upTo_state tr.projAC p fun _ hk => hm hk.le
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have := hp.faults _ ht0 hib
    have := Fin.pos p
    omega
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
  have hcut := hp.clean_window_timing_at hs s (by have := sp.two_le_k; clear * - this; omega)
  have hsg : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have hz := Healing.lt_cutZ sp g
    linarith only [hcut, hz, hΔ]
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt p k → tr.time k < sp.ts s := by
    intro k hki hk
    apply (hp.restart_le_before_at (hp.run.antitone (hm hki) hpH)
      (Compose.projAC_restartAt.mp hk) ((hm hki).trans hib)).trans_lt
    rw [Healing.cutZ_eq] at hcut
    have := (SA.ts_le_iff sp).mp hcut
    exact (SA.ts_lt_iff sp).mpr (by clear * - this; omega)
  obtain ⟨hPhi, hPhiV⟩ := SA.frameIn_of_callAt hr hpH hcp
  have hPhiU := hPhiV.trans subU
  rcases hp.clean_source_proposal_domain_before_at hc hx hpH (Or.inl ⟨CV, Or.inr hop⟩) hs
      (by clear * -; omega) hrb hR hci hcall hd hti hib with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, _, hstart, _⟩ := Compose.acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  -- the proposer's locks of a label `≥ s` are optimistic of label `s`, so compatible with `B`
  have hnoopt := Healing.proposal_no_optimistic_of_run (hp.run.upTo ht0) (hp.noColl.upTo _) hf
    hpH (by rw [RunTrace.upTo_projAC]; exact hcp) hcall hti
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocksAt H) (tr.projAC.state p i)
      (tr.time i) s B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hls X hX hXr => ?_
    rw [← hst] at hl
    obtain ⟨q, hqi, D, hw, L, hL, hLr, hLD⟩ := SA.lock_provenance hr hpH i l hl
    obtain rfl : L = X := hU.1 (subU hL) hX (hLr.trans hXr.symm)
    have hLD' := hLD.mono subU
    have hqt : tr.time q ≤ sp.ts (s + 1 : Nat) := hti ▸ hm hqi.le
    rcases hw with ⟨CV', hop'⟩ | ⟨ell', hupd⟩
    · have hle : l.slot ≤ s + 1 := by
        obtain ⟨ell', A, _, hsl, _⟩ := hop'
        change sp.slot (tr.time q) = l.slot at hsl
        have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) (l.slot : Int)).mpr
          (by clear * - hsl; omega)
        exact_mod_cast (SA.ts_le_iff sp).mp (this.trans hqt)
      have hne : l.slot ≠ s + 1 := fun he =>
        hnoopt p hpH q hqi D CV' (by rw [RunTrace.upTo_projAC]; exact he ▸ hop')
      have he : l.slot = s := by clear * - hls hle hne; omega
      rw [he] at hop'
      obtain ⟨-, hop''⟩ := (SA.upTo_optimisticLockAt hm).mp hop'
      rcases hp.optimistic_sources_compatible_at (hp.run.antitone (hm hqi.le) hpH) hx
          ((hm hqi.le).trans hib) hrb hop'' hop with h | h
      · exact Or.inl (hLD'.trans h)
      · exact SA.anc_total hU hLD' h
    · have ht : tr.time q = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hle := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ l.slot by clear * - hls; omega)
      rw [hts] at hqt
      exfalso
      linarith only [hqt, ht, hle, hΔ]
  refine SA.Growing.ProposalSources.optimistic_first_proposal_anc_at hac hf hx hop .refl hpH hci
    (SA.proposal_slot hti) hd ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  intro v hv
  obtain ⟨hvs, hsend, D, hD, hDr, hBD, hacc⟩ := fastLock_writer_at hac.localRun hx
    (Or.inr hop) v hv
  have hFD := hFB.trans hBD
  refine SA.Growing.heldAtProposal_of_writer_at hac.localRun
    (hp.sync.ac_service_at hp.run (SA.le_gbar g))
    (by linarith) (b := b) (by rw [hti, hts] at hib; linarith) hpH hci hti hrs hvs hsend
    ⟨D, hD, hDr, hFD, ?_⟩
  rcases hacc with hg | ⟨q, hqH, hq, hqt⟩
  · exact Or.inl hg
  by_cases hg : SA.gbar g ≤ tr.time q
  · exact Or.inr (Or.inl ⟨q, hqH, hq, hg, hqt⟩)
  -- an acceptance before the reset is relayed to the proposer by the catch-up
  have hprex := hp.run.upTo (hp.run.time_nonneg q)
  obtain ⟨ellq, hcq, hblock⟩ := hq
  have hcq' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hcq⟩
  obtain ⟨q', rfl, haq', htime⟩ := Compose.acBlock_prev hprex.toLocalRun hqH hcq' hblock
  obtain ⟨hqq, haq⟩ := (Trace.upTo_callAt tr).mp haq'
  change tr.time q' = tr.time (q' + 1) at htime
  have hex : ∃ k, SA.gbar g + 2 * sp.Δ ≤ tr.time k := ⟨i, by rw [hti, hts]; linarith⟩
  have hfirst : tr.FirstCutFrom (Nat.find hex) (SA.gbar g + 2 * sp.Δ) :=
    ⟨Nat.find_spec hex, fun k hk => not_le.mp (Nat.find_min hex hk)⟩
  have hki : Nat.find hex ≤ i := Nat.find_min' hex (by rw [hti, hts]; linarith)
  have hpy := hp.run.upTo ht0
  have hFD' : Anc (tr.HonestBlocksAt H) (tr.state p (Nat.find hex)).fg.F D := by
    have hF := Healing.run_F_mono hpy.toLocalRun hpH hki
    rw [RunTrace.upTo_state_of_le hm (hm hki), RunTrace.upTo_state_of_le hm le_rfl] at hF
    have hframe := Compose.frame_of_projAC hpy hpH (by rw [RunTrace.upTo_projAC]; exact hcp)
    rw [RunTrace.upTo_state_of_le hm le_rfl] at hframe
    have hFeq : ell.frame.F = (tr.state p i).fg.F := congrArg Frame.F hframe
    exact (hF.mono subU).trans (by rwa [← hFeq])
  obtain ⟨k, hkk, hak⟩ := hc x q' D (hp.run.antitone hqq hqH) haq
    (by rw [htime]; exact not_le.mp hg) p _
    (hp.run.antitone (hfirst.1.trans (hm hki)) hpH) hfirst hFD'
  have hk := hkk.le.trans hki
  have hak' := (RunTrace.upTo_acceptAt tr).mpr ⟨hm hk, hak⟩
  obtain ⟨ellk, hck, hblock, ht⟩ := Compose.accept_next hpy.toLocalRun hpH hak'
  have hck' := (Trace.upTo_callAt tr).mp hck |>.2
  refine Or.inr (Or.inr ⟨k + 1, by omega, ⟨ellk, Compose.projAC_callAt.mpr hck', hblock⟩, ?_⟩)
  change tr.time (k + 1) < _
  change tr.time (k + 1) = tr.time k at ht
  rw [ht]
  have := hfirst.2 k hkk
  linarith

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
