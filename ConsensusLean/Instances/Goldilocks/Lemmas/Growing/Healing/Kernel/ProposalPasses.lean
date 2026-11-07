module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalDelivery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.LockWriter
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposals after the growing reset

Batch votes use the proposal reader's finite prefix. The adjacent optimistic
origin uses historical release service, not survival of its original writer.
The source and retention induction contracts remain explicit dependencies.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- Every earlier high origin is below the bounded post-drain proposal head. -/
theorem ResetPremisesUpTo.reset_proposal_passes_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ∀ O, (∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u) →
      Anc (tr.HonestBlocksAt H) O d.head := by
  rintro O ⟨x, r, l, ho, hrt⟩
  have hm := hp.run.time_mono
  have ht0 := hp.run.time_nonneg i
  have hS := healthy_base_of_reset_catch_before_at hp hc ht0 hib
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hU := hac.localRun.coherent
  have subU := RunTrace.honestBlocks_upTo_subset hm (H := H) ht0
  have narrow : ∀ {A B : SA.Blk sp.n (List (FG.Att sp.n))},
      B ∈ (tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)) →
      Anc (tr.HonestBlocksAt H) A B →
      Anc ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) A B :=
    fun hB hAB => RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl ht0 hB hAB
  have hcp := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
  have hs : (tr.projAC.upTo (tr.time i)).state p i = tr.projAC.state p i :=
    Trace.upTo_state tr.projAC p fun _ hk => hm hk.le
  have hdp : (SA.acProposal sp ((tr.projAC.upTo (tr.time i)).state p i)
      ell.frame ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by
    rw [hs]
    exact hd
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have := hp.faults _ ht0 hib
    have := Fin.pos p
    omega
  have hri : r < i := by
    by_contra hn
    have ht := hm (Nat.le_of_not_gt hn)
    rw [hti] at ht
    exact (not_lt_of_ge ht) hrt
  have hrb := (hm hri.le).trans hib
  have hlu := hp.origin_label_lt_at_proposal_at hpH hci hcall hti hib hri ho
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hsucc : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]
    push_cast
    ring
  obtain ⟨hPhi, hPhiV⟩ := SA.frameIn_of_callAt hr hpH hcp
  have hPhiU := hPhiV.trans subU
  have below : Anc (tr.HonestBlocksAt H) O ell.frame.fcRoot →
      Anc (tr.HonestBlocksAt H) O d.head := by
    intro hOF
    obtain ⟨_, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A, _, hstart, _⟩ := Compose.acProposal_walk hd
    rw [hstart] at hsQ
    exact hOF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A (tr.time i)).trans hsQ))
  rcases hp.proposal_holds_old_at hpH hci hcall hd hti hib ho hrt with hOt | hOF
  swap
  · obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
    exact hOF.trans (Anc.mono hPhiU ((hPhi.rooted.2 _ hstart).trans hsQ))
  rcases hp.held_high_origin_viable_at hpH hci hib ho hrb
      (by rw [hti]; exact (SA.ts_le_iff sp).mpr (by omega)) hOt with hV | hOF
  swap
  · exact below (hOF.mono hPhiU)
  have hFO := (hPhi.rooted.2 O hOt).mono hPhiU
  have hhigh := hp.proposal_stored_locks_compatible_old_at hc hpH hR hci hcall hti hib ho hrb
  have hhigh' : SA.HighLocksCompatible (tr.HonestBlocksAt H) (tr.projAC.state p i)
      (tr.time i) s O := by simpa only [Nat.add_sub_cancel] using hhigh
  have hcut : cutZ sp.toParams g ≤ sp.ts s :=
    (hp.cutZ_le_ts_of_highOrigin_at ho hrb).trans ((SA.ts_le_iff sp).mpr (by omega))
  have hsg : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := lt_cutZ sp g
    linarith
  have hsb : sp.ts s + sp.Δ ≤ tr.time i := by rw [hti, hsucc]; linarith
  have hrestart : ∀ z ∈ H (tr.time i), ∀ q, tr.time q ≤ tr.time i →
      tr.projAC.RestartAt z q → tr.time q ≤ sp.ts ((s : Int) - 1) := by
    intro z hz q hqi hrest
    apply (restart_le_before_at hp (hp.run.antitone hqi hz)
      (Compose.projAC_restartAt.mp hrest) (hqi.trans hib)).trans
    rw [cutZ_eq] at hcut
    have := (SA.ts_le_iff sp).mp hcut
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hrs : ∀ q ≤ i, tr.projAC.RestartAt p q → tr.time q < sp.ts s := by
    intro q hqi hrest
    exact (hrestart p hpH q (hm hqi) hrest).trans_lt
      ((SA.ts_lt_iff sp).mpr (by omega))
  have hrsp : ∀ q ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) p q →
      (tr.projAC.upTo (tr.time i)).time q < sp.ts s := by
    intro q hqi hrest
    exact hrs q hqi (ACTrace.upTo_restartAt.mp hrest).2
  by_cases hls : l < s
  · have votes : ∀ z ∈ H (tr.time i), ∀ q e,
        SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e → e.msg.slot = s →
        SA.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) e.msg O := by
      rintro z hz q e hv hes
      obtain ⟨hqi, ellq, hcq, heq⟩ := SA.upTo_voteAt.mp hv
      obtain ⟨R, hRV, hRroot, _⟩ := SA.honest_head hS.run hz hv
      obtain ⟨R', hR'U, hR'root, hOR'⟩ := hp.high_origin_votes_before_at q (hqi.trans hib)
        x r l O ho hrb z ellq e (hp.run.antitone hqi hz) ⟨hcq, heq⟩ (by omega)
      have hRR : R' = R := hU.1 hR'U (subU hRV) (hR'root.trans hRroot.symm)
      rw [hRR] at hOR'
      exact ⟨R, hRV, hRroot, narrow hRV hOR'⟩
    have hhalf := SA.honest_voters_half_before hS hsg hsb
      (fun z hz q hqt hrest => hrestart z hz q (hqt.trans hsb)
        (ACTrace.upTo_restartAt.mp hrest).2)
    have hhalf' : sp.n ≤ 2 * {z | z ∈ H (tr.time i) ∧ ∃ q e,
        SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = s}.ncard := by
      have hle := Set.ncard_le_ncard (s := {z | z ∈ H (tr.time i) ∧ ∃ q e,
        SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = s ∧
          (tr.projAC.upTo (tr.time i)).time q ≤ sp.ts s + sp.Δ})
        (t := {z | z ∈ H (tr.time i) ∧ ∃ q e,
          SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = s})
        (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
      change sp.n ≤ 2 * _ at hhalf
      omega
    apply Anc.mono subU
    refine SA.batch_proposal hS.run hf hhalf' votes hpH hcp
      (SA.proposal_slot hti) hdp ⟨hOt, Or.inl hV⟩ ?_ ?_
    · intro z hz q e hv hes
      obtain ⟨R, hRV, hRroot, hOR⟩ := votes z hz q e hv hes
      obtain ⟨Hd, hHd, hHdr, _, hmem, _, hbs⟩ := SA.late_vote_held_of_frame_before hS hpH hcp hsg
        (by change _ ≤ tr.time i; rw [hti, hsucc]; linarith) le_rfl
        (fun k hki t _ => Compose.ac_deadline_le_of_restarts
          (fun k' hk' hr' => (hrsp k' (hk'.trans hki) hr').le) t) hrsp hz hv hes
        (fun Hd hHd hHdr => by
          rw [hr.coherent.1 hHd hRV (hHdr.trans hRroot.symm)]
          exact narrow hRV (hFO.trans (hOR.mono subU)))
      exact SA.heldAtProposal_iff.mpr ⟨Or.inl hmem, Hd, hHd, hHdr,
        (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _))⟩
    · apply SA.highLocksCompatible_iff.mpr
      intro lock hl hlive hsl Y hY hYr
      have hcompat := SA.highLocksCompatible_iff.mp hhigh' lock (hs ▸ hl) hlive hsl Y (subU hY) hYr
      rcases hcompat with h | h
      · exact Or.inl (narrow (hPhiV hOt) h)
      · exact Or.inr (narrow hY h)
  · have hls : l = s := by omega
    obtain ⟨CV, ellx, D, hcx, hfl, hO⟩ := ho.2.2.1
    have hfls := hls ▸ hfl
    obtain ⟨ell', hcx', hDt⟩ := Healing.fastLock_mem hfl
    obtain rfl : ellx = ell' := Option.some.inj (hcx.2.symm.trans hcx'.2)
    obtain ⟨hPhix, hPhixTree⟩ := frame_tree_subset_at hp.run hp.noColl ho.1 hcx
    have hPhixU : ellx.frame.tree ⊆ tr.HonestBlocksAt H := by
      intro C hC
      exact ⟨x, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hm hq.le,
        ho.1, hPhixTree hC⟩
    have hOD : Anc (tr.HonestBlocksAt H) O D := by
      rw [hO]
      exact (SA.anc_viableAncestor ellx.frame D).mono hPhixU
    rcases hfls with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | hop
    · have ht' : tr.time r = sp.ts s + 6 * sp.Δ := ht
      rw [hsucc] at hrt
      linarith
    refine SA.Growing.optimistic_first_proposal_anc_at hac hf ho.1 hop hOD hpH hci
      (SA.proposal_slot hti) hd ⟨hOt, Or.inl hV⟩ ?_ hhigh'
    intro v hv
    obtain ⟨hvs, hsend, B, hB, hBr, hDB, hacc⟩ := fastLock_writer_at hac.localRun ho.1
      (Or.inr hop) v hv
    have hFB := hFO.trans (hOD.trans hDB)
    refine SA.Growing.heldAtProposal_of_writer_at hac.localRun
      (hp.sync.ac_service_at hp.run (SA.le_gbar g))
      (by linarith) (b := b) (by rw [hti, hsucc] at hib; linarith) hpH hci hti hrs hvs hsend
      ⟨B, hB, hBr, hFB, ?_⟩
    rcases hacc with hg | ⟨q, hqH, hq, hqt⟩
    · exact Or.inl hg
    by_cases hg : SA.gbar g ≤ tr.time q
    · exact Or.inr (Or.inl ⟨q, hqH, hq, hg, hqt⟩)
    · have hprex := hp.run.upTo (hp.run.time_nonneg q)
      obtain ⟨ellq, hcq, hblock⟩ := hq
      have hcq' := (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hcq⟩
      obtain ⟨q', rfl, haq', htime⟩ := Compose.acBlock_prev hprex.toLocalRun hqH hcq' hblock
      obtain ⟨hqq, haq⟩ := (Trace.upTo_callAt tr).mp haq'
      change tr.time q' = tr.time (q' + 1) at htime
      have hex : ∃ k, SA.gbar g + 2 * sp.Δ ≤ tr.time k := ⟨i, by rw [hti, hsucc]; linarith⟩
      have hfirst : tr.FirstCutFrom (Nat.find hex) (SA.gbar g + 2 * sp.Δ) :=
        ⟨Nat.find_spec hex, fun k hk => not_le.mp (Nat.find_min hex hk)⟩
      have hki : Nat.find hex ≤ i := Nat.find_min' hex (by rw [hti, hsucc]; linarith)
      have hpy := hp.run.upTo ht0
      have hBF : Anc (tr.HonestBlocksAt H) (tr.state p (Nat.find hex)).fg.F B := by
        have hF := Healing.run_F_mono hpy.toLocalRun hpH hki
        rw [RunTrace.upTo_state_of_le hm (hm hki), RunTrace.upTo_state_of_le hm le_rfl] at hF
        have hframe := Compose.frame_of_projAC hpy hpH (by rw [RunTrace.upTo_projAC]; exact hcp)
        rw [RunTrace.upTo_state_of_le hm le_rfl] at hframe
        have hFeq : ell.frame.F = (tr.state p i).fg.F := congrArg Frame.F hframe
        have hFB' : Anc (tr.HonestBlocksAt H) (tr.state p i).fg.F B := by rwa [← hFeq]
        exact (hF.mono subU).trans hFB'
      obtain ⟨k, hkk, hak⟩ := hc x q' B (hp.run.antitone hqq hqH) haq
        (by rw [htime]; exact not_le.mp hg) p _
        (hp.run.antitone (hfirst.1.trans (hm hki)) hpH) hfirst hBF
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

end Consensus.Goldilocks.Healing.Growing

end
