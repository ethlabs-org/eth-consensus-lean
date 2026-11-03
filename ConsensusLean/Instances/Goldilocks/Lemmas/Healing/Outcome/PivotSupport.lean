module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotWalk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

/-! # Goldilocks Healing: old-source proposal support

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- Every old source is below the proposal's duty head. Relay and high-origin viability put
the source on the walk; earlier-label votes or the same-label optimistic quorum favor its
chain. -/
theorem reset_proposal_passes (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root) :
    ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O d.head := by
  intro O hO
  have hpH := hP.1
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨x, r, l, ho, hrt⟩ := oldSrc_iff.1 hO
  have hlu := label_lt_of_old hp ho hrt
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hslot := SA.proposal_slot (tr := tr.projAC) hti
  have hai : a ≤ tr.time i := by rw [hti]; exact (reset_lt_ts hp hR).le
  rcases proposal_holds_old hp hpH hai hci hcall hd hti (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩)
    with hOt | hOF
  swap
  · obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hΦ hd
    exact hOF.trans (Anc.mono hΦU ((hΦ.rooted.2 _ hstart).trans hsQ))
  have hV := held_high_origin_viable hp hpH hci ho
    (by rw [hti]; exact (SA.ts_le_iff sp).2 (by omega)) hOt
  have hFO := (hΦ.rooted.2 O hOt).mono hΦU
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) s O := by
    exact proposal_stored_locks_compatible_old hp hc hP hR hci hcall hti O
      (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩)
  have hcut : cutZ sp.toParams g ≤ sp.ts s :=
    (cutZ_le_ts_of_highOrigin hp ho).trans ((SA.ts_le_iff sp).2 (by omega))
  have hgs : g ≤ sp.ts s := by
    have := le_gbar g
    have := lt_cutZ sp g
    linarith
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt p k → tr.projAC.time k < sp.ts s := by
    intro k _ hk
    have := restart_le hp hpH (Compose.projAC_restartAt.1 hk)
    have hcZ := cutZ_eq sp g
    have htlt : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) < cutZ sp.toParams g := by
      rw [hcZ]
      exact (SA.ts_lt_iff sp).2 (by omega)
    exact lt_of_le_of_lt this (htlt.trans_le hcut)
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF g (sp.ts s + 2 * sp.Δ) hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 le_rfl)
  have hheld : ∀ z ∈ H, ∀ v : SA.Vote sp.n, v.slot = s →
      (∃ k, tr.projAC.SendOrAdmit z k v ∧ sp.ts s ≤ tr.projAC.time k ∧
        tr.projAC.time k < sp.ts s + 2 * sp.Δ) →
      (∃ B ∈ tr.HonestBlocks H, B.root = v.head ∧ Anc (tr.HonestBlocks H) O B ∧
        (B.root = sp.genesisRoot ∨ ∃ k, tr.projAC.AcceptAt z k B ∧
          tr.projAC.time k < sp.ts s + 2 * sp.Δ)) →
      SA.HeldAtProposal (tr.projAC.state p i) ℓp.frame s v := by
    rintro z hz v hvs hsend ⟨B, hB, hBr, hOB, hacc⟩
    apply SA.heldAtProposal_of_writer hr hsync hgs le_rfl hz hpH hci hti hrs hvs hsend
    refine ⟨B, hB, hBr, hFO.trans hOB, ?_⟩
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · exact Or.inl hg
    refine Or.inr (Or.inl ⟨k, hk, ?_, hkt⟩)
    have := (cutZ_lt_of_anc hp ho hz (acceptAt_mem hp hz hk) hOB).1
    have := lt_cutZ sp g
    have := le_gbar g
    change g ≤ tr.time k
    linarith
  by_cases hls : l < s
  · have hvotes : ∀ z ∈ H, ∀ k e, SA.VoteAt tr.projAC z k e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg O := by
      rintro z hz k e ⟨ℓ, hcz, he⟩ hes
      exact (hret.votes x r l O ho z hz k ℓ e ⟨hcz, he⟩ (by omega)).1
    refine SA.batch_proposal hrun (faulty_lt_half hp p) (half_committee hp hcut) hvotes hpH hci
      hslot hd ⟨hOt, hV⟩ ?_ hhigh
    intro z hz k e hv hes
    obtain ⟨B, hB, hBr, hOB⟩ := hvotes z hz k e hv hes
    obtain ⟨ℓz, hcz, he⟩ := hv
    obtain ⟨⟨B', hB't, hB'r, -⟩, hkt⟩ := Compose.cast_head_fcRoot hr hz ⟨hcz, he⟩
    have hEq : B' = B := hU.1 ((SA.frameIn_of_callAt hr hz hcz).2 hB't) hB (hB'r.trans hBr.symm)
    rw [hEq] at hB't
    rw [hes] at hkt
    refine hheld z hz e.msg hes ⟨k, ⟨ℓz, hcz, Or.inl ⟨e, he, rfl⟩⟩, ?_, by linarith⟩
      ⟨B, hB, hBr, hOB, ?_⟩
    · exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by have := (SA.castAt_spec hr hz ⟨hcz, he⟩).2.1; omega)
    · rcases Compose.frame_anc_accepted hr hz k ℓz hcz B hB't B .refl with hg | ⟨k', hkk, hk⟩
      · exact Or.inl hg
      · exact Or.inr ⟨k', hk, by have := hr.time_mono hkk; linarith⟩
  · have hls : l = s := by omega
    obtain ⟨ℓx, D, CV, hcx, hfl, _, _, _, hOD, _⟩ := highOrigin_mem hp ho
    rw [hls] at hfl
    rcases hfl with ⟨ℓ', C, ⟨_, _, ht, _⟩, _⟩ | hop
    · have ht' : tr.time r = sp.ts s + 6 * sp.Δ := ht
      have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    refine optimistic_first_proposal_anc hrun (faulty_lt_half hp p) ho.1 hop
      (hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2) hpH hci hslot hd ⟨hOt, hV⟩ ?_ hhigh
    intro v hv
    obtain ⟨hvs, hsend, B, hB, hBr, hDB, hacc⟩ := fastLock_writer hr ho.1 (Or.inr hop) v hv
    exact hheld x ho.1 v hvs hsend ⟨B, hB, hBr,
      (hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2).trans hDB, hacc⟩

/-- Every pre-slot high origin lies below the bounded operational proposal's parent. -/
theorem ResetPremisesUpTo.reset_proposal_passes {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ∀ O, (∃ x r l, HighOrigin tr H g x r l O ∧ tr.time r < sp.ts u) →
      Anc (tr.HonestBlocks H) O d.head := by
  rintro O ⟨x, r, l, ho, hrt⟩
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos p; omega
  have hri : r < i := by
    by_contra hn
    have ht := hp.run.time_mono (Nat.le_of_not_gt hn)
    rw [hti] at ht
    exact (not_lt_of_ge ht) hrt
  have hrb := (hp.run.time_mono hri.le).trans hib
  have hlu := hp.origin_label_lt_at_proposal hpH hci hcall hti hri ho
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hsucc : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  have below : Anc (tr.HonestBlocks H) O ell.frame.fcRoot →
      Anc (tr.HonestBlocks H) O d.head := by
    intro hOF
    obtain ⟨_, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A, _, hstart, _⟩ := acProposal_walk hd
    rw [hstart] at hsQ
    exact hOF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A (tr.time i)).trans hsQ))
  rcases hp.proposal_holds_old hpH hci hcall hd hti hib ho hrt with hOt | hOF
  swap
  · obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
    exact hOF.trans (Anc.mono hPhiU ((hPhi.rooted.2 _ hstart).trans hsQ))
  rcases hp.held_high_origin_viable hpH hci hib ho hrb
      (by rw [hti]; exact (SA.ts_le_iff sp).mpr (by omega)) hOt with hV | hOF
  swap
  · exact below (hOF.mono hPhiU)
  have hFO := (hPhi.rooted.2 O hOt).mono hPhiU
  have hhigh := hp.proposal_stored_locks_compatible_old hc hpH hR hci hcall hti hib ho hrb
  have hhigh' : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.projAC.time i) s O := by
    change SA.HighLocksCompatible _ _ (tr.time i) s O
    simpa only [Nat.add_sub_cancel] using hhigh
  have hcut : cutZ sp.toParams g ≤ sp.ts s :=
    (hp.cutZ_le_ts_of_highOrigin ho).trans ((SA.ts_le_iff sp).mpr (by omega))
  have hsg : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := lt_cutZ sp g
    linarith
  have hsb : sp.ts s + sp.Δ ≤ b := by rw [hti, hsucc] at hib; linarith
  have hrestart : ∀ z ∈ H, ∀ q, tr.time q ≤ b → tr.projAC.RestartAt z q →
      tr.time q ≤ sp.ts ((s : Int) - 1) := by
    intro z hz q hqb hrest
    apply (restart_le_before hp hz (Compose.projAC_restartAt.mp hrest) hqb).trans
    rw [cutZ_eq] at hcut
    have := (SA.ts_le_iff sp).mp hcut
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hrs : ∀ q ≤ i, tr.projAC.RestartAt p q → tr.time q < sp.ts s := by
    intro q hqi hrest
    exact (hrestart p hpH q ((hp.run.time_mono hqi).trans hib) hrest).trans_lt
      ((SA.ts_lt_iff sp).mpr (by omega))
  by_cases hls : l < s
  · have votes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg O := by
      rintro z hz q e ⟨ell', hcast⟩ hes
      have hqb : tr.time q ≤ b := by
        have ht := SA.vote_time_le hr hz ⟨ell', hcast⟩
        have hsl := (SA.castAt_spec hr hz hcast).2.1
        rw [← hsl, hes] at ht
        exact ht.trans hsb
      exact hp.high_origin_votes_before q hqb x r l O ho hrb z hz ell' e hcast (by omega)
    have hhalf := SA.honest_voters_half_before hS hsg hsb
      (fun z hz q hqt hrest => hrestart z hz q (hqt.trans hsb) hrest)
    have hhalf' : sp.n ≤ 2 *
        {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s}.ncard := by
      change sp.n ≤ 2 * {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧
        e.msg.slot = s ∧ tr.time q ≤ sp.ts s + sp.Δ}.ncard at hhalf
      have hle := Set.ncard_le_ncard (s := {z | z ∈ H ∧ ∃ q e,
        SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s ∧ tr.time q ≤ sp.ts s + sp.Δ})
        (t := {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = s})
        (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
      omega
    refine SA.batch_proposal hS.run hf hhalf' votes hpH hci
      (SA.proposal_slot hti) hd ⟨hOt, Or.inl hV⟩ ?_ hhigh'
    intro z hz q e hv hes
    obtain ⟨H', hH', hHr', hOH⟩ := votes z hz q e hv hes
    obtain ⟨Hd, hHd, hHdr, _, hmem, _, hbs⟩ := SA.late_vote_held_of_frame_before hS hpH hci hsg
      (by change _ ≤ tr.time i; rw [hti, hsucc]; linarith) hib
      (fun k hki t _ => deadline_le_restarts
        (fun k' hk' hr' => (hrs k' (hk'.trans hki) hr').le) t) hrs hz hv hes
      (fun Hd hHd hHdr => by
        rw [hU.1 hHd hH' (hHdr.trans hHr'.symm)]
        exact hFO.trans hOH)
    exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHd, hHdr,
      (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩
  · have hls : l = s := by omega
    obtain ⟨ellx, D, CV, hcx, hfl, _, _, _, hOD, _⟩ := hp.highOrigin_mem ho
    rw [hls] at hfl
    rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | hop
    · have ht' : tr.time r = sp.ts s + 6 * sp.Δ := ht
      rw [hsucc] at hrt
      linarith
    have hODU := hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2
    refine optimistic_first_proposal_anc hS.run hf ho.1 hop hODU hpH hci
      (SA.proposal_slot hti) hd ⟨hOt, Or.inl hV⟩ ?_ hhigh'
    intro v hv
    obtain ⟨hvs, hsend, B, hB, hBr, hDB, hacc⟩ := fastLock_writer hr ho.1 (Or.inr hop) v hv
    have hFB := hFO.trans (hODU.trans hDB)
    refine SA.heldAtProposal_of_writer hr (hp.sync.syncAC hp.run (le_gbar g))
      (by linarith) le_rfl ho.1 hpH hci hti hrs hvs hsend ⟨B, hB, hBr, hFB, ?_⟩
    rcases hacc with hg | ⟨q, hq, hqt⟩
    · exact Or.inl hg
    by_cases hg : SA.gbar g ≤ tr.time q
    · exact Or.inr (Or.inl ⟨q, hq, hg, hqt⟩)
    · obtain ⟨k, hki, hak, hkt⟩ := hS.catchUp.relay x ho.1 q B hq (not_le.mp hg) p hpH i ell hci
        (by change _ ≤ tr.time i; rw [hti, hsucc]; linarith) hib hFB
      exact Or.inr (Or.inr ⟨k, hki, hak, by change tr.time k < _ at hkt ⊢; linarith⟩)

/-- A crossing below an origin written before a serving proposal is below its duty parent.
The explicit timestamp preserves the provenance needed by bounded report consumers. -/
theorem crossing_below_proposal_parent
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {x : Fin sp.n} {r l : Nat} {X O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u)
    (hXO : Anc (tr.HonestBlocks H) X O) : Anc (tr.HonestBlocks H) X d.head :=
  hXO.trans (reset_proposal_passes hp hc hP hR hci hcall hd hti hPQ O
    (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩))

/-- The proposal root is genesis or below an old source. High `J` has a crossing row signed
before the proposal. Low `J` is below the held reset seed by the root's no-contest condition. -/
theorem reset_proposal_fcRoot (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root) :
    ℓp.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot O := by
  have hpH := hP.1
  have hU := honest_coherent hp
  have hr := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, i, hX⟩
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  obtain ⟨hFm, hJm, hFJ, ⟨B, hBm, hBJ, hBhj⟩, hmax, -⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBm
  obtain rfl : E = (tr.state p i).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBJ)
  have hroot : (tr.state p i).fg.fcRoot = (tr.state p i).fg.J ∨
      (tr.state p i).fg.fcRoot = (tr.state p i).fg.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    rw [hfr]
    rcases hroot with h | h
    · exact congrArg (·.root) (h.trans hg)
    · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
      rw [← hg] at hJF
      have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
      exact congrArg (·.root) (h.trans (he.trans hg))
  by_cases hh : HZ tr H g + 1 ≤ (tr.state p i).fg.hj
  · obtain ⟨W, hW, att, ha, v, hv, k', hki, hs, haT, -⟩ :=
      left_entry_origin hp hpH hJm hJT (by omega) hEB
        (by have := Store.hj_lt_h hr hBm; omega)
    obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run hv hs
    obtain rfl : E' = (tr.state p i).fg.J :=
      hU.1 ⟨v, hv, k', hE'⟩ (hsub hJm) (hE'r.trans haT)
    have hah : HZ tr H g + 1 ≤ att.h := by
      rw [← hE'h, σ_eq_run hp hv hpH hE' hJm, hJh, hBhj]
      exact hh
    obtain ⟨D, O, hDs, hO, hDO⟩ := proposal_high_row hp hpH hci hcall hti hv hki hs hah
    obtain ⟨z, hz, r, -, -, hJD, -, -⟩ :=
      Compose.honest_source_entry hp.run hp.noColl hDs (hsub hJm) haT.symm
    have hJO := (Anc.mono (T := tr.HonestBlocks H) (fun X hX => ⟨z, hz, r, hX⟩) hJD).trans hDO
    right
    refine ⟨O, hO, ?_⟩
    rw [hfr]
    change Anc _ (tr.state p i).fg.fcRoot O
    rcases hroot with h | h
    · rw [h]; exact hJO
    · rw [h]; exact (hFJ.mono hsub).trans hJO
  obtain ⟨v, r, l, O, ho, hl, hrt⟩ := reset_seed hp
  have hO : OldSrc tr H g u O := oldSrc_iff.2 ⟨v, r, l, ho, hrt.trans_lt (reset_lt_ts hp hR)⟩
  have hFO : Anc (tr.HonestBlocks H) (tr.state p i).fg.F O := by
    rcases finalized_compatible_high_origin hp hpH
      (by rw [hti]; exact (reset_lt_ts hp hR).le) ho with h | h
    · exact h
    · have hOJ := h.trans (hFJ.mono hsub)
      have := high_of_anc hp ho hpH hJm hOJ
      rw [hJh, hBhj] at this
      omega
  right
  refine ⟨O, hO, ?_⟩
  rw [hfr]
  change Anc _ (tr.state p i).fg.fcRoot O
  unfold Store.fcRoot
  split_ifs with hchoose
  · have hOt : O ∈ ℓp.frame.tree := by
      rcases proposal_holds_old hp hpH (by rw [hti]; exact (reset_lt_ts hp hR).le)
        hci hcall hd hti hO with h | h
      · exact h
      · rw [hfr] at h
        have := high_of_anc hp ho hpH hJm (h.trans (hFJ.mono hsub))
        rw [hJh, hBhj] at this
        omega
    rw [hfr] at hOt
    have hOh := high_of_anc hp ho hpH hOt.1 .refl
    have hOm := hmax O hOt.1
    have hJO : (tr.state p i).fg.Anc (tr.state p i).fg.J O := by
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, O, hOt.1, hOt.2, by omega, hn⟩
    exact hJO.mono hsub
  · exact hFO

/-- Bounded pre-slot origins suffice to bound an actual proposal's height floor. -/
theorem ResetPremisesUpTo.proposal_floor_above_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} (hci : tr.projAC.CallAt p i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state p i).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u → tr.time r ≤ b →
      Anc (tr.HonestBlocks H) O B) :
    (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h := by
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH i
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, hrb, _, hrt⟩ := hp.reset_seed_before_slot hR
  have hBh := hp.high_of_anc ho₀ hpH hB (hBold v₀ r₀ l₀ O₀ ho₀ hrt hrb)
  have hnc := hp.no_high_contest hpH i (fun q hq => (hp.run.time_mono hq.le).trans hib)
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state p i).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state p i).fg.headHeightFloor = (tr.state p i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨_, _, _, _, _, ⟨C, hC, hCh⟩, _⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state p i).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨_, _, _, _, v, _, d, hdj, _, _, r, hrd, l, O, ho, hEO⟩ :=
    hp.left_entry_origin hpH hE hET (by omega) hEC (by omega)
  have hlu := hp.origin_label_lt_at_proposal hpH hci hcall hti (by omega : r < i) ho
  obtain ⟨_, D, CV, _, hf, _⟩ := hp.highOrigin_mem ho
  have hrt : tr.time r < sp.ts u := hp.fastLock_time_lt hf hlu (by
    have := hp.run.time_mono (by omega : r ≤ i)
    rw [hti] at this
    have := sp.toParams.hΔ
    linarith)
  have hEB := hEO.trans (hBold v r l O ho hrt ((hp.run.time_mono (by omega)).trans hib))
  have := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hpH hEB hB)
  omega

/-- The finite proposal root is genesis or below a bounded pre-slot high origin. -/
theorem ResetPremisesUpTo.reset_proposal_root_source {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b ∧
        Anc (tr.HonestBlocks H) ell.frame.fcRoot O := by
  have hU := hp.honest_coherent
  have hr := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, i, hX⟩
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  obtain ⟨hFm, hJm, hFJ, ⟨B, hBm, hBJ, hBhj⟩, hmax, _⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBm
  obtain rfl : E = (tr.state p i).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBJ)
  have hroot : (tr.state p i).fg.fcRoot = (tr.state p i).fg.J ∨
      (tr.state p i).fg.fcRoot = (tr.state p i).fg.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    rw [hfr]
    rcases hroot with h | h
    · exact congrArg (·.root) (h.trans hg)
    · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
      rw [← hg] at hJF
      have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
      exact congrArg (·.root) (h.trans (he.trans hg))
  right
  by_cases hh : HZ tr H g + 1 ≤ (tr.state p i).fg.hj
  · obtain ⟨_, _, _, _, v, _, k', hki, _, _, r, hrk, l, O, ho, hJO⟩ :=
      hp.left_entry_origin hpH hJm hJT (by omega) hEB
        (by have := Store.hj_lt_h hr hBm; omega)
    have hlu := hp.origin_label_lt_at_proposal hpH hci hcall hti (by omega : r < i) ho
    obtain ⟨_, D, CV, _, hfl, _⟩ := hp.highOrigin_mem ho
    have hrt : tr.time r < sp.ts u := hp.fastLock_time_lt hfl hlu (by
      have := hp.run.time_mono (by omega : r ≤ i)
      rw [hti] at this
      have := sp.toParams.hΔ
      linarith)
    refine ⟨v, r, l, O, ho, hrt, (hp.run.time_mono (by omega)).trans hib, ?_⟩
    rw [hfr]
    change Anc _ (tr.state p i).fg.fcRoot O
    rcases hroot with h | h
    · rw [h]; exact hJO
    · rw [h]; exact (hFJ.mono hsub).trans hJO
  obtain ⟨v, r, l, O, ho, hrb, _, hrt⟩ := hp.reset_seed_before_slot hR
  have hFO := hp.low_finalized_below_origin hpH i (by omega) ho
  refine ⟨v, r, l, O, ho, hrt, hrb, ?_⟩
  rw [hfr]
  change Anc _ (tr.state p i).fg.fcRoot O
  unfold Store.fcRoot
  split_ifs with hchoose
  · have hOt : O ∈ ell.frame.tree := by
      rcases hp.proposal_holds_old hpH hci hcall hd hti hib ho hrt with h | h
      · exact h
      · rw [hfr] at h
        have := hp.high_of_anc ho hpH hJm (h.trans (hFJ.mono hsub))
        rw [hJh, hBhj] at this
        omega
    rw [hfr] at hOt
    have hOh := hp.high_of_anc ho hpH hOt.1 .refl
    have hOm := hmax O hOt.1
    have hJO : (tr.state p i).fg.Anc (tr.state p i).fg.J O := by
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, O, hOt.1, hOt.2, by omega, hn⟩
    exact hJO.mono hsub
  · exact hFO


end Consensus.Goldilocks.Healing
