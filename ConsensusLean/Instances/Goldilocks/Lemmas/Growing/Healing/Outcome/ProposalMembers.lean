module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Proposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.OptimisticParent
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalPasses
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Pre-cut healed members below a post-drain proposal parent -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ} {hold : Time}

private theorem result_proposal_parent_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hc : HighSourceCover tr H g a b)
    {x p : Fin sp.n} {r s i u : Nat}
    (hx : x ∈ H (tr.time r)) (hpH : p ∈ H (tr.time i))
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s B CV)
    (hs : healedOriginFloor sp a ≤ s) (hrb : tr.time r ≤ b)
    (hsu : s + 2 ≤ u) (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocksAt H) B d.head := by
  have hm := hp.run.time_mono
  have hi0 := hp.run.time_nonneg i
  have hS := healthy_base_of_reset_catch_before_at hp hi0 hib
  have hr := hS.run.localRun
  have hU := Compose.Growing.honestBlocksAt_coherent hp.run hp.noColl
  have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) hi0
  have hΔ := sp.toParams.hΔ
  have hmem : Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
      (healedOriginFloor sp a) B s b :=
    Compose.Growing.HealedOrigin.of_origin hs
      (Compose.Growing.originWithin_iff.2 ⟨x, r, CV, hx, hrb, Or.inl hres⟩)
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by
    have := sp.two_le_k
    simp only [healedOriginFloor, healedLockFloor] at hs
    omega
  have hcut := hp.clean_window_timing_at hclean s (by have := sp.two_le_k; omega)
  have hsg : AC.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have := Healing.lt_cutZ sp g
    linarith
  have hcp := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
  obtain ⟨hPhi, hPhiV⟩ := AC.frameIn_of_callAt hr hpH hcp
  have hPhiU := hPhiV.trans hsub
  have hBx : B ∈ (tr.state x r).fg.tree := by
    obtain ⟨ellx, hu, hconf, -⟩ := hres
    exact (frame_tree_subset_at hp.run hp.noColl hx hu.1).2
      (AC.deepest_mem hconf).1.1
  have hdomain : Anc (tr.HonestBlocksAt H) B ell.frame.F ∨
      B ∈ ell.frame.viableTree ell.frame.tree := by
    refine ProposalImpl.held_target_proposal_domain_before_covered_at hp hx hpH hBx hci
      hcall hd hti hib
      (ProposalImpl.raw_writer_held_at_slot_start_at hp hx hpH (Or.inl hres) .refl hsg
        (by omega) hci hti hib) ?_ ?_
    · obtain ⟨v, q, m, S, hseed, hqa, -⟩ := hp.reset_seed_at
      have hqt : tr.time q < sp.ts u := by
        have hau : sp.slot a < u := by
          rw [drainTime_eq] at hR
          have := (AC.ts_le_iff sp).mp hR
          omega
        by_contra h
        have ha0 := (hp.run.time_nonneg q).trans hqa
        have := (AC.ts_le_iff_le_slot sp ha0 u).mp ((not_lt.mp h).trans hqa)
        omega
      exact ⟨v, q, m, S, hseed, hqt,
        hc.s1 B s S m hmem (Compose.Growing.HealedOrigin.of_high
          (hqa.trans hp.reset_le) hseed)⟩
    · refine compatibleWithOrigins_iff.2 ⟨?_, ?_⟩
      · intro v q m O hqi ho
        exact hc.s1 B s O m hmem
          (Compose.Growing.HealedOrigin.of_high ((hm hqi.le).trans hib) ho)
      · exact fun _ D j hD _ => hc.s1 B s D j hmem hD.healedOrigin
  rcases hdomain with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A, _, hstart, _⟩ := Compose.acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU
      ((AC.fcRoot_anc_getAnchor hPhi A (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  obtain ⟨σ, rfl⟩ : ∃ σ, u = σ + 1 := ⟨u - 1, by omega⟩
  have hsucc : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := AC.ts_succ σ
  have hσg : AC.gbar g + 4 * sp.Δ ≤ sp.ts σ :=
    hsg.trans ((AC.ts_le_iff sp).mpr (by omega))
  have hσD : sp.ts σ + sp.Δ ≤ tr.time i := by rw [hti, hsucc]; linarith
  have votes : ∀ z ∈ H (tr.time i), ∀ q e,
      AC.VoteAt (tr.projAC.upTo (tr.time i)) z q e → e.msg.slot = σ →
      AC.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) e.msg B := by
    intro z hz q e hv hes
    obtain ⟨hqi, hv₀⟩ := AC.upTo_voteAt.mp hv
    obtain ⟨R, hR, hRr, -⟩ := AC.honest_headU hS.run.toU hz hv
    obtain ⟨R', hR', hR'r, hBR⟩ := hc.s2 B s hmem z q e
      (Compose.Growing.hVoteAt_iff.2 ⟨hp.run.antitone hqi hz, hv₀⟩)
      (hqi.trans hib) (by omega)
    rw [hU.1 hR' (hsub hR) (hR'r.trans hRr.symm)] at hBR
    exact ⟨R, hR, hRr,
      RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hi0 hR hBR⟩
  have hrestart : ∀ z ∈ H (tr.time i), ∀ q,
      ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) z q →
      tr.time q ≤ sp.ts ((σ : Int) - 1) := by
    intro z hz q hrest
    obtain ⟨hqi, hrest⟩ := ACTrace.upTo_restartAt.mp hrest
    apply (hp.restart_le_before_at (hp.run.antitone hqi hz)
      (Compose.projAC_restartAt.mp hrest) (hqi.trans hib)).trans
    rw [Healing.cutZ_eq] at hcut
    have := (AC.ts_le_iff sp).mp hcut
    exact (AC.ts_le_iff sp).mpr (by omega)
  have hrs : ∀ q ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) p q →
      tr.time q < sp.ts σ := by
    intro q _ hrest
    exact (hrestart p hpH q hrest).trans_lt ((AC.ts_lt_iff sp).mpr (by omega))
  have hhalf := AC.honest_voters_half_before hS hσg hσD
    (fun z hz q _ hrest => hrestart z hz q hrest)
  have hhalf' : sp.committeeSize ≤ 2 * {z | z ∈ H (tr.time i) ∧ ∃ q e,
      AC.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = σ}.ncard := by
    have hle := Set.ncard_le_ncard (s := {z | z ∈ H (tr.time i) ∧ ∃ q e,
      AC.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = σ ∧
        (tr.projAC.upTo (tr.time i)).time q ≤ sp.ts σ + sp.Δ})
      (t := {z | z ∈ H (tr.time i) ∧ ∃ q e,
        AC.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = σ})
      (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
    omega
  have hst : (tr.projAC.upTo (tr.time i)).state p i = tr.projAC.state p i :=
    Trace.upTo_state _ p fun _ hq => hm hq.le
  have hd' : (AC.acProposal sp ((tr.projAC.upTo (tr.time i)).state p i)
      ell.frame ((tr.projAC.upTo (tr.time i)).time i)).2 = some (d, pay) := by
    rw [hst]; exact hd
  apply Anc.mono hsub
  refine AC.batch_proposal hS.run
    (hS.cs2 σ (by linarith) (by linarith)) hhalf' votes hpH hcp
    (fun v hv => hS.hP.1 p hpH i σ v hv) (AC.proposal_slot hti) hd'
    ⟨hV.1, Or.inl hV⟩ ?_ ?_
  · intro z hz q e hv hes
    obtain ⟨R, hR, hRr, hBR⟩ := votes z hz q e hv hes
    obtain ⟨Hd, hHd, hHdr, _, hpool, _, hbs⟩ :=
      AC.late_vote_held_of_frame_before hS hpH hcp hσg
        (by change _ ≤ tr.time i; rw [hti, hsucc]; linarith) le_rfl
        (fun k hki t _ => Compose.ac_deadline_le_of_restarts
          (fun k' hk' hr' => (hrs k' (hk'.trans hki) hr').le) t) hrs hz hv hes
        (fun Hd hHd hHdr => by
          rw [hr.coherent.1 hHd hR (hHdr.trans hRr.symm)]
          exact RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hi0 hR
            (hFB.trans (hBR.mono hsub)))
    exact AC.heldAtProposal_iff.2 ⟨Or.inl hpool, Hd, hHd, hHdr,
      (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩
  · refine AC.highLocksCompatible_iff.2 fun l hl _ hlabel L hL hLr => ?_
    rw [hst] at hl
    obtain ⟨q, D, DV, hqi, hslot, hqH, hop, L', hL', hL'r, hLD⟩ :=
      ProposalImpl.proposal_high_lock_source_at hp hpH hci hcall hti
        (by rw [hsucc]; linarith) hib hl (by simpa using hlabel)
    obtain rfl : L' = L := hU.1 hL' (hsub hL) (hL'r.trans hLr.symm)
    have hDm : Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a)
        (healedOriginFloor sp a) D l.slot b :=
      Compose.Growing.HealedOrigin.of_lock (by
        simp only [healedLockFloor]
        simp only [Nat.add_sub_cancel] at hslot
        omega) (Compose.Growing.lockWithin_iff.2
          ⟨p, q, hqH, (hm hqi.le).trans hib, Or.inl ⟨DV, Or.inr hop⟩⟩)
    rcases hc.s1 D l.slot B s hDm hmem with h | h
    · exact Or.inl (RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hi0
        (hPhiV hV.1) (hLD.trans h))
    · rcases AC.anc_total hU hLD h with hLB | hBL
      · exact Or.inl (RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hi0
          (hPhiV hV.1) hLB)
      · exact Or.inr (RunTrace.anc_upTo_of_right hp.run.toLocalRun hp.noColl hi0 hL hBL)

/-- A healed member written before the proposal, with a strictly earlier label, lies below
the proposal's parent. The writing cut in `hmember` is essential: a member of label `u - 1`
written after the proposal is not an input to this statement.

Proof route: split the member's own event into its origin, lock, or high-origin arm. S2 supplies
the previous-slot votes for labels strictly before `u - 1`. At the adjacent label, update results
and fast/slow update writes occur too late; retain the optimistic writer route instead.
Reuse `reset_proposal_passes_at` in `Growing/Healing/Kernel/ProposalPasses` as the batch and
retention template: `AC.batch_proposal`, `AC.late_vote_held_of_frame_before`,
`AC.Growing.ProposalSources.optimistic_first_proposal_anc_at`, and `fastLock_writer_at`
are its two walk arms.
Historical writer delivery is `AC.Growing.heldAtProposal_of_writer_at` in
`Growing/Healing/Kernel/ProposalDelivery`; `ResetService.ac_service_at` is in
`Growing/Healing/Kernel/ProposalService`. The generic walk target is
`Compose.Growing.proposal_walk_passes_from` in `Growing/Sleepy/Service/PivotWalk`.
Use S1 for the member's compatibility with row members and stored lock writes, rather than
assuming the member is a fast `HighOrigin`. -/
theorem reset_proposal_passes_member_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hcover : HighSourceCover tr H g a b)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i))
    (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (AC.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hmember : HealedMemberBefore tr H g a b C s i) (hs : s < u) :
    Anc (tr.HonestBlocksAt H) C d.head := by
  have hm := hp.run.time_mono
  have hΔ := sp.toParams.hΔ
  have update_early : ∀ {x r ell'}, r < i →
      AC.UpdateAt tr.projAC x r s ell' → s + 2 ≤ u := by
    intro x r ell' hri hu
    have ht : tr.time r = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hle := hm hri.le
    rw [hti, ht] at hle
    by_contra h
    have hslots := (AC.ts_le_iff sp).mpr (show (u : Int) ≤ s + 1 by omega)
    have hsucc : sp.ts ((s : Int) + 1) = sp.ts s + 4 * sp.Δ := by
      simp only [AC.ACParams.ts]; ring
    rw [hsucc] at hslots
    linarith
  have optimistic : ∀ {x r CV}, x ∈ H (tr.time r) → tr.time r ≤ b →
      AC.OptimisticLockAt tr.projAC x r s C CV → healedLockFloor sp a ≤ s →
      Anc (tr.HonestBlocksAt H) C d.head := by
    intro x r CV hx hrb hop hfloor
    by_cases hsu : s + 2 ≤ u
    · exact hp.clean_source_proposal_parent_before_at hx hpH
        (Or.inl ⟨CV, Or.inr hop⟩) hfloor hsu hrb hR hci hcall hd hti hib
    · have hu : u = s + 1 := by omega
      exact hp.clean_optimistic_proposal_parent_at hx hpH hop hfloor hrb
        (hu ▸ hR) hci hcall hd (hu ▸ hti) hib
  rcases healedMemberBefore_iff.1 hmember with
    ⟨hfloor, x, r, CV, hri, hx, hrb, hres | hop⟩ |
    ⟨hfloor, x, r, hri, hx, hrb, hfast | hslow⟩ | ⟨x, r, hri, hrb, ho⟩
  · have hres' := hres
    obtain ⟨ell', hu, _, _⟩ := hres'
    exact result_proposal_parent_at hp hcover hx hpH hres hfloor hrb
      (update_early hri hu) hR hci hcall hd hti hib
  · exact optimistic hx hrb hop (by
      have := sp.two_le_k
      simp only [healedOriginFloor, healedLockFloor] at hfloor ⊢
      omega)
  · obtain ⟨CV, hf⟩ := hfast
    rcases hf with hupdate | hop
    · have hupdate' := hupdate
      obtain ⟨ell', D, hu, _⟩ := hupdate'
      exact hp.clean_source_proposal_parent_before_at hx hpH
        (Or.inl ⟨CV, Or.inl hupdate⟩) hfloor (update_early hri hu) hrb hR
        hci hcall hd hti hib
    · exact optimistic hx hrb hop hfloor
  · have hslow' := hslow
    obtain ⟨ell', D, hu, _⟩ := hslow'
    exact hp.clean_source_proposal_parent_before_at hx hpH (Or.inr hslow) hfloor
      (update_early hri hu) hrb hR hci hcall hd hti hib
  · apply hp.reset_proposal_passes_at hpH hR hci hcall hd hti hib C
    refine ⟨x, r, s, ho, ?_⟩
    obtain ⟨CV, ell', D, hcx, hf, _⟩ := ho.2.2.1
    rcases hf with ⟨ell'', E, hu, _⟩ | ⟨ell'', A, hpt, hsl, _⟩
    · have hsu := update_early hri hu
      have ht : tr.time r = sp.ts s + 6 * sp.Δ := hu.2.2.1
      have hslots := (AC.ts_le_iff sp).mpr (show (s : Int) + 2 ≤ u by omega)
      simp only [AC.ACParams.ts] at hslots ht ⊢
      linarith
    · by_contra h
      have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) u).mp (not_lt.mp h)
      change sp.slot (tr.time r) = s at hsl
      omega

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
