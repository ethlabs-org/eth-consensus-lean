module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Healed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OperationalPersistence
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRowSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix

public section

/-! # Goldilocks Obligations: C4 of the Healed bundle from the reset (WI-17)

consensus-lean#135, WI-17; workbench `notes/fg-liveness/r14-end-to-end/s4-follow.md` L4.6 (C4,
no reorg of honest blocks). Under `Healing.ResetPremises` and Catch(2Δ), an honest operational
proposal of a post-drain slot `s` is an ancestor of every honest proposal of a slot `s' ≥ s + 2`
(`honest_proposal_below_later_upTo`, from `UpTo.operational_proposal_below_later_parent`). Every
honest proposal is operational (`proposesAt_of_honestProposalRun`), and the adjacent pairs
`s' = s + 1` follow from the slot-`s` batch (`honest_proposal_below_next_upTo`,
`SA.batch_proposal`). -/

namespace Consensus.Goldilocks.Obligations

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-! ### The operational form of an honest proposal -/

/-- **An honest proposal is made operationally.** The proposer accepts `P` in the AC projection,
so its FG accepts `P` at the previous cut; `P` has an honest proposer, so that call is preceded by
the proposer's own block call of `P` (unforgeable blocks), which is a tick's, at `t_{slot(P)}`.
The converse of `Healing.honestProposalRun_of_proposesAt`. -/
theorem proposesAt_of_honestProposalRun (hrun : GoldilocksRun proposer dg H tr) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : Healing.HonestProposalRun tr H proposer s P) :
    ∃ k, tr.ProposesAt (proposer s) k P := by
  have hl := hrun.toLocalRun
  obtain ⟨hpH, -, -, -, -, -, -, -, -, -, -, hPp, -, j, -, hacc, -⟩ := hP
  obtain ⟨j₀, -, ha, -⟩ := Healing.fg_accept_before hl hpH hacc
  obtain ⟨j', -, ⟨acc, hc⟩, hpos⟩ := hl.block_unforgeable _ hpH j₀ P ⟨true, ha⟩ (hPp ▸ hpH)
  rw [hPp] at hc
  rcases Compose.blockCall_cases hl hpH hc with hg | ⟨j₁, x, rfl, -, hpr, d', pay', -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  · have hs : P.slot = sp.toParams.slotOf (tr.time (j₁ + 2)) := by rw [hB]; rfl
    exact ⟨j₁ + 2, ⟨⟨acc, hc⟩, hpos⟩, hPp, hs ▸ hpr.2.1⟩

/-! ### Adjacent slots -/

/-- The duty head of a proposal is the walk from the anchor after the proposal's unlocking (as
`Healing.Outcome.Pivot`'s private `acProposal_walk`). -/
private theorem acProposal_start_anchor {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {t : Time}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    ∃ A₁ : SA.SAState sp.n, d.start = SA.getAnchor sp A₁ Φ t := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, rfl⟩

/-- **No reorg one slot on, finite horizon.** A post-drain operational proposal `P` of slot `u` is
an ancestor of the duty head of every honest proposal of slot `u + 1` (`SA.batch_proposal` with
`σ = u` and `B = P`): the honest slot-`u` votes are all `P` (`operational_unanimous`), half of
the committee votes, `P` is in the proposer's domain (`held_target_proposal_domain_before`), the
live high locks compare with `P`, and the votes are held at the proposal. -/
theorem UpTo.operational_proposal_below_next_parent {b : Time}
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (u + 1 : Nat)) :
    Anc (tr.HonestBlocks H) P d.head := by
  have hΔ := sp.toParams.hΔ
  have hS := Healing.healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos y; omega
  have hσ : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hib : tr.time i ≤ b := by rw [hti, hσ]; linarith
  have hσb : sp.ts u + sp.Δ ≤ b := by linarith
  have hacc := Compose.proposal_accepted hp.run hp.noColl hpH hactual
  have hPx : P ∈ (tr.state p (k + 1)).fg.tree := by
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hpH _)).1 P _
        (hp.run.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
    exact Set.mem_insert _ _
  have hPU : P ∈ tr.HonestBlocks H := ⟨p, hpH, k + 1, hPx⟩
  have hca := Healing.cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨q, hq, _⟩ := hp.snapshot; exact ⟨q, hq⟩) hp.reset
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    linarith
  have hau : sp.slot a + 2 * sp.k + 5 ≤ u := by
    rw [Healing.drainTime_eq] at hR
    exact_mod_cast (SA.ts_le_iff sp).1 hR
  have hu : 0 < u := by omega
  have hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 2) ≤ sp.ts u :=
      (SA.ts_le_iff sp).2 (by omega)
    have hgap : sp.ts ((sp.slot a : Int) + 2) =
        sp.ts ((sp.slot a : Int) + 1) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    have := Healing.lt_cutZ sp g
    rw [hgap] at hle
    linarith
  have hun : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z hz q e hv hqb hs =>
    hp.operational_unanimous hc hpH hdesignated hactual hPs hR (by linarith)
      z hz q e hv hs hqb
  have hRnext : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat) :=
    hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hci
  have hdom : Anc (tr.HonestBlocks H) P ell.frame.fcRoot ∨
      P ∈ ell.frame.viableTree ell.frame.tree := by
    refine hp.held_target_proposal_domain_before hpH hy hPx hci hcall hd hti hib ?_ ?_ ?_
    · intro hFP
      rw [Compose.frame_of_projAC hp.run hy hci] at hFP
      exact UpTo.unanimous_head_held_at_call hp hc hPU hun hgu hRnext hy hci
        (by rw [hti, hσ]; linarith) hib hFP
    · obtain ⟨x, q, m, S, ho, -, -, hqt⟩ := hp.reset_seed_before_slot hR
      exact ⟨x, q, m, S, ho, hqt.trans (by rw [hσ]; linarith),
        Or.inr (UpTo.old_origin_below_unanimous hp hc hPU hun hgu hRnext hσb ho hqt)⟩
    · intro v q m O hqi ho
      have hq : tr.time q ≤ sp.ts u + 6 * sp.Δ := by
        have := hp.run.time_mono hqi.le
        rw [hti, hσ] at this
        linarith
      exact (UpTo.high_origin_compatible_before_update hp hc hPU hPs hu hun hgu hRnext hTb
        ho hq).symm
  rcases hdom with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, hstart⟩ := acProposal_start_anchor hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 P hV.1).mono hPhiU
  have votes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
    rintro z hz q e ⟨ell', hc'⟩ hslot
    have hqb : tr.time q ≤ b := by
      have ht := SA.vote_time_le hr hz ⟨ell', hc'⟩
      have hsl := (SA.castAt_spec hr hz hc').2.1
      rw [← hsl, hslot] at ht
      exact ht.trans hσb
    exact ⟨P, hPU, (hun z hz q e ⟨ell', hc'⟩ hqb hslot).symm, .refl⟩
  have hrestart : ∀ z ∈ H, ∀ q, tr.time q ≤ b → tr.projAC.RestartAt z q →
      tr.time q ≤ sp.ts ((u : Int) - 1) := fun z hz q hqb hrest =>
    UpTo.restart_before_unanimous_slot hp hRnext hz (Compose.projAC_restartAt.mp hrest) hqb
  have hrs : ∀ q ≤ i, tr.projAC.RestartAt y q → tr.time q < sp.ts u := by
    intro q hqi hrest
    exact (hrestart y hy q ((hp.run.time_mono hqi).trans hib) hrest).trans_lt
      ((SA.ts_lt_iff sp).mpr (by omega))
  have hhalf := SA.honest_voters_half_before hS hgu hσb
    (fun z hz q hqt hrest => hrestart z hz q (hqt.trans hσb) hrest)
  have hhalf' : sp.n ≤ 2 *
      {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = u}.ncard := by
    change sp.n ≤ 2 * {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧
      e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ}.ncard at hhalf
    have hle := Set.ncard_le_ncard (s := {z | z ∈ H ∧ ∃ q e,
      SA.VoteAt tr.projAC z q e ∧ e.msg.slot = u ∧ tr.time q ≤ sp.ts u + sp.Δ})
      (t := {z | z ∈ H ∧ ∃ q e, SA.VoteAt tr.projAC z q e ∧ e.msg.slot = u})
      (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
    omega
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state y i)
      (tr.time i) u P := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
    obtain ⟨L, hL, hLr, O, hLO, q, hqi, CV, hO⟩ := SA.lock_below_origin hr hy i l hl
    obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
    have hcomp : Compatible (tr.HonestBlocks H) O P := by
      rcases hO with ⟨ell', ⟨_, _, ht, _⟩, _⟩ | ⟨ellO, A, hpt, hsl, hsel, hCV⟩
      · have htime := hr.time_mono hqi.le
        have hle := (SA.ts_le_iff sp).mpr (show (u : Int) ≤ l.slot by omega)
        change tr.time q ≤ tr.time i at htime
        change tr.time q = sp.ts l.slot + 6 * sp.Δ at ht
        rw [hti, hσ] at htime
        exfalso
        linarith
      · have hle : l.slot ≤ u := by
          have htime := hp.run.time_mono hqi.le
          have hne : l.slot ≠ u + 1 := fun he =>
            Healing.proposal_no_optimistic_of_run hp.run hp.noColl hf hy hci hcall hti
              y hy q hqi O CV (he ▸ ⟨ellO, A, hpt, hsl, hsel, hCV⟩)
          have hstart := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) (l.slot : Int)).mpr
            (by change sp.slot (tr.time q) = l.slot at hsl; omega)
          rw [hti] at htime
          have := (SA.ts_le_iff sp).mp (hstart.trans htime)
          omega
        have hΦU := (SA.frameIn_of_callAt hr hy hpt.1).2
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        have h34 := (SA.deepest_mem hsel).1.2.1
        rw [hsl] at h34
        refine SA.origin_compatible hU hΦU h34 hf fun v hv hvH => ?_
        obtain ⟨hvs, q', _, e', hv', rfl⟩ := SA.optimisticPoint_pool_vote hS.run hy hpt hv hvH
        exact votes _ hvH q' e' hv' (by rw [hvs]; omega)
    rcases hcomp with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  refine SA.batch_proposal hS.run hf hhalf' votes hy hci
    (SA.proposal_slot hti) hd ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  intro z hz q e hv he
  obtain ⟨H', hH', hHr', hBH⟩ := votes z hz q e hv he
  obtain ⟨Hd, hHd, hHdr, _, hmem, _, hbs⟩ := SA.late_vote_held_of_frame_before hS hy hci hgu
    (by change _ ≤ tr.time i; rw [hti, hσ]; linarith) hib
    (fun k hki t _ => Healing.deadline_le_restarts
      (fun k' hk' hr' => (hrs k' (hk'.trans hki) hr').le) t) hrs hz hv he
    (fun Hd hHd hHdr => by
      rw [hU.1 hHd hH' (hHdr.trans hHr'.symm)]
      exact hFB.trans hBH)
  exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHd, hHdr,
    (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩

end Consensus.Goldilocks.Obligations

end
