module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HonestProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Domain
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # C4 of the healed window under growing faults: no reorg of honest proposals

The growing form of `Obligations/HealedC4` and of the window-facing C4 wrappers of
`Obligations/HealedUpTo`, with each proposer honest through its own slot's `t_s + hold`:

* `proposesAt_of_honestProposalRun_at`: an honest proposal run is made operationally;
  `honestProposalRun_slot_at`, `accept_of_proposesAt_at` (the static `accept_of_proposesAt` on the
  prefix through the proposal cut), `proposer_mem_of_proposesAt_at`, `proposal_held_at`: its
  slot, its proposer's honesty at the proposal cut, the acceptance and the holding after it;
* `UpTo.operational_proposal_below_next_parent_at`: under the finite reset premises and
  Catch(2Δ), a post-drain operational proposal of slot `u` is an honest ancestor of the duty head
  of every honest proposal call at `t_{u+1}`;
* `honest_proposal_child_at`: an honest proposal is the child of the duty head of its call. -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **An honest proposal run is made operationally**: its proposer proposes it at some cut. -/
theorem proposesAt_of_honestProposalRun_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) :
    ∃ k, tr.ProposesAt (proposer s) k P := by
  obtain ⟨hpH, -, -, -, -, -, -, -, -, -, -, hPp, -, j, -, hacc, htj⟩ := hP
  change tr.time j = sp.ts s at htj
  have hd := hrun.time_nonneg j
  have hl := (hrun.upTo hd).toLocalRun
  have hp : proposer s ∈ H (tr.time j) := hrun.antitone (by
    rw [htj]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hacc' : (tr.upTo (tr.time j)).projAC.AcceptAt (proposer s) j P := by
    obtain ⟨ℓ, hc, hb⟩ := hacc
    rw [RunTrace.upTo_projAC]
    exact ⟨ℓ, (Trace.upTo_callAt_of_le _ le_rfl).mpr hc, hb⟩
  obtain ⟨j₀, -, ha, -⟩ := Healing.fg_accept_before hl hp hacc'
  obtain ⟨j', -, ⟨acc, hc⟩, hpos⟩ := hl.block_unforgeable _ hp j₀ P ⟨true, ha⟩ (hPp ▸ hp)
  rw [hPp] at hc
  rcases Compose.blockCall_cases hl hp hc with hg | ⟨j₁, x, rfl, -, hpr, d', pay', -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  · have hs : P.slot = sp.toParams.slotOf (tr.time (j₁ + 2)) := by rw [hB]; rfl
    have hown : (tr.upTo (tr.time j)).OwnBlockAt (proposer s) (j₁ + 2) P := ⟨⟨acc, hc⟩, hpos⟩
    exact ⟨j₁ + 2, ((RunTrace.upTo_ownBlockAt _).mp hown).2, hPp, hs ▸ hpr.2.1⟩

/-- The block of an honest proposal run of slot `s` has slot `s`. -/
theorem honestProposalRun_slot_at {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) : P.slot = s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hs, -⟩ := hP
  exact hs

/-- **A proposal of a node honest at its proposal cut is accepted there**, with the block in its
tree after the cut (the static `accept_of_proposesAt` on the prefix through the cut's time). -/
theorem accept_of_proposesAt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    {W : SA.Blk sp.n (List (FG.Att sp.n))} (hp : p ∈ H (tr.time k)) (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  have hd := hrun.time_nonneg k
  have hb : ∀ m < k + 1, tr.time m ≤ tr.time k := fun _ hm => hrun.time_mono (by omega)
  have hW' : (tr.upTo (tr.time k)).ProposesAt p k W :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hW.1⟩, hW.2.1, hW.2.2⟩
  obtain ⟨ha, hmem, hpost⟩ := Healing.accept_of_proposesAt (hrun.upTo hd)
    (hnc.upTo (tr.time k)) hp hW'
  rw [Trace.upTo_state _ _ hb] at hmem hpost
  exact ⟨((RunTrace.upTo_acceptAt _).mp ha).2, hmem, hpost⟩

/-- The proposer of an honest anchor is honest at its proposal cut. -/
theorem proposer_mem_of_proposesAt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {s : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) {k : Nat}
    (hk : tr.ProposesAt (proposer s) k P) : proposer s ∈ H (tr.time k) := by
  have hsl := honestProposalRun_slot_at hP
  have ht : tr.time k = sp.ts s := by
    rw [hk.2.2, ← hsl, sp.slotTime_eq]; rfl
  refine hrun.antitone ?_ hP.1
  rw [ht]
  exact le_add_of_nonneg_right sp.toParams.hΔ.le

/-- **An honest proposal is held by its proposer**: proposed at a cut `k` where the proposer is
honest, and held after it, at cut `k + 1`, which is at the same time. -/
theorem proposal_held_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.Growing.HonestProposalRun tr H proposer s P) :
    ∃ k, tr.ProposesAt (proposer s) k P ∧ proposer s ∈ H (tr.time k) ∧
      tr.time (k + 1) = tr.time k ∧ P ∈ (tr.state (proposer s) (k + 1)).fg.tree := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun_at hrun hP
  have hm := proposer_mem_of_proposesAt_at hrun hP hk
  obtain ⟨ha, hP', -⟩ := accept_of_proposesAt_at hrun hnc hm hk
  obtain ⟨-, -, -, ht⟩ := accept_next_at hrun hm ha
  exact ⟨k, hk, hm, ht, hP'⟩

/-- The duty head of a proposal is the walk from the anchor after the proposal's unlocking (as the
static `Obligations/HealedC4`'s private helper). -/
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

/-- **No reorg one slot on, finite horizon**, under growing faults. A post-drain operational
proposal `P` of slot `u`, by its proposer honest through `t_u + hold`, is an honest ancestor of the
duty head of every proposal call at `t_{u+1}` of a node honest at that call. -/
theorem UpTo.operational_proposal_below_next_parent_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + Regimes.Growing.hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt y i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (u + 1 : Nat)) :
    Anc (tr.HonestBlocksAt H) P d.head := by
  classical
  have hΔ := sp.toParams.hΔ
  have hσ : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hib : tr.time i ≤ b := by rw [hti, hσ]; linarith
  have hσb : sp.ts u + sp.Δ ≤ b := by linarith
  have hσi : sp.ts u + sp.Δ ≤ tr.time i := by rw [hti, hσ]; linarith
  have hi0 := hp.run.time_nonneg i
  have hmono := hp.run.time_mono
  -- The proposal is held by its proposer, honest at the acceptance.
  obtain ⟨k', -, hpk', hkt', hPx⟩ := proposal_held_at hp.run hp.noColl
    (Healing.Growing.honestProposalRun_of_proposesAt_at hp.run hp.noColl hpH hdesignated
      hactual hPs)
  have hPU : P ∈ tr.HonestBlocksAt H :=
    ⟨_, k' + 1, tr.time k', hp.run.time_nonneg k', fun _ hq => hmono (by omega), hpk', hPx⟩
  have hca := hp.cutZ_lt_reset_at
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
  have hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z q e hz hv hqb hs =>
    hp.operational_unanimous_at hc hpH hdesignated hactual hPs hR (by linarith)
      z q e hz hv hs hqb
  have hRnext : Healing.drainTime sp a ≤ sp.ts (u + 1 : Nat) :=
    hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  -- The static AC base on the prefix through the proposal call, over the validators honest there.
  have hS := Healing.Growing.healthy_base_of_reset_catch_before_at hp hc hi0 hib
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hsub := RunTrace.honestBlocks_upTo_subset hmono (H := H) hi0
  have hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have := hp.faults _ hi0 hib; have := Fin.pos y; omega
  have hci' : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt_of_le _ le_rfl).mpr hci
  have hci'' : (tr.upTo (tr.time i)).projAC.CallAt y i ell := by
    rw [RunTrace.upTo_projAC]; exact hci'
  have hst : (tr.projAC.upTo (tr.time i)).state y i = tr.projAC.state y i :=
    Trace.upTo_state tr.projAC y fun _ hq => hmono hq.le
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hci'
  have hdom : Anc (tr.HonestBlocksAt H) P ell.frame.fcRoot ∨
      P ∈ ell.frame.viableTree ell.frame.tree := by
    refine Healing.Growing.ProposalImpl.held_target_proposal_domain_before_at hp
      (by rw [hkt']; exact hpk') hy hPx hci hcall hd hti hib ?_ ?_ ?_
    · intro hFP
      rw [Compose.frame_of_projAC (hp.run.upTo hi0) hy hci'',
        RunTrace.upTo_state_of_le hmono le_rfl] at hFP
      exact Healing.Growing.unanimous_head_held_at_call_at hp hc hPU hun hgu hRnext hy hci
        (by rw [hti, hσ]; linarith) hib hFP
    · obtain ⟨x, q, m, S, ho, -, -, hqt⟩ := hp.reset_seed_before_slot_at hR
      exact ⟨x, q, m, S, ho, hqt.trans (by rw [hσ]; linarith),
        Or.inr (Healing.Growing.old_origin_below_unanimous_at hp hc hPU hun hgu hRnext hσb ho
          hqt)⟩
    · intro v q m O hqi ho
      have hq : tr.time q ≤ sp.ts u + 6 * sp.Δ := by
        have := hmono hqi.le
        rw [hti, hσ] at this
        linarith
      exact (Healing.Growing.high_origin_compatible_before_update_at hp hc hPU hPs hu hun hgu
        hRnext hTb ho hq).symm
  rcases hdom with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, hstart⟩ := acProposal_start_anchor hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono (hPhiU.trans hsub)
      ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  -- `P` is viable in the frame, so held by the caller, honest there.
  have hPV := hPhiU hV.1
  have hFB := (hPhi.rooted.2 P hV.1).mono hPhiU
  have votes : ∀ z ∈ H (tr.time i), ∀ q e, SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e →
      e.msg.slot = u →
      SA.VoteExtends ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) e.msg P := by
    intro z hz q e hv hslot
    obtain ⟨hqt, hv'⟩ := SA.upTo_voteAt.mp hv
    exact ⟨P, hPV, (hun z q e (hp.run.antitone hqt hz) hv' (hqt.trans hib) hslot).symm, .refl⟩
  have hrestart : ∀ z ∈ H (tr.time i), ∀ q, tr.time q ≤ tr.time i → tr.RestartAt z q →
      tr.time q ≤ sp.ts ((u : Int) - 1) := fun z hz q hqt hrest =>
    Healing.Growing.restart_before_unanimous_slot_at hp hRnext (hp.run.antitone hqt hz) hrest
      (hqt.trans hib)
  have hrs : ∀ q ≤ i, ACTrace.RestartAt (tr.projAC.upTo (tr.time i)) y q →
      tr.time q < sp.ts u := fun q _ hrest => by
    obtain ⟨hqt, hrest'⟩ := ACTrace.upTo_restartAt.mp hrest
    exact (hrestart y hy q hqt (Compose.projAC_restartAt.mp hrest')).trans_lt
      ((SA.ts_lt_iff sp).mpr (by omega))
  have hhalf := SA.honest_voters_half_before hS hgu hσi fun z hz q _ hrest => by
    obtain ⟨hqt, hrest'⟩ := ACTrace.upTo_restartAt.mp hrest
    exact hrestart z hz q hqt (Compose.projAC_restartAt.mp hrest')
  have hhalf' : sp.n ≤ 2 * {z | z ∈ H (tr.time i) ∧ ∃ q e,
      SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = u}.ncard := by
    have hle := Set.ncard_le_ncard (s := {z | z ∈ H (tr.time i) ∧ ∃ q e,
      SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = u ∧
        (tr.projAC.upTo (tr.time i)).time q ≤ sp.ts u + sp.Δ})
      (t := {z | z ∈ H (tr.time i) ∧ ∃ q e,
        SA.VoteAt (tr.projAC.upTo (tr.time i)) z q e ∧ e.msg.slot = u})
      (by rintro z ⟨hz, q, e, hv, hs, _⟩; exact ⟨hz, q, e, hv, hs⟩)
    omega
  have hhigh : SA.HighLocksCompatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i)))
      ((tr.projAC.upTo (tr.time i)).state y i) (tr.time i) u P := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
    obtain ⟨L, hL, hLr, O, hLO, q, hqi, CV, hO⟩ := SA.lock_below_origin hr hy i l hl
    obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
    have hcomp : Compatible ((tr.upTo (tr.time i)).HonestBlocks (H (tr.time i))) O P := by
      rcases hO with ⟨ell', ⟨_, _, ht, _⟩, _⟩ | ⟨ellO, A, hpt, hsl, hsel, hCV⟩
      · have htime := hmono hqi.le
        have hle := (SA.ts_le_iff sp).mpr (show (u : Int) ≤ l.slot by omega)
        change tr.time q = sp.ts l.slot + 6 * sp.Δ at ht
        rw [hti, hσ] at htime
        exfalso
        linarith
      · have hle : l.slot ≤ u := by
          have htime := hmono hqi.le
          have hno := Healing.proposal_no_optimistic_of_run (hp.run.upTo hi0)
            (hp.noColl.upTo _) hf hy hci'' hcall hti hp.stock
          rw [RunTrace.upTo_projAC] at hno
          have hne : l.slot ≠ u + 1 := fun he =>
            hno y hy q hqi O CV (he ▸ ⟨ellO, A, hpt, hsl, hsel, hCV⟩)
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
        refine SA.origin_compatible hU hΦU (SA.CommitteeDict.full sp.n) h34
          (fun _ _ => SA.mem_full _ _) (by simpa only [SA.ncard_inter_full, hp.stock] using hf)
          fun v hv hvH => ?_
        obtain ⟨hvs, q', _, e', hv', rfl⟩ := SA.optimisticPoint_pool_vote hS.run hy hpt hv hvH
        exact votes _ hvH q' e' hv' (by rw [hvs]; omega)
    rcases hcomp with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  refine Anc.mono hsub (SA.batch_proposal hS.run hf hhalf' votes hy hci'
    (SA.proposal_slot hti) (by rw [hst]; exact hd) ⟨hV.1, Or.inl hV⟩ ?_ hhigh hp.stock)
  intro z hz q e hv he
  obtain ⟨H', hH', hHr', hBH⟩ := votes z hz q e hv he
  obtain ⟨Hd, hHd, hHdr, _, hmem, _, hbs⟩ := SA.late_vote_held_of_frame_before hS hy hci' hgu
    (by change _ ≤ tr.time i; rw [hti, hσ]; linarith) le_rfl
    (fun k hki t _ => Compose.ac_deadline_le_of_restarts
      (fun k' hk' hr' => (hrs k' (hk'.trans hki) hr').le) t) hrs hz hv he
    (fun Hd hHd hHdr => by
      rw [hU.1 hHd hH' (hHdr.trans hHr'.symm)]
      exact hFB.trans hBH)
  exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHd, hHdr,
    (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩

/-- The honest proposal `P'` of `s'` is the child of the duty head of its proposal call. -/
theorem honest_proposal_child_at
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {s' : Nat} {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP' : Healing.Growing.HonestProposalRun tr H proposer s' P')
    (hPd : ∀ {i ell} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay},
      tr.projAC.CallAt (proposer s') i ell → ell.call = .proposal →
      (SA.acProposal sp (tr.projAC.state (proposer s') i) ell.frame (tr.time i)).2 =
        some (d, pay) → tr.time i = sp.ts s' → Anc (tr.HonestBlocksAt H) P d.head) :
    Anc (tr.HonestBlocksAt H) P P' := by
  have hBU : P' ∈ tr.HonestBlocksAt H := by
    obtain ⟨k, -, hm, ht, hXm⟩ := proposal_held_at hp.run hp.noColl hP'
    exact ⟨_, k + 1, tr.time k, hp.run.time_nonneg k,
      fun _ hq => hp.run.time_mono (by omega), hm, hXm⟩
  obtain ⟨hy, i, ell, d, pay, hci, hcall, hd, hti, hpar, -⟩ := hP'
  change tr.time i = sp.ts s' at hti
  have h0 := hp.run.time_nonneg i
  have hyi : proposer s' ∈ H (tr.time i) := hp.run.antitone (by
    rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hy
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hp.run.upTo h0) (hp.noColl.upTo _)).localRun
  have hci' : (tr.upTo (tr.time i)).projAC.CallAt (proposer s') i ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hci
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hyi hci'
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ell.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hQU : d.head ∈ tr.HonestBlocksAt H :=
    RunTrace.honestBlocks_upTo_subset hp.run.time_mono h0 (hPhiU hQt)
  exact (hPd hci hcall hd hti).trans (.single ⟨hQU, hBU, hpar⟩)

end Consensus.Goldilocks.Obligations.Growing

end
