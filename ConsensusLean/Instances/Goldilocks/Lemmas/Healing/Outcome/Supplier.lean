module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.UnanimityWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: post-reset duty suppliers

The source and transport facts are in `Outcome.Foundation`; the proposal pivot is in
`Outcome.Pivot`; the post-drain slot arithmetic and the voter's walk to the proposal, shared by
both unanimity duties, are in `Outcome.UnanimityWalk`. The duty conclusions here may use all
three without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **The joined duty, unanimity** (the join with RN/RU): under the reset
premises and `Catch(2Δ)`, every honest vote of the slot `u` of an honest ready proposal `P` with
`t_u ≥ R` is `P`. -/
theorem ready_unanimous (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) : Unanimous tr H u P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨s, rfl, hu, hg, hgu, -⟩ := post_drain_slot (cutZ_lt_reset hp.run hp.healthy hp.reset) hR
  obtain ⟨-, i, ellp, d, pay, hci, hcall, hd, hti, hPQ, -, -, hpay, -⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hci hd
  change tr.time i = sp.ts (s + 1 : Nat) at hti
  change (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay) at hd
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := reset_pivot hp hc hP hR hci hcall hd hti hPQ
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hP.1 hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  intro y hy j
  induction j using Nat.strong_induction_on generalizing y with
  | _ j ih =>
    intro e hv hes
    obtain ⟨elly, hcy, hey⟩ := hv
    have hcy : SA.CastAt tr.projAC y j elly e := ⟨hcy, hey⟩
    have hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
        e'.msg.slot = s + 1 → e'.msg.head = P.root :=
      fun x hx j' hj' e' hv' hs' => ih j' hj' x hx e' hv' hs'
    obtain ⟨hPsi, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
    have hjt : sp.ts (s + 1 : Nat) ≤ tr.time j := by
      apply (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
      have := (SA.castAt_spec hr hy hcy).2.1
      rw [hes] at this
      exact_mod_cast this.le
    have hgj := hgu.trans hjt
    have hroot := reset_vote_root_below_proposal hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
    have hPy := reset_proposal_frame hp hc hP (by omega) hy hcy hes hgj
      ((hPsi.F_anc_fcRoot.mono hPsiU).trans hroot)
    have hPv := reset_proposal_viable hp hc hP hR hci hcall hd hti hPQ hy hcy hes hPy hE
    obtain ⟨hstep, hP₀⟩ := reset_stop_at_parent hp hc hP hR hci hcall hd hti hpay hPQ hy
      hcy hes hPv hg (hti ▸ hgu) hgj hQt (hviab _ hDQ .refl)
    obtain ⟨X, hXc, haX, hXend⟩ := hvot y hy j elly e hcy hes hE
    have hspec := SA.castAt_head_of_viable hr hy hcy (hes ▸ ⟨P, hPv⟩)
    rw [hes] at hspec
    exact hspec.trans (congrArg (·.root) (voter_head_eq_proposal hPhi hPsi hd hslot hsD hXc haX
      hXend hPv hstep hP₀ fun B C hXB hDB hBQ hne hCQ hC => reset_suffix_best hp hc hP hci hcall
        hd hti hpay hPQ hy hcy hes hPv hg (hti ▸ hgu) hgj hQt hBQ hne (hviab _ hDB hBQ) hCQ
        ((haX.mono hPsiU).trans (hXB.mono hPhiU)) hC))

/-- Every bounded honest cast agrees with an actual honest proposal after the reset drain. -/
theorem ResetPremisesUpTo.operational_unanimous {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u) (hub : sp.ts u ≤ b) :
    ∀ y ∈ H, ∀ j e, SA.VoteAt tr.projAC y j e → e.msg.slot = u → tr.time j ≤ b →
      e.msg.head = P.root := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨s, rfl, hu, hg, hgu, hjoin⟩ := post_drain_slot (cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, _⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset) hR
  obtain ⟨_, i, ellp, d, pay, hci, hcall, hd, hti, hPQ, _, _, hpay, _⟩ :=
    honestProposalRun_of_proposesAt hp.run hp.noColl hpH hdesignated hactual hPs
  rw [← hdesignated] at hci hd
  change tr.time i = sp.ts (s + 1 : Nat) at hti
  change (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay) at hd
  have hib : tr.time i ≤ b := hti ▸ hub
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := hp.reset_pivot hc hpH hactual hR hci hcall hd hti hib hPQ
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; simpa using (SA.slot_arithmetic sp (s + 1)).1 0 (by omega)
  intro y hy j
  induction j using Nat.strong_induction_on generalizing y with
  | _ j ih =>
    intro e hv hes hjb
    obtain ⟨elly, hcy, hey⟩ := hv
    have hcy : SA.CastAt tr.projAC y j elly e := ⟨hcy, hey⟩
    have hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
        e'.msg.slot = s + 1 → e'.msg.head = P.root :=
      fun x hx j' hj' e' hv' hs' => ih j' hj' x hx e' hv' hs'
        ((hp.run.time_mono hj'.le).trans hjb)
    obtain ⟨hPsi, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
    have hjt : sp.ts (s + 1 : Nat) ≤ tr.time j := by
      apply (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
      have := (SA.castAt_spec hr hy hcy).2.1
      rw [hes] at this
      exact_mod_cast this.le
    have hgj := hgu.trans hjt
    have hroot := hp.reset_vote_root_below_proposal hc hpH hactual hR hci hcall hd hti hib
      hPQ hy hcy hes hjb
    have hPy := hp.reset_proposal_frame hc hpH hdesignated hactual hPs (by omega) hy hcy hes
      hjb hgj (hjoin.trans hjt) ((hPsi.F_anc_fcRoot.mono hPsiU).trans hroot)
    have hPv := hp.reset_proposal_viable hc hpH hactual hPs hR hci hcall hd hti hib hPQ
      hy hcy hes hjb hPy
    obtain ⟨hstep, hP₀⟩ := hp.reset_stop_at_parent hc hpH hdesignated hactual hPs hR
      hci hcall hd hti hpay hPQ hy hcy hes hib hjb hPv hg (hti ▸ hgu) hgj
      (hti ▸ hjoin) (hjoin.trans hjt) hQt (hviab _ hDQ .refl)
    obtain ⟨X, hXc, haX, hXend⟩ := hvot y hy j elly e hcy hes hjb hE
    have hspec := SA.castAt_head_of_viable hr hy hcy (hes ▸ ⟨P, hPv⟩)
    rw [hes] at hspec
    exact hspec.trans (congrArg (·.root) (voter_head_eq_proposal hPhi hPsi hd hslot hsD hXc haX
      hXend hPv hstep hP₀ fun B C hXB hDB hBQ hne hCQ hC => hp.reset_suffix_best hc hpH
        hdesignated hactual hPs hci hcall hd hti hpay hPQ hy hcy hes hib hjb hPv hg (hti ▸ hgu)
        hgj (hti ▸ hjoin) (hjoin.trans hjt) hQt hBQ hne (hviab _ hDB hBQ) hCQ
        ((haX.mono hPsiU).trans (hXB.mono hPhiU)) hC))

/-- Every honest node executes the joined update and immediately following joined to-FG call
at the coverage deadline. This supplies calls, not a nonempty returned report. -/
theorem update_toFG_calls_of_awake
    (hrun : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {u : Nat}
    (hawake : tr.awake y (sp.ts u + 6 * sp.Δ))
    (hjoin : ∀ i, tr.time i = sp.ts u + 6 * sp.Δ →
      SA.joined sp (tr.projAC.state y i) (tr.time i)) :
    ∃ j ell ell', SA.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  have hDelta := sp.toParams.hΔ
  have hts : 0 ≤ sp.ts u := by simp only [SAParams.ts]; positivity
  obtain ⟨j, x, hg⟩ := hrun.tick_of_awake y hy (sp.ts u + 6 * sp.Δ)
    (by linarith) ⟨4 * (u : Int) + 6, by simp only [SAParams.ts]; ring⟩ hawake
  have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
    SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith)
      (by simp only [SAParams.ts]; push_cast; linarith)
  have hnP : ¬ Node.Proposes proposer y (sp.ts u + 6 * sp.Δ) := by
    rintro ⟨-, h, -⟩
    rw [show sp.toParams.slotOf (sp.ts u + 6 * sp.Δ) = u + 1 from hslot,
      sp.slotTime_eq] at h
    simp only [SAParams.ts] at h
    push_cast at h
    linarith
  obtain ⟨hcj, htj⟩ := tick_first_cut hg
  have h1 : (Node.exec proposer dg y (tr.state y j) (sp.ts u + 6 * sp.Δ) (.tick x)).2[1]? =
      some (Node.acToFG
        (Node.tickStep proposer dg y (tr.state y j) (sp.ts u + 6 * sp.Δ) x .acTick).1
        (sp.ts u + 6 * sp.Δ)).2.1 := by
    change (Node.onTick proposer dg y (tr.state y j) (sp.ts u + 6 * sp.Δ) x).2[1]? = _
    rw [onTick_eq]
    simp only [Node.tickStep, hnP, ↓reduceIte]
    split <;> simp [Node.acToFG, Node.acCall]
  obtain ⟨hk', hlabel⟩ := List.getElem?_eq_some_iff.1 h1
  obtain ⟨hn, ht, -, -, hl⟩ := hg.2.1 1 hk'
  obtain ⟨ell', hcj1, hcall', htj1⟩ : ∃ ell' : ACLabel (goldilocksNode sp ro),
      tr.CallAt y (j + 1) (.ac ell') ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ :=
    ⟨_, ⟨hn, hl.trans (congrArg some hlabel)⟩, rfl, ht⟩
  obtain ⟨ell, hcjAC, hcall⟩ : ∃ ell : ACLabel (goldilocksNode sp ro),
      tr.projAC.CallAt y j ell ∧ ell.call = .tick :=
    ⟨_, Compose.projAC_callAt.2 hcj, rfl⟩
  refine ⟨j, ell, ell', ⟨hcjAC, hcall, htj, hjoin j htj⟩,
    Compose.projAC_callAt.2 hcj1, hcall', htj1, ?_, hjoin (j + 1) htj1⟩
  rw [(hrun.cutLaw y hy (j + 1) _ hcj1).1,
    Compose.frame_of_projAC hrun hy hcjAC, tr.state_succ_of_call hcj]
  unfold Node.frame
  rw [(hrun.cutLaw y hy j _ hcj).2.2.1]

/-- Bounded wakefulness and the causal restart bound supply the actual adjacent
update and report call. The slot bound follows from the ready-slot initial margin;
no Catch or service premise is needed to produce these calls. -/
theorem ResetPremisesUpTo.update_toFG_calls {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {u : Nat}
    (hu : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u)
    (hub : sp.ts u + 6 * sp.Δ ≤ b) :
    ∃ j ell ell', SA.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  have hgu : SA.gbar g ≤ sp.ts u := by
    have hnext := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
      ((sp.slot (SA.gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp hnext).le.trans hu
  apply update_toFG_calls_of_awake hp.run hy
    (hp.awake y hy _ (by linarith [sp.toParams.hΔ]) hub)
  intro i hi
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  unfold SA.joined
  rcases SA.restartTime_state hr hy i with h | ⟨r, hri, hrs, h⟩
  · rw [h]; exact bot_le
  · rw [h]
    apply WithBot.coe_le_coe.mpr
    have hrestart := restart_le_before hp hy (Compose.projAC_restartAt.1 hrs)
      ((hp.run.time_mono hri.le).trans (hi ▸ hub))
    have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
      SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
        (by simp only [SAParams.ts]; push_cast; linarith [sp.toParams.hΔ])
    change tr.time r ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
    rw [hi, hslot]
    simpa using hrestart.trans hu

/-- A bounded reset seed reaches a read through an earlier actual update, provided
the read's finalized tip is below it. The next-event clock need not be in the horizon. -/
theorem ResetPremisesUpTo.reset_seed_held_at_read {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {y : Fin sp.n} (hy : y ∈ H) {n u : Nat} {t : Time}
    (hrp : Regimes.ReadPoint tr n t) (htb : t ≤ b)
    (hdrain : drainTime sp a ≤ sp.ts u) (hgst : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hbefore : sp.ts u + 6 * sp.Δ < t) :
    ∃ v r l S, HighOrigin tr H g v r l S ∧ tr.time r ≤ b ∧ l < u ∧
      tr.time r < sp.ts u ∧
      (Anc (tr.HonestBlocks H) (tr.state y n).fg.F S → S ∈ (tr.state y n).fg.tree) := by
  obtain ⟨v, r, l, S, hS, hrb, hlu, hru⟩ := hp.reset_seed_before_slot hdrain
  have hΔ := sp.toParams.hΔ
  have hslot := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) (sp.slot (SA.gbar g))).mpr
    (by omega)
  have hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := by
    simp only [SAParams.ts] at hslot hgst ⊢
    push_cast
    linarith
  obtain ⟨j, ell, _, hup, _⟩ := hp.update_toFG_calls hy hjoin (hbefore.le.trans htb)
  have hjt : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjn : j ≤ n := by
    by_contra h
    have := (hrp.2.trans (hp.run.time_mono (by omega : n ≤ j))).trans_eq hjt
    linarith
  refine ⟨v, r, l, S, hS, hrb, hlu, hru, fun hF => ?_⟩
  obtain ⟨ellS, _, _, hcallS, _, _, _, hSm, _⟩ := hp.highOrigin_mem hS
  have hgrow := Compose.fg_grows hp.run hy hjn
  have hFj : Anc (tr.HonestBlocks H) ell.frame.F S := by
    rw [Compose.frame_of_projAC hp.run hy hup.1]
    exact hgrow.2.trans hF
  have hheld := hp.reset_frame_relay hc hS.1 hy hcallS hup.1 hSm
    (hjt ▸ hbefore.le.trans htb) (by rw [hjt]; linarith)
    (by rw [hjt]; linarith) (by rw [hjt]; linarith) hFj
  exact hgrow.1 (hp.frame_tree_subset hy hup.1 hheld)

/-- One reset seed is available at every bounded honest call after the relay delay,
whenever that call's finalized tip is below it. The seed is chosen before the calls. -/
theorem ResetPremisesUpTo.reset_seed_held_at_call {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ)) :
    ∃ v r l S, HighOrigin tr H g v r l S ∧ tr.time r ≤ a ∧ tr.time r ≤ b ∧
      ∀ y ∈ H, ∀ c (ell : ACLabel (goldilocksNode sp ro)), tr.projAC.CallAt y c ell →
        a + sp.Δ ≤ tr.time c → tr.time c ≤ b →
        Anc (tr.HonestBlocks H) ell.frame.F S → S ∈ ell.frame.tree := by
  obtain ⟨⟨v, hv, k, att, hs, hh, hka⟩, _⟩ := hp.reset
  obtain ⟨r, hrk, l, S, hS, _⟩ := hp.high_row_source hv hs hh.ge
  have hra : tr.time r ≤ a := (hp.run.time_mono hrk.le).trans hka.le
  refine ⟨v, r, l, S, hS, hra, hra.trans hp.reset_le, ?_⟩
  intro y hy c ell hcall hac hcb hF
  obtain ⟨ellS, _, _, hcallS, _, _, _, hSm, _⟩ := hp.highOrigin_mem hS
  have hcut : cutZ sp.toParams g < a := cutZ_lt_reset_of_snapshot hp.run
    (let ⟨q, hq, _⟩ := hp.snapshot; ⟨q, hq⟩) hp.reset
  have hnext : SA.gbar g < sp.ts (sp.slot (SA.gbar g) + 1 : Nat) := by
    exact not_le.mp ((SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g)
      ((sp.slot (SA.gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega))
  rw [cutZ_eq] at hcut
  have hΔ := sp.toParams.hΔ
  apply hp.reset_frame_relay hc hv hy hcallS hcall hSm hcb ?_ ?_ (by linarith) hF
  · simp only [SAParams.ts] at hcut hnext
    push_cast at hcut hnext
    linarith
  · simp only [SAParams.ts] at hcut ⊢
    push_cast at hcut ⊢
    linarith

/-- A deepest candidate extending a non-genesis block gives an actual report by this call's
time, including the historical report that suppresses a new return. -/
theorem report_of_deepest_candidate_of_run
    (hrun : GoldilocksRun proposer dg H tr) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : SA.joined sp (tr.projAC.state y j) (tr.time j))
    {P C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPg : P.root ≠ sp.genesisRoot)
    (hC : SA.deepest ell.frame (SA.toFGCandidates sp (tr.projAC.state y j)
      ell.frame (tr.time j)) = some C) (hPC : ell.frame.Anc P C) :
    ∃ r ell' R, SA.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  by_cases hrep : SA.AncR ell.frame C (tr.projAC.state y j).fgReported
  · obtain ⟨R, hRt, hRr, hCR⟩ := hrep
    have hPR : ell.frame.Anc P R := hPC.trans hCR
    rcases fgReported_origin hr hy j with hgen | ⟨r, hrj, ell', R', hto, hR'r⟩
    · have hG := Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hy j)
      have he := hr.coherent.1 (hPhiU hRt) ⟨y, hy, j, hG⟩ (hRr.trans hgen)
      rw [he] at hPR
      rcases Relation.ReflTransGen.cases_tail hPR with heq | ⟨Y, _, hY⟩
      · exact False.elim (hPg (by rw [← heq]; rfl))
      · exact False.elim (Option.some_ne_none _ (hY.2.2.symm.trans rfl))
    have hR't := toFG_mem_tree hrun hy hto
    obtain rfl : R' = R := hr.coherent.1 ⟨y, hy, r, hR't⟩ (hPhiU hRt)
      (hR'r.trans hRr.symm)
    exact ⟨r, ell', R', hto, hrun.time_mono hrj.le, hPR.mono hPhiU⟩
  · refine ⟨j, ell, C, ⟨hc, hcall, ?_⟩, le_rfl, hPC.mono hPhiU⟩
    change (SA.acToFG sp (tr.projAC.state y j) ell.frame (tr.time j)).2 = some C
    unfold SA.acToFG
    simp only [hjoin, not_true_eq_false, ↓reduceIte, hC, hrep]

/-- A live report candidate compatible with every other candidate supplies an actual report
extending it. An earlier report suppressing this call is included in the conclusion. -/
theorem report_of_compatible_candidate_of_run
    (hrun : GoldilocksRun proposer dg H tr) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : SA.joined sp (tr.projAC.state y j) (tr.time j))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPc : P ∈ SA.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j))
    (hcompat : ∀ C ∈ SA.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) C P) :
    ∃ r ell' R, SA.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
  have hsub : SA.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j) ⊆
      ell.frame.tree := fun _ h => h.1.1
  obtain ⟨C, hC⟩ := SA.exists_deepest hPhi hsub ⟨P, hPc⟩
  obtain ⟨hCc, hmax⟩ := SA.deepest_mem hC
  apply report_of_deepest_candidate_of_run hrun hnoColl hy hc hcall hjoin hPg hC
  rcases hcompat C hCc with hCP | hPC
  · by_cases he : P = C
    · exact he ▸ .refl
    have hCPf := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hCc) hCP (hsub hPc)
    have hlt := SA.depth_lt_of_anc hPhi hCPf (Ne.symm he) (hsub hPc)
    rcases hmax P hPc he with h | ⟨h, _⟩ <;> omega
  · exact SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hPc) hPC (hsub hCc)

/-- Every sufficiently clean older fast or slow source is below the unanimous proposal.
The source need not precede the chosen vote cut: clean-source transfer budgets both times. -/
theorem clean_source_below_ready
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s < u) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := healthy_base_of_reset_catch hp hc
  obtain ⟨j, e, hv, hes⟩ := SA.honest_votes_in_slot hS hgu p hP.1
  obtain ⟨ell, hcast⟩ := hv
  obtain ⟨Hd, hHd, hHdr, hBH⟩ := clean_source_votes_before hp hc
    (max (tr.time r) (tr.time j)) hx horig hs (le_max_left _ _) j (le_max_right _ _)
    p hP.1 ell e hcast (hes ▸ hsu)
  have hhead := ready_unanimous hp hc hP hR p hP.1 j e ⟨ell, hcast⟩ hes
  have hPU := (SA.frameIn_of_callAt hS.run.localRun hP.1 hcast.1).2
  obtain ⟨X, hXt, hXr, -⟩ := (Compose.cast_head_fcRoot hS.run.localRun hP.1 hcast).1
  have hXP : X = P := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ja, -, hacc, -⟩ :=
      honestProposalRun_of_ready hp.run hp.noColl hP
    rw [← hP.2.1] at hacc
    obtain ⟨ellp, hcp, hblock⟩ := hacc
    have hPm := (SA.accept_new sp hS.run.localRun hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
    exact hS.run.localRun.coherent.1 (hPU hXt)
      ((SA.frameIn_of_callAt hS.run.localRun hP.1 hcp).2 hPm) (hXr.trans hhead)
  have hDP : Hd = P := hS.run.localRun.coherent.1 hHd (hXP ▸ hPU hXt)
    (hHdr.trans hhead)
  exact hDP ▸ hBH

/-- A fast or slow lock source of the proposal's own label is below the unanimous proposal.
This uses an actual counted honest vote, not the fast lock sought at a later update. -/
theorem same_slot_source_below_ready
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {r : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r u B CV) ∨ SA.SlowLockAt tr.projAC x r u B) :
    Anc (tr.HonestBlocks H) B P := by
  have hS := healthy_base_of_reset_catch hp hc
  have hU := hS.run.localRun.coherent
  obtain ⟨-, -, _, _, _, _, _, _, _, _, _, _, _, ja, _, hacc, _⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (SA.accept_new sp hS.run.localRun hP.1 ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hPU := (SA.frameIn_of_callAt hS.run.localRun hP.1 hcp).2 hPm
  have below : ∀ z ∈ H, ∀ j e, SA.VoteAt tr.projAC z j e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B → Anc (tr.HonestBlocks H) B P := by
    rintro z hz j e hv hes ⟨Hd, hHd, hHdr, hBH⟩
    have he := hU.1 hHd hPU (hHdr.trans (ready_unanimous hp hc hP hR z hz j e hv hes))
    exact he ▸ hBH
  rcases horig with ⟨CV, hf⟩ | ⟨ell, C, hupd, hC, hD⟩
  · obtain ⟨z, hz, j, e, hv, hes, hB⟩ :=
      SA.fastLock_honest_vote hS.run hS.two_faulty_lt hx hf hp.stock
    exact below z hz j e hv hes hB
  · obtain ⟨z, hz, j, e, hv, hes, Hd, hHd, hHdr, hCH⟩ := SA.result_extended hS hgu hx
      hupd.1 (by rw [hupd.2.2.1]; linarith [sp.toParams.hΔ]) hC
    have hPhiU := (SA.frameIn_of_callAt hS.run.localRun hx hupd.1).2
    exact below z hz j e hv hes
      ⟨Hd, hHd, hHdr, ((SA.deepest_mem hD).1.1.2.2.mono hPhiU).trans hCH⟩

/-- At any post-drain call, the viable image of a stored live lock of an older label lies
below the ready proposal. This covers both slow locks and fast locks. -/
theorem ready_old_lock_below
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : drainTime sp a ≤ tr.time j)
    {l : SA.Lock} (hl : l ∈ (tr.projAC.state y j).locks) (hlu : l.slot < u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ell.frame.tree)
    (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) P := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcall
  have hs := drain_stored_lock_label ht hlive
  obtain ⟨r, _, B, horig, X, hX, hXr, hXB⟩ : ∃ r < j, ∃ B,
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot B CV) ∨ SA.SlowLockAt tr.projAC y r l.slot B) ∧
      ∃ X ∈ tr.HonestBlocks H, X.root = l.block ∧ Anc (tr.HonestBlocks H) X B := by
    cases hf : l.fast with
    | false =>
      obtain ⟨r, hrj, B, hslow, hX⟩ := SA.slow_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, B, Or.inr hslow, hX⟩
    | true =>
      obtain ⟨r, hrj, B, CV, hfast, hX⟩ := SA.fast_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, B, Or.inl ⟨CV, hfast⟩, hX⟩
  have hXL : X = L := hr.coherent.1 hX (hPhiU hL) (hXr.trans hLr.symm)
  rw [hXL] at hXB
  exact ((SA.anc_viableAncestor ell.frame L).mono hPhiU).trans
    (hXB.trans (clean_source_below_ready hp hc hP hR hgu hy horig hs hlu))

/-- At any honest call after the drain and through the deadline, old and same-slot locks
are below the ready proposal. Next-slot optimistic compatibility remains explicit. -/
theorem ready_call_locks_compatible
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell)
    (hafter : drainTime sp a ≤ tr.time j) (hbefore : tr.time j ≤ sp.ts u + 6 * sp.Δ)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocks H) B P) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcall
  have hDelta := sp.toParams.hΔ
  rintro L ⟨hLt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hLr⟩
  have he : L = ell.frame.viableAncestor B := hPhi.coherent.1 hLt
    (SA.viableAncestor_anc hPhi hB).1 hLr.symm
  rw [he]
  by_cases hlu : l.slot < u
  · exact Or.inl (ready_old_lock_below hp hc hP hR hgu hy hcall
      hafter hl hlu (le_trans hlive ((SA.locksWF_state hr hy j).cap hl)) hB hBr)
  obtain ⟨r, hrj, D, horig, X, hX, hXr, hXD⟩ : ∃ r < j, ∃ D,
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨ SA.SlowLockAt tr.projAC y r l.slot D) ∧
      ∃ X ∈ tr.HonestBlocks H, X.root = l.block ∧ Anc (tr.HonestBlocks H) X D := by
    cases hf : l.fast with
    | false =>
      obtain ⟨r, hrj, D, hs, hX⟩ := SA.slow_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, D, Or.inr hs, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hf, hX⟩ := SA.fast_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hf⟩, hX⟩
  have hXB : X = B := hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)
  rw [hXB] at hXD
  have hLD := ((SA.anc_viableAncestor ell.frame B).mono hPhiU).trans hXD
  have hrt : tr.time r ≤ sp.ts u + 6 * sp.Δ := (hp.run.time_mono hrj.le).trans hbefore
  have hDP : Compatible (tr.HonestBlocks H) D P := by
    by_cases heq : l.slot = u
    · exact Or.inl (same_slot_source_below_ready hp hc hP hR hgu hy (heq ▸ horig))
    have hgt : u < l.slot := by omega
    rcases horig with ⟨CV, ⟨ellr, C, hupd, _⟩ | hop⟩ | ⟨ellr, C, hupd, _⟩
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hts := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith
    · have hsl : sp.slot (tr.time r) = l.slot := hop.choose_spec.choose_spec.2.1
      have hbound : l.slot ≤ u + 1 := by
        have hmono := SA.slot_mono sp (hr.time_nonneg r) hrt
        change sp.slot (tr.time r) ≤ sp.slot (sp.ts u + 6 * sp.Δ) at hmono
        have hs : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
          SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith)
            (by simp only [SAParams.ts]; push_cast; linarith)
        rw [hsl, hs] at hmono
        exact hmono
      exact hnext r hrj D CV (show l.slot = u + 1 by omega ▸ hop)
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hts := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith
  rcases hDP with hDP | hPD
  · exact Or.inl (hLD.trans hDP)
  · exact SA.anc_total hr.coherent hLD hPD

/-- The update is a deadline call, so the general live-lock comparison applies. -/
theorem ready_update_locks_compatible
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y j u ell)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocks H) B P) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P := by
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
  exact ready_call_locks_compatible hp hc hP hR hgu hy hu.1
    (by rw [ht]; linarith [sp.toParams.hΔ]) (by rw [ht]) hnext

/-- With the frame and next-slot optimism obligations discharged, the actual update confirms
the ready proposal without veto and selects that exact block for its fast lock. -/
theorem ready_update_selection
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocks H) B P) :
    SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P := by
  have hS := healthy_base_of_reset_catch hp hc
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hS.run.localRun hy hu.1
  have hPg : P.root ≠ sp.genesisRoot := by
    intro hgen
    have hG := Store.genesis_mem (Compose.fg_reachable hp.run.toLocalRun hy j)
    have he := hS.run.localRun.coherent.1 (hPhiU hPt) ⟨y, hy, j, hG⟩ hgen
    have hPs := hP.2.2.2.2.1
    rw [he] at hPs
    simp only [Params.genesisBlock] at hPs
    have hDelta := sp.toParams.hΔ
    have hg0 := SA.gbar_nonneg g
    have hts : sp.ts u = 0 := by rw [← hPs]; simp [SAParams.ts]
    linarith
  obtain ⟨hconf, hnv, hfast, -⟩ := SA.first_update_post hS hgu
    (ready_unanimous hp hc hP hR) hy hu.1 hu.2.1 hu.2.2.1 hPt
    (ready_update_locks_compatible hp hc hP hR hgu hy hu hnext)
  exact ⟨hconf, hnv, SA.fastSelect_eq_result hPhi hPt hPg hfast⟩

/-- Finite report coverage. The unproduced duties are explicit: a deadline cut with
compatible finality for each reader, and a below-finality actual-report producer.
Neither duty assumes wakefulness after `b`; historical reports have no lower time bound. -/
theorem ResetPremisesUpTo.report_cover_of_compatible_floors {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcuts : ∀ z ∈ H, ∃ j, tr.time j ≤ sp.ts u + 6 * sp.Δ ∧
      Compatible (tr.HonestBlocks H) (tr.state z j).fg.F P ∧
      (Anc (tr.HonestBlocks H) (tr.state z j).fg.F P →
        ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
          Anc (tr.HonestBlocks H) P C)) :
    (∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  by_cases hall : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C
  · exact Or.inl hall
  push Not at hall
  obtain ⟨z, hz, hn⟩ := hall
  obtain ⟨j, hj, hcompat, hbelow⟩ := hcuts z hz
  rcases hp.finality_below_or_higher_report hz hcompat with
    hF | ⟨v, hv, r, ell, C, hrj, hto, hPC, hlt⟩
  · obtain ⟨r, ell, C, hto, ht, hPC⟩ := hbelow hF
    exact False.elim (hn r ell C hto ht hPC)
  · exact Or.inr ⟨v, hv, r, ell, C, hto, (hp.run.time_mono hrj.le).trans hj, hPC, hlt⟩

/-- Conditional report coverage at actual cuts bounded by the update deadline.
Compatibility discharges the strict-descendant branch using an earlier actual report;
the below-floor branch still needs an actual-report producer (selection alone is not one).
The cuts may be updates or first-loss post-states; no lower bound on report time is imposed. -/
theorem report_cover_of_compatible_floors
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcuts : ∀ z ∈ H, ∃ j, tr.time j ≤ sp.ts u + 6 * sp.Δ ∧
      Compatible (tr.HonestBlocks H) (tr.state z j).fg.F P ∧
      (Anc (tr.HonestBlocks H) (tr.state z j).fg.F P →
        ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
          Anc (tr.HonestBlocks H) P C)) :
    (∀ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h :=
  (hp.toUpTo tr H le_rfl).report_cover_of_compatible_floors hcuts

end Consensus.Goldilocks.Healing

end
