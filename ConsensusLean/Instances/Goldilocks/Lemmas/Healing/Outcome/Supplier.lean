module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.UnanimityWalk
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.SignTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.ServedBase
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: post-reset duty suppliers

The source and transport facts are in `Outcome.Foundation`; the proposal pivot is in
`Outcome.Pivot`; the post-drain slot arithmetic and the voter's walk to the proposal, shared by
both unanimity duties, are in `Outcome.UnanimityWalk`. The duty conclusions here may use all
three without an import cycle. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF a : Time}

/-- **The joined duty, unanimity** (the join with RN/RU): under the reset
premises and `Catch(2Δ)`, every honest vote of the slot `u` of an honest ready proposal `P` with
`t_u ≥ R` is `P`. -/
theorem ready_unanimous (hp : ResetPremises tr H K proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : ReadyProposal tr H proposer p k u P)
    (hR : drainTime sp a ≤ sp.ts u) : Unanimous tr H u P := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨s, rfl, hu, hg, hgu, hjoin⟩ :=
    post_drain_slot (cutZ_lt_reset hp.run hp.healthy hp.reset) hR
  obtain ⟨-, i, ellp, d, pay, hci, hcall, hd, hti, hPQ, -, -, hpay, -⟩ :=
    honestProposalRun_of_ready hp.run hp.noColl hP
  rw [← hP.2.1] at hci hd
  change tr.time i = sp.ts (s + 1 : Nat) at hti
  change (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay) at hd
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := reset_pivot hp hc hP hR hci hcall hd hti hPQ
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hP.1 hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; simpa using (AC.slot_arithmetic sp (s + 1)).1 0 (by omega)
  intro y hy j
  induction j using Nat.strong_induction_on generalizing y with
  | _ j ih =>
    intro e hv hes
    obtain ⟨elly, hcy, hey⟩ := hv
    have hcy : AC.CastAt tr.projAC y j elly e := ⟨hcy, hey⟩
    have hE : ∀ x ∈ H, ∀ j' < j, ∀ e', AC.VoteAt tr.projAC x j' e' →
        e'.msg.slot = s + 1 → e'.msg.head = P.root :=
      fun x hx j' hj' e' hv' hs' => ih j' hj' x hx e' hv' hs'
    obtain ⟨hPsi, hPsiU⟩ := AC.frameIn_of_callAt hr hy hcy.1
    have hjt : sp.ts (s + 1 : Nat) ≤ tr.time j := by
      apply (AC.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
      have := (AC.castAt_spec hr hy hcy).2.1
      rw [hes] at this
      exact_mod_cast this.le
    have hgj := hgu.trans hjt
    have hjoj := hjoin.trans hjt
    have hjoi : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i := hti ▸ hjoin
    have hroot := reset_vote_root_below_proposal hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
    have hPy := reset_proposal_frame hp hc hP (by omega) hy hcy hes hgj hjoj
      ((hPsi.F_anc_fcRoot.mono hPsiU).trans hroot)
    have hPv := reset_proposal_viable hp hc hP hR hci hcall hd hti hPQ hy hcy hes hPy hE
    obtain ⟨hstep, hP₀⟩ := reset_stop_at_parent hp hc hP hR hci hcall hd hti hpay hPQ hy
      hcy hes hPv hg (hti ▸ hgu) hgj hQt (hviab _ hDQ .refl)
    obtain ⟨X, hXc, haX, hXend⟩ := hvot y hy j elly e hcy hes hE
    have hspec := AC.castAt_head_of_viable hr hy hcy (hes ▸ ⟨P, hPv⟩)
    rw [hes] at hspec
    exact hspec.trans (congrArg (·.root) (voter_head_eq_proposal hPhi hPsi hd hslot hsD hXc haX
      hXend hPv hstep hP₀ fun B C hXB hDB hBQ hne hCQ hC => reset_suffix_best hp hc hP hci hcall
        hd hti hpay hPQ hy hcy hes hPv hg (hti ▸ hgu) hgj hjoi hjoj hQt hBQ hne
        (hviab _ hDB hBQ) hCQ
        ((haX.mono hPsiU).trans (hXB.mono hPhiU)) hC))

/-- Every bounded honest cast agrees with an actual honest proposal after the reset drain. -/
theorem ResetPremisesUpTo.operational_unanimous {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u) (hub : sp.ts u ≤ b) :
    ∀ y ∈ H, ∀ j e, AC.VoteAt tr.projAC y j e → e.msg.slot = u → tr.time j ≤ b →
      e.msg.head = P.root := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨s, rfl, hu, hg, hgu, hjoin⟩ := post_drain_slot (cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, _⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset) hR
  obtain ⟨_, i, ellp, d, pay, hci, hcall, hd, hti, hPQ, _, _, hpay, _⟩ :=
    honestProposalRun_of_proposesAt hp.run hp.noColl hpH hdesignated hactual hPs
  rw [← hdesignated] at hci hd
  change tr.time i = sp.ts (s + 1 : Nat) at hti
  change (AC.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay) at hd
  have hib : tr.time i ≤ b := hti ▸ hub
  obtain ⟨D, hsD, hDQ, hviab, hvot⟩ := hp.reset_pivot hc hpH hactual hR hci hcall hd hti hib hPQ
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hpH hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ellp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hslot : sp.slot (tr.time i) = s + 1 := by
    rw [hti]; simpa using (AC.slot_arithmetic sp (s + 1)).1 0 (by omega)
  intro y hy j
  induction j using Nat.strong_induction_on generalizing y with
  | _ j ih =>
    intro e hv hes hjb
    obtain ⟨elly, hcy, hey⟩ := hv
    have hcy : AC.CastAt tr.projAC y j elly e := ⟨hcy, hey⟩
    have hE : ∀ x ∈ H, ∀ j' < j, ∀ e', AC.VoteAt tr.projAC x j' e' →
        e'.msg.slot = s + 1 → e'.msg.head = P.root :=
      fun x hx j' hj' e' hv' hs' => ih j' hj' x hx e' hv' hs'
        ((hp.run.time_mono hj'.le).trans hjb)
    obtain ⟨hPsi, hPsiU⟩ := AC.frameIn_of_callAt hr hy hcy.1
    have hjt : sp.ts (s + 1 : Nat) ≤ tr.time j := by
      apply (AC.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2
      have := (AC.castAt_spec hr hy hcy).2.1
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
    have hspec := AC.castAt_head_of_viable hr hy hcy (hes ▸ ⟨P, hPv⟩)
    rw [hes] at hspec
    exact hspec.trans (congrArg (·.root) (voter_head_eq_proposal hPhi hPsi hd hslot hsD hXc haX
      hXend hPv hstep hP₀ fun B C hXB hDB hBQ hne hCQ hC => hp.reset_suffix_best hc hpH
        hdesignated hactual hPs hci hcall hd hti hpay hPQ hy hcy hes hib hjb hPv hg (hti ▸ hgu)
        hgj (hti ▸ hjoin) (hjoin.trans hjt) hQt hBQ hne (hviab _ hDB hBQ) hCQ
        ((haX.mono hPsiU).trans (hXB.mono hPhiU)) hC))

/-- Every awake honest node executes the joined update, whether or not its tick signs. -/
theorem update_call_of_awake {ini}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {u : Nat}
    (hawake : tr.awake y (sp.ts u + 6 * sp.Δ))
    (hjoin : ∀ i, tr.time i = sp.ts u + 6 * sp.Δ →
      AC.joined sp (tr.projAC.state y i) (tr.time i)) :
    ∃ j ell, AC.UpdateAt tr.projAC y j u ell := by
  have hDelta := sp.toParams.hΔ
  have hts : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
  obtain ⟨j, x, fgDue, hg⟩ := hrun.tick_of_awake y hy (sp.ts u + 6 * sp.Δ)
    (by linarith) ⟨4 * (u : Int) + 6, by simp only [ACParams.ts]; ring⟩ hawake
  obtain ⟨hc, ht⟩ := tick_first_cut hg
  exact ⟨j, _, Compose.projAC_callAt.2 hc, rfl, ht, hjoin j ht⟩

/-- Every honest node executes the joined update and immediately following joined to-FG call
at the coverage deadline. This supplies calls, not a nonempty returned report. -/
theorem toFG_call_after_update_of_sign {ini}
    (hrun : GoldilocksRun proposer dg H tr ini)
    (hsign : tr.AllTicksSign proposer dg H)
    {y : Fin sp.n} (hy : y ∈ H) {u : Nat}
    (hawake : tr.awake y (sp.ts u + 6 * sp.Δ))
    (hjoin : ∀ i, tr.time i = sp.ts u + 6 * sp.Δ →
      AC.joined sp (tr.projAC.state y i) (tr.time i)) :
    ∃ j ell ell', AC.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      AC.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  have hDelta := sp.toParams.hΔ
  have hts : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
  obtain ⟨j, x, fgDue, hg⟩ := hrun.tick_of_awake y hy (sp.ts u + 6 * sp.Δ)
    (by linarith) ⟨4 * (u : Int) + 6, by simp only [ACParams.ts]; ring⟩ hawake
  obtain ⟨x, hg⟩ := hsign y hy j _ ⟨x, fgDue, hg⟩
  obtain ⟨ell, ell', hcj, hcall, htj, hcj1, hcall', htj1, hfr⟩ :=
    toFG_second_cut_of_signing_tick hg (not_proposes_update_time y u)
      fun i c hc _ => hrun.cutLaw y hy i c hc
  exact ⟨j, ell, ell', ⟨hcj, hcall, htj, hjoin j htj⟩, hcj1, hcall', htj1, hfr,
    hjoin (j + 1) htj1⟩

/-- Bounded wakefulness and the causal restart bound supply the actual adjacent
update and report call. The slot bound follows from the ready-slot initial margin;
no Catch or service premise is needed to produce these calls. -/
theorem ResetPremisesUpTo.update_toFG_calls {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    (hsign : tr.AllTicksSign proposer dg H)
    {y : Fin sp.n} (hy : y ∈ H) {u : Nat}
    (hu : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u)
    (hub : sp.ts u + 6 * sp.Δ ≤ b) :
    ∃ j ell ell', AC.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      AC.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  have hgu : AC.gbar g ≤ sp.ts u := by
    have hnext := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g)
      ((sp.slot (AC.gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp hnext).le.trans hu
  apply toFG_call_after_update_of_sign hp.run hsign hy
    (hp.awake y hy _ (by linarith [sp.toParams.hΔ]) hub)
  intro i hi
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  unfold AC.joined
  rcases AC.restartTime_state hr hp.run.vstart hy i with h | ⟨r, hri, hrs, h⟩
  · rw [h]; exact bot_le
  · rw [h]
    apply WithBot.coe_le_coe.mpr
    have hrestart := restart_le_before hp hy (Compose.projAC_restartAt.1 hrs)
      ((hp.run.time_mono hri.le).trans (hi ▸ hub))
    have hslot : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
      AC.slot_of_mem sp (u + 1) (by simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
        (by simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ])
    change tr.time r ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
    rw [hi, hslot]
    simpa using hrestart.trans hu

/-- A deepest candidate extending a non-genesis block gives an actual report by this call's
time, including the historical report that suppresses a new return. -/
theorem report_of_deepest_candidate_of_run
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : AC.joined sp (tr.projAC.state y j) (tr.time j))
    {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPg : P.root ≠ sp.genesisRoot)
    (hC : AC.deepest ell.frame (AC.toFGCandidates sp (tr.projAC.state y j)
      ell.frame (tr.time j)) = some C) (hPC : ell.frame.Anc P C) :
    ∃ r ell' R, AC.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc
  by_cases hrep : AC.AncR ell.frame C (tr.projAC.state y j).fgReported
  · obtain ⟨R, hRt, hRr, hCR⟩ := hrep
    have hPR : ell.frame.Anc P R := hPC.trans hCR
    rcases fgReported_origin hr hrun.vstart hy j with hgen | ⟨r, hrj, ell', R', hto, hR'r⟩
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
    change (AC.acToFG sp (tr.projAC.state y j) ell.frame (tr.time j)).2 = some C
    unfold AC.acToFG
    simp only [hjoin, not_true_eq_false, ↓reduceIte, hC, hrep]

/-- A live report candidate compatible with every other candidate supplies an actual report
extending it. An earlier report suppressing this call is included in the conclusion. -/
theorem report_of_compatible_candidate_of_run
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnoColl : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell) (hcall : ell.call = .toFG)
    (hjoin : AC.joined sp (tr.projAC.state y j) (tr.time j))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPc : P ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j))
    (hcompat : ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) C P) :
    ∃ r ell' R, AC.ToFGAt tr.projAC y r ell' R ∧ tr.time r ≤ tr.time j ∧
      Anc (tr.HonestBlocks H) P R := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnoColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc
  have hsub : AC.toFGCandidates sp (tr.projAC.state y j) ell.frame (tr.time j) ⊆
      ell.frame.tree := fun _ h => h.1.1
  obtain ⟨C, hC⟩ := AC.exists_deepest hPhi hsub ⟨P, hPc⟩
  obtain ⟨hCc, hmax⟩ := AC.deepest_mem hC
  apply report_of_deepest_candidate_of_run hrun hnoColl hy hc hcall hjoin hPg hC
  rcases hcompat C hCc with hCP | hPC
  · by_cases he : P = C
    · exact he ▸ .refl
    have hCPf := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hCc) hCP (hsub hPc)
    have hlt := AC.depth_lt_of_anc hPhi hCPf (Ne.symm he) (hsub hPc)
    rcases hmax P hPc he with h | ⟨h, _⟩ <;> omega
  · exact AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU (hsub hPc) hPC (hsub hCc)

/-- Finite report coverage. The unproduced duties are explicit: a deadline cut with
compatible finality for each reader, and a below-finality actual-report producer.
Neither duty assumes wakefulness after `b`; historical reports have no lower time bound. -/
theorem ResetPremisesUpTo.report_cover_of_compatible_floors {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hcuts : ∀ z ∈ H, ∃ j, tr.time j ≤ sp.ts u + 6 * sp.Δ ∧
      Compatible (tr.HonestBlocks H) (tr.state z j).fg.F P ∧
      (Anc (tr.HonestBlocks H) (tr.state z j).fg.F P →
        ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
          Anc (tr.HonestBlocks H) P C)) :
    (∀ z ∈ H, ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  by_cases hall : ∀ z ∈ H, ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧
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
    (hp : ResetPremises tr H K proposer dg g ΔF a)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hcuts : ∀ z ∈ H, ∃ j, tr.time j ≤ sp.ts u + 6 * sp.Δ ∧
      Compatible (tr.HonestBlocks H) (tr.state z j).fg.F P ∧
      (Anc (tr.HonestBlocks H) (tr.state z j).fg.F P →
        ∃ r ℓ C, AC.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
          Anc (tr.HonestBlocks H) P C)) :
    (∀ z ∈ H, ∃ r ℓ C, AC.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C) ∨
    ∃ z ∈ H, ∃ r ℓ C, AC.ToFGAt tr.projAC z r ℓ C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h :=
  (hp.toUpTo tr H le_rfl).report_cover_of_compatible_floors hcuts

end Consensus.Goldilocks.Healing

end
