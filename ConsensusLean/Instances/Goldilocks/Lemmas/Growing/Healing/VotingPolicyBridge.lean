module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowSupply
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Frame.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.ClientSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.RecordsCore

public section

/-! # Report ancestry, signing duties, and publication for voting policies -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- A new report extends the still-recorded earlier report in a sleepy invariant window.
The earlier source need not still be in the AC frame: if it is above the new source, the
new source's membership forces it into that frame and the suppression rule applies. -/
theorem report_extends_recorded_report_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hsleepy : SleepyInvariantUpTo tr H b)
    {y : Fin sp.n} {i j : Nat} (hij : i ≤ j) (hy : y ∈ H (tr.time j)) (hjb : tr.time j ≤ b)
    {old new : SA.Blk sp.n (List (FG.Att sp.n))}
    {ell₀ ell : ACLabel (goldilocksNode sp ro)}
    (hOld : SA.ToFGAt tr.projAC y i ell₀ old) (hNew : SA.ToFGAt tr.projAC y j ell new)
    (hrecord : (tr.projAC.state y j).fgReported = old.root) :
    Anc (tr.HonestBlocksAt H) old new := by
  have hyi := hrun.antitone (hrun.time_mono hij) hy
  have hbi : ∀ k < i, tr.time k ≤ b := fun k hk =>
    (hrun.time_mono (hk.le.trans hij)).trans hjb
  have ht := hrun.time_nonneg j
  have hbj : ∀ k < j, tr.time k ≤ tr.time j := fun k hk => hrun.time_mono hk.le
  obtain ⟨hΦ₀, hΦ₀U⟩ := frameIn_at hrun hnc hyi hOld.1
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hNew.1
  have hc₀ := (SA.toFG_candidate hOld.2.2).1.1
  have hc := (SA.toFG_candidate hNew.2.2).1.1
  rcases (hsleepy.sources y i hyi hbi _ _ hOld).compatible hrun hnc
    hsleepy.origins_compatible (hΦ₀U hc₀) (hΦU hc)
    (hsleepy.sources y j hy (fun k hk => (hbj k hk).trans hjb) _ _ hNew) with forward | backward
  · exact forward
  exfalso
  have hf₀ := frame_of_projAC_at hrun hyi hOld.1
  have hf := frame_of_projAC_at hrun hy hNew.1
  have hheld₀ : old ∈ (tr.state y i).fg.tree := by
    rw [hf₀] at hc₀
    exact hc₀.1
  have hheld := tree_mono_at hrun ht hy hbj hij hheld₀
  have hfloor : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F new := by
    have h := (hΦ.rooted.2 new hc).mono hΦU
    rwa [hf] at h
  have hmem := frame_mem_of_tree_at hrun hnc ht hy hbj hheld (hfloor.trans backward)
  change old ∈ (Node.frame (tr.state y j)).tree at hmem
  rw [← hf] at hmem
  have hanc := Frame.anc_tree_of_anc_U (honestBlocksAt_coherent hrun hnc) hΦ hΦU hc backward hmem
  have hsupp : SA.AncR ell.frame new (tr.projAC.state y j).fgReported :=
    ⟨old, hmem, hrecord.symm, hanc⟩
  have hret := hNew.2.2
  unfold SA.acToFG at hret
  split_ifs at hret
  split at hret
  · contradiction
  · rename_i C hC
    split_ifs at hret with hs
    have hEq := Option.some.inj hret
    exact hs (hEq ▸ hsupp)

open Classical in
private theorem report_record_step (A : SA.SAState sp.n)
    (Φ : SA.Frm sp.n (List (FG.Att sp.n))) (y : Fin sp.n) (t : Time)
    (c : (goldilocksNode sp ro).Call) (hnr : c ≠ .restart) :
    (ACInterface.step (goldilocksNode sp ro) y A Φ t c).1.fgReported =
      ((if c = ACInterface.Call.toFG then (SA.acToFG sp A Φ t).2 else none).map (·.root)).getD
        A.fgReported := by
  have admit (B : SA.SAState sp.n) (v : SA.Vote sp.n) :
      (SA.admitVote sp B t v).fgReported = B.fgReported := by
    unfold SA.admitVote
    split_ifs <;> rfl
  have latest (B : SA.SAState sp.n) (C : SA.Blk sp.n (List (FG.Att sp.n))) :
      (SA.updateLatestConfirmed sp B Φ C).fgReported = B.fgReported := by
    unfold SA.updateLatestConfirmed
    split_ifs <;> rfl
  have optimistic (B : SA.SAState sp.n) :
      (SA.optimisticConfirmation sp B Φ t).fgReported = B.fgReported := by
    unfold SA.optimisticConfirmation
    split
    · rfl
    · exact latest _ _
  have update (B : SA.SAState sp.n) (s : Nat) :
      (SA.updateConfirmation sp B Φ t s).fgReported = B.fgReported := by
    unfold SA.updateConfirmation
    dsimp only
    split
    · rfl
    · split_ifs
      · rfl
      all_goals exact latest _ _
  have vote (B : SA.SAState sp.n) : (SA.tryVote sp y B Φ t).1.fgReported = B.fgReported := by
    unfold SA.tryVote
    dsimp only
    split_ifs <;> first | rfl | exact (optimistic _).trans (admit _ _)
  cases c with
  | restart => exact (hnr rfl).elim
  | proposal =>
    rw [ite_eq_right (by intro h; cases h)]
    change (SA.acProposal sp A Φ t).1.fgReported = _
    unfold SA.acProposal
    split_ifs <;> rfl
  | tick =>
    rw [ite_eq_right (by intro h; cases h)]
    change (SA.acOnTick sp y A Φ t).1.fgReported = A.fgReported
    unfold SA.acOnTick
    dsimp only
    split_ifs <;> first | rfl | exact (update _ _).trans (vote _) | exact update _ _ | exact vote _
  | message v =>
    rw [ite_eq_right (by intro h; cases h)]
    exact ((vote _).trans (optimistic _)).trans (admit _ _)
  | block B =>
    rw [ite_eq_right (by intro h; cases h)]
    have receipt : (SA.blockReceipt sp A t B).fgReported = A.fgReported := by
      unfold SA.blockReceipt
      generalize he : ({ A with
        blockStamp := Function.update A.blockStamp B.root (SA.ETime.of t) } : SA.SAState sp.n) = A'
      rw [← show A'.fgReported = A.fgReported by rw [← he]]
      clear he
      induction SA.blockVotes B generalizing A' with
      | nil => rfl
      | cons _ _ ih => rw [List.foldl_cons, ih, admit]
    exact ((vote _).trans (optimistic _)).trans receipt
  | toFG =>
    rw [ite_eq_left rfl]
    change (SA.acToFG sp A Φ t).1.fgReported = ((SA.acToFG sp A Φ t).2.map (·.root)).getD _
    unfold SA.acToFG
    split_ifs
    · split
      · rfl
      · split_ifs <;> rfl
    · rfl

/-- Consecutive successful reports of an honest node order forward within a sleepy window,
provided no restart intervenes. Non-report calls and unsuccessful report calls preserve the
first report's recorded root. -/
theorem report_extends_previous_without_restart_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time} (hsleepy : SleepyInvariantUpTo tr H b)
    {y : Fin sp.n} {i j : Nat} (hij : i < j) (hy : y ∈ H (tr.time j)) (hjb : tr.time j ≤ b)
    {old new : SA.Blk sp.n (List (FG.Att sp.n))}
    {ell₀ ell : ACLabel (goldilocksNode sp ro)}
    (hOld : SA.ToFGAt tr.projAC y i ell₀ old) (hNew : SA.ToFGAt tr.projAC y j ell new)
    (hnr : ∀ k, i < k → k < j → ¬ tr.projAC.RestartAt y k)
    (hprev : ∀ k, i < k → k < j → ∀ l C, ¬ SA.ToFGAt tr.projAC y k l C) :
    Anc (tr.HonestBlocksAt H) old new := by
  classical
  have hac := (Compose.Growing.goldilocks_ac_projection_from hrun hnc).localRun
  have hstep : ∀ {k l}, k ≤ j → tr.projAC.CallAt y k l → l.call ≠ .restart →
      (tr.projAC.state y (k + 1)).fgReported =
        ((if l.call = ACInterface.Call.toFG then
          (SA.acToFG sp (tr.projAC.state y k) l.frame (tr.time k)).2 else none).map
            (·.root)).getD (tr.projAC.state y k).fgReported := by
    intro k l hkj hc hnr'
    have he := hac.exec k l hc.2 (hc.1 ▸ hrun.antitone (hrun.time_mono hkj) hy)
    rw [hc.1] at he
    have hst : tr.projAC.state y (k + 1) = tr.projAC.post k := by
      simp [Trace.state, hc.1, hc.2]
    have hpost := congrArg Prod.fst he
    dsimp only at hpost
    rw [hst, ← hpost]
    exact report_record_step _ _ y _ _ hnr'
  have hfirst := hstep hij.le hOld.1 (by rw [hOld.2.1]; intro h; cases h)
  have hret := hOld.2.2
  change (SA.acToFG sp (tr.projAC.state y i) ell₀.frame (tr.time i)).2 = some old at hret
  have hb₀ : (tr.projAC.state y (i + 1)).fgReported = old.root := by
    simpa only [hOld.2.1, ite_true, hret, Option.map_some, Option.getD_some] using hfirst
  have hrec : ∀ k, i < k → k ≤ j → (tr.projAC.state y k).fgReported = old.root := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hik hkj
      by_cases he : k = i
      · exact he ▸ hb₀
      have hik' : i < k := by omega
      have hkj' : k < j := by omega
      have hold := ih hik' hkj'.le
      by_cases hc : ∃ l, tr.projAC.CallAt y k l
      · obtain ⟨l, hl⟩ := hc
        rw [hstep hkj'.le hl (fun h => hnr k hik' hkj' ⟨l, hl, h⟩), hold]
        by_cases hto : l.call = .toFG
        · have hn : (SA.acToFG sp (tr.projAC.state y k) l.frame (tr.time k)).2 = none := by
            cases h : (SA.acToFG sp (tr.projAC.state y k) l.frame (tr.time k)).2 with
            | none => rfl
            | some C => exact (hprev k hik' hkj' l C ⟨hl, hto, h⟩).elim
          simp [hto, hn]
        · simp [hto]
      · have hst : tr.projAC.state y (k + 1) = tr.projAC.state y k := by
          rw [Trace.state]
          split_ifs with h
          · exact absurd ⟨_, h.1, (Option.ne_none_iff_exists'.1 h.2).choose_spec⟩ hc
          · rfl
        rwa [hst]
  exact report_extends_recorded_report_at hrun hnc hsleepy hij.le hy hjb hOld hNew
    (hrec j hij le_rfl)

/-- A frozen row already in the proposer's pool and not on its chosen parent chain is selected
exactly when it names the current entry or carries a still-pending finality vote at an older height.
Release does not refresh either payload field. -/
theorem frozen_row_selected_iff {P : Params} {ACP : Type} (st : Store P ACP)
    {head : NodeBlock P ACP} {att : FG.Att P.n}
    (hpool : att ∈ st.atts) (hnew : ¬ st.OnChain head att) :
    att ∈ st.proposalAttestations head ↔
      (att.h = (st.σ head.root).h ∧ att.T = (st.σ head.root).Th) ∨
        ∃ p ∈ att.fin.toList, p ∈ (st.σ head.root).pending ∧ p.1 < att.h ∧
          att.h < (st.σ head.root).h := by
  simp only [Store.proposalAttestations, List.mem_filter, decide_eq_true_eq, hpool, hnew,
    not_false_eq_true, true_and, and_true, FG.ChainState.validAtt]

/-- Even if a stale row is selected for finality, processing it cannot add a progress or target
bit at the newer height. -/
theorem frozen_row_old_height_bits {n : Nat} (σ : FG.ChainState n) (att : FG.Att n)
    (hold : att.h < σ.h) :
    (σ.processAtt att).prog = σ.prog ∧ (σ.processAtt att).target = σ.target := by
  have hh : att.h ≠ σ.h := Nat.ne_of_lt hold
  cases hf : att.fin with
  | none => simp [FG.ChainState.processAtt, hf, hh]
  | some p =>
    by_cases hp : p ∈ σ.pending <;> simp [FG.ChainState.processAtt, hf, hp, hh]

/-- A fixed shift of a public report time by whole node delays has an actual tick when the
node is honest and awake at the due time. A restart at the due time precedes that tick. This
supplies a duty, not an attestation or wakefulness for historical reports. -/
theorem fixed_shift_tick_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {t : Time} (ht : 0 ≤ t) (hpublic : sp.toParams.IsPublic t) (L : Nat)
    (hy : y ∈ H (t + (L : Time) * sp.Δ)) (hawake : tr.awake y (t + (L : Time) * sp.Δ)) :
    ∃ j, tr.TickAt proposer dg y j (t + (L : Time) * sp.Δ) ∧
      ∀ r, tr.GroupAt proposer dg y r (t + (L : Time) * sp.Δ) .restart → r ≤ j := by
  have hnonneg : 0 ≤ t + (L : Time) * sp.Δ :=
    add_nonneg ht (mul_nonneg (Int.natCast_nonneg L) sp.toParams.hΔ.le)
  have hgrid : sp.toParams.IsPublic (t + (L : Time) * sp.Δ) :=
    dvd_add hpublic ⟨(L : Time), mul_comm _ _⟩
  obtain ⟨j, x, hj⟩ := hrun.tick_of_awake y _ hy hnonneg hgrid hawake
  refine ⟨j, ⟨x, hj⟩, fun r hr => le_of_not_gt fun h => ?_⟩
  have hphase := hrun.toLocalRun.phase_order y y j r _ (.tick x) .restart hy hy hj hr h
  change 1 ≤ 0 at hphase
  omega

/-- An actual attempt on the original same-height source supplies the row, even if the
client suppressed the attempt because it previously signed at that height. This does not
assert that the policy services the due tick or that the attestation has been published. -/
theorem ResetPremisesUpTo.row_of_delayed_original_report_at
    {g ΔF a b : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {z : Fin sp.n} {r k : Nat} (hrk : r ≤ k) (hzk : z ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    (hkb : tr.time k ≤ b) {ell : ACLabel (goldilocksNode sp ro)}
    {C T : SA.Blk sp.n (List (FG.Att sp.n))} (hreport : SA.ToFGAt tr.projAC z r ell C)
    {s : Option (FG.Att sp.n)} (hattempt : tr.CallAt z k (.fg (.attest C s)))
    {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t)
    (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    (hTC : Anc (tr.HonestBlocksAt H) T C) (hCh : ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time k ∧ att.val = z ∧
      att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  have hrt := hp.run.time_mono hrk
  have hzr := hp.run.antitone (max_le_max le_rfl hrt) hzk
  obtain ⟨io, _, jo, O, _, _, ho, hiob, _, hCO, _⟩ :=
    hp.high_report_origin_at hzr hreport (hrt.trans hkb) (hCh ▸ hhT)
  have hTO := hTC.trans hCO
  have hz := hp.run.antitone (le_max_right _ _) hzk
  have hz₀ := hp.run.antitone hrt hz
  have hk₀ := hp.run.time_nonneg k
  have hleK : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hp.run.time_mono hq.le
  have hleR : ∀ q < r, tr.time q ≤ tr.time r := fun q hq => hp.run.time_mono hq.le
  have hCr := toFG_mem_tree_at hp.run hz₀ hreport
  have hC := tree_mono_at hp.run hk₀ hz hleK hrk hCr
  have hTk := mem_of_honest_anc_at hp.run hp.noColl hk₀ hleK hz hTC hC
  have hσk := (σ_eq_honest_at hp.run hp.noColl hk₀ hleK hz ht hle hy hTk hT).trans hσ
  have hCk : ((tr.state z k).fg.σ C.root).h = σT.h := by
    rw [← σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg r) hleR hz₀ hk₀ hleK hz hCr hC]
    exact hCh
  have hCTh : ((tr.state z k).fg.σ C.root).Th = T.root := by
    rw [Healing.Th_eq_of_anc (fg_reachable_at hp.run hk₀ hleK hz)
      (store_anc_of_honest_anc_at hp.run hp.noColl hk₀ hleK hz hTC hC)
      (by rw [hCk, hσk]), hσk, hTe]
  have hentry : (tr.state z k).fg.σ ((tr.state z k).fg.σ C.root).Th = σT := by
    rw [hCTh, hσk]
  have hsign : ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time k ∧ att.h = σT.h := by
    cases s with
    | some att =>
      have hcut := (hp.run.cutLaw z k _ hattempt hz).1
      change (tr.state z k).record.createAtt z ((tr.state z k).fg.σ
        ((tr.state z k).fg.σ C.root).Th) = some (att, _) at hcut
      exact ⟨k, att, ⟨C, hattempt⟩, le_rfl, by rw [(createAtt_fields hcut).2.1, hentry]⟩
    | none =>
      have hcut := (hp.run.cutLaw z k _ hattempt hz).1
      change (tr.state z k).record.createAtt z ((tr.state z k).fg.σ
        ((tr.state z k).fg.σ C.root).Th) = none at hcut
      rw [hentry] at hcut
      rcases createAtt_refused hcut with ⟨hl, hl'⟩ | ⟨c, hc, _⟩
      · obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.1 hl
        have he := hp.record_entry_eq_at hk₀ hleK hzk hkb hhT (Or.inr (Or.inr hroot))
          ho hiob hTO ht hle hy hT (congrArg FG.ChainState.h hσ)
          ((congrArg FG.ChainState.Th hσ).trans hTe)
        exact absurd (by rw [hroot, he, hTe]) hl'
      · obtain ⟨j, hj, att, hs, rfl⟩ := Healing.sent_origin_from (hp.run.upTo hk₀).toLocalRun hz k
          (by rw [Trace.upTo_state tr z hleK]; exact hc)
        exact ⟨j, att, ((RunTrace.upTo_signAt _).mp hs).2, hp.run.time_mono hj.le, by assumption⟩
  obtain ⟨j, att, hs, htj, hh⟩ := hsign
  obtain ⟨hv, hroot, htimeout, hfin⟩ := hp.row_of_sign_at
    (hp.run.antitone (max_le_max le_rfl htj) hzk) hs (htj.trans hkb)
    ht hle hy hT hσ hTe hhT hhj ho hiob hTO hh
  exact ⟨j, att, hs, htj, hv, hh, hroot, htimeout, hfin⟩

/-- Exact-source service through the horizon gives the signed quorum branch of row supply.
The service hypothesis is about observed attempts, not a bound on gaps between open gates. -/
theorem ResetPremisesUpTo.rowSupplyWithin_of_original_attempts
    {g ΔF a b D : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK) (hD : 0 ≤ D)
    (hservice : ∀ z r ell C, SA.ToFGAt tr.projAC z r ell C → tr.time r + D ≤ b →
      z ∈ H (max (cutZ sp.toParams g) (tr.time r + D)) →
      ∃ k s, r ≤ k ∧ tr.time k ≤ tr.time r + D ∧ tr.CallAt z k (.fg (.attest C s))) :
    RowSupplyWithin tr H g b D := by
  classical
  refine ⟨?_⟩
  intro T y m t ht hle hy hT σT hσ hTe hhT hhj d hd hdb hreports
  left
  let p := max (cutZ sp.toParams g) (d + D)
  refine ⟨Finset.univ.filter (· ∈ H p), ?_, ?_⟩
  · have hcard : (Finset.univ.filter (· ∈ H p)).card = (H p).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp
    rw [hcard]
    have hn : (H p).ncard + (H p)ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    have hf := hp.faults p ((add_nonneg hd hD).trans (le_max_right _ _))
      (max_le (hj.2.le.trans hjb) hdb)
    change (2 * sp.n + 2) / 3 ≤ _
    omega
  · intro z hz
    have hzH := (Finset.mem_filter.1 hz).2
    obtain ⟨r, ell, C, hr, hrd, hTC, hh⟩ := hreports z
      (hp.run.antitone (max_le_max le_rfl (le_add_of_nonneg_right hD)) hzH)
    have hrdD : tr.time r + D ≤ d + D := Int.add_le_add_right hrd D
    obtain ⟨k, s, hrk, hk, hattempt⟩ := hservice z r ell C hr (hrdD.trans hdb)
      (hp.run.antitone (max_le_max le_rfl hrdD) hzH)
    obtain ⟨j, att, hs, htj, hv, hah, hroot, htimeout, hfin⟩ :=
      hp.row_of_delayed_original_report_at hrk
        (hp.run.antitone (max_le_max le_rfl (hk.trans hrdD)) hzH) (hk.trans (hrdD.trans hdb))
        hr hattempt ht hle hy hT hσ hTe hhT hhj hTC hh
    exact ⟨hzH, att, j, hs, hv, hah, hroot, htimeout, htj.trans (hk.trans hrdD), hfin⟩

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A correctly keyed attestation in one of the first two positions after the FG update is
actually released by the two selected trailing polls. Other entries may precede or follow it. -/
theorem att_released_of_trailing_poll_rank (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (k : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll) (hdue : (shapeOf S hn nd).fgDue = true)
    {a : FG.Att (Fintype.card V)} (hval : a.val = rho.ownKey v)
    (hrank : let Q := (fgUpdate (shapeOf S hn nd)).outbox
      Q.head? = some (.att (encodeAtt a)) ∨ Q.tail.head? = some (.att (encodeAtt a))) :
    attObj a ∈ (rho.dutyStep v nd (.poll k)).2 ++
      (rho.dutyStep v (rho.dutyStep v nd (.poll k)).1 (.poll k)).2 := by
  obtain ⟨F, hfirst, _, hsecond, _, _⟩ := trailing_polls S rho hn v nd k hsel hdue
  have hkey := pollRole_selected_of_not_vote S rho hsel
    (b := .att (encodeAtt a)) (fun _ h => by cases h)
  rw [attObj_eq_pollObj_of_val S rho hval, hfirst, hsecond]
  rcases hrank with h | h
  · apply List.mem_append_left _ (List.mem_append_left _ ?_)
    rw [h, relHead_eq, Option.elim_some, ite_eq_left hkey]
    exact List.mem_singleton_self _
  · apply List.mem_append_right _
    rw [h, relHead_eq, Option.elim_some, ite_eq_left hkey]
    exact List.mem_singleton_self _

end Consensus.Goldilocks.Simulation

end
