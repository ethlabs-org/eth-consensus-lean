module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyConfirmedSupply
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafety
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

/-! # The healthy confirmed-supply endpoint from the preparation initializer

`healthy_confirmed_supply_of_initializer` proves the statement of `healthy_confirmed_supply`
from the type of the initializer `healthy_preparation_initialize`, taken as a hypothesis.
Everything else is produced here or landed:

* `UpTo.operational_update_fresh_lock`: at every actual honest update of an actual post-drain
  proposal `P` of slot `u`, the post-state holds the fresh fast lock `(P, u, true)` (the
  `hlocks` input of `healthy_confirmed_coverage_of_service`). The selection is
  `UpTo.operational_update_selection`; `P` is its own viable ancestor in the update frame by the
  held-target candidate argument; the update writes the lock (expiry at least `u + 2`).
* `healthy_cut_tips_ancestor_of_preparation`: the statement of `healthy_cut_tips_ancestor`, with
  its repair schedule from the supplied preparation schedule
  (`healthy_repair_schedule_of_preparation`) instead of the open `healthy_repair_schedule`.
* The endpoint: the selected proposal is `healthy_query_slot`/`confirmed_slot_event` at the
  query's own readiness, its coverage is `healthy_confirmed_coverage_of_service`, and the
  later-read continuation is the variant above at the end-of-time cuts of `t_u + 6Δ` and the
  deadline (A1–A3).

`healthy_confirmed_supply` (NonfinalEndpoints) applies it to the proved initializer
(`HealthyResetEnvelope`). -/

public section
namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

section FiniteSupply
variable {sp : SA.SAParams}
  {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {g ΔF a b : Time}

/-- A fast update writes its fast lock with an expiry of at least `u + 2` (`s + k` or
`fastExpiry`), so it is live at every `t` of slot at most `u + 2`. -/
private theorem fastLock_mem_updateConfirmation_floor {FGP : Type} {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n FGP} {t : Time} {u : Nat} {P : SA.Blk sp.n FGP} (hPt : P ∈ Φ.tree)
    (hva : Φ.viableAncestor P = P) (hconf : SA.getConfirmation sp A Φ u = some P)
    (hnv : ¬ SA.conflictsWithLock sp A.locks Φ t P) (hfast : SA.fastSelect sp A Φ u P = some P)
    (hage : sp.slot t ≤ u + 2) :
    ∃ e, u + 2 ≤ e ∧
      (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (SA.updateConfirmation sp A Φ t u).locks := by
  -- unvetoed, so the filtered fast selection is the raw one
  have hD := Obligations.UpTo.deepest_of_subset (S := {B | B ∈ {B | B ∈ SA.confirmationPath sp Φ P ∧
      ¬ SA.conflictsWithLock sp A.locks Φ t B} ∧ SA.FastTest sp A Φ u B}) hfast
    (fun B hB => ⟨hB.1.1, hB.2⟩)
    ⟨⟨(SA.deepest_mem hfast).1.1, hnv⟩, (SA.deepest_mem hfast).1.2⟩
  unfold SA.updateConfirmation
  simp only [hconf]
  rw [ite_eq_right hnv]
  exact ⟨_, SA.le_fastExpiry sp _ _ _ _, ⟨P.root, u, true, _⟩,
    Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPt, rfl,
    hage.trans (SA.le_fastExpiry sp _ _ _ _), by rw [hva]⟩

/-- **The fresh fast lock at an actual update.** Every honest update of slot `u` after the drain
writes `(P, u, true, e)` for the actual designated proposal `P` of slot `u`, with an expiry
`e ≥ u + 2`. -/
theorem UpTo.operational_update_fresh_lock
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hR : Healing.drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks := by
  have hΔ := sp.toParams.hΔ
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  obtain ⟨hPt, hconf, hnv, hfast, hpost, -⟩ :=
    UpTo.operational_update_selection hp hc hpH hdesignated hactual hPs hR hgu hTb hy hup
  have hframe := Compose.frame_of_projAC hp.run hy hup.1
  have hPj : P ∈ (Node.frame (tr.state y j)).tree := hframe ▸ hPt
  have hPU : P ∈ tr.HonestBlocks H := ⟨y, hy, j, hPj.1⟩
  have hun := hp.operational_unanimous hc hpH hdesignated hactual hPs hR
    (show sp.ts u ≤ b by linarith only [hTb, hΔ])
  have hRnext := hR.trans ((SA.ts_le_iff sp).mpr
    (show (u : Int) ≤ (u + 1 : Nat) by exact_mod_cast Nat.le_succ u))
  have hu : 0 < u := by
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    exact (Nat.succ_pos _).trans_le (by exact_mod_cast this)
  have hprefix : ∀ q < j, tr.time q ≤ b :=
    fun q hq => (hp.run.time_mono hq.le).trans (ht ▸ hTb)
  obtain ⟨v, r, m, S, hseed, hrb, -, hrt⟩ := hp.reset_seed_before_slot hRnext
  have hSP := UpTo.high_origins_before_next_slot_below hp hc hPU
    (fun z hz q e hv hqb hs => hun z hz q e hv hs hqb) hgu hRnext
    (by linarith only [hTb, hΔ]) hseed hrt hrb
  have hva : (Node.frame (tr.state y j)).viableAncestor P = P := by
    apply SA.viableAncestor_self (Compose.frameOK_state hp.run.toLocalRun hy j) hPj
    exact (UpTo.held_target_ancestor_candidate_at_state hp hy hprefix hPj hseed hrb hSP
      (fun x q l B hqe ho =>
        (UpTo.high_origin_compatible_before_update hp hc hPU hPs hu
          (fun z hz q e hv hqb hs => hun z hz q e hv hs hqb) hgu hRnext hTb ho
          ((hp.run.time_mono hqe.le).trans ht.le)).symm)).symm
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    apply SA.slot_of_mem sp (u + 1)
    · simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ]
    · simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ]
  rw [hpost]
  exact fastLock_mem_updateConfirmation_floor hPt (hframe ▸ hva) hconf hnv hfast
    (by rw [hslot]; exact Nat.le_succ _)

end FiniteSupply

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- **Tip ancestry from a preparation schedule.** The statement of `healthy_cut_tips_ancestor`,
with the state facts and the repair schedule produced from `W` and `Dprep`
(`healthy_prepare`, `healthy_preserve`, `healthy_repair_schedule_of_preparation`). -/
theorem healthy_cut_tips_ancestor_of_preparation (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q) (Dprep : HealthyPreparationSchedule S A V Q W)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2))
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now)
      (Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn j)
        (stateAt S Q.run.2 Q.hn v j).now) := by
  have states := healthy_preserve S A V Q h0 hb W (healthy_prepare S A V Q h0 hb hp W Dprep)
  obtain ⟨D, -, -, -⟩ := healthy_repair_schedule_of_preparation S A V Q W Dprep
  obtain ⟨O, hr⟩ := healthy_bounded_repairing_opening S A V Q h0 hb hp W states D
  rw [healthy_current_record_read S A V Q h0 hb hp W states D O hr hi hvi,
    healthy_current_record_read S A V Q h0 hb hp W states D O hr hj hvj]
  exact effective_record_of_interval D.reset.run D.reset.noColl
    (honest_ownKey (S := S) ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hvi.1))
    (cutMap_mono S Q.run.2 Q.hn hij)
    (healthy_current_record_interval S A V Q h0 hb hp W states D O hr hi hj hij hvi) .refl

/-- Engine readiness from health: an honest validator is ready at every `t ∈ [ready, horizon]`
(HealthyOn keeps it awake on `[max g 0, horizon]`). -/
private theorem confirmed_ready_of_healthy (Q : ConfirmedQuery S A V)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) Q.gst Q.run) {v : V}
    (hv : Q.run.2.point.HonestAt v 0) {t : Time}
    (hr : (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run ≤ t) (htb : t ≤ Q.run.2.horizon) :
    Q.run.2.point.Ready Q.duration v t := by
  refine ⟨(Q.run.2.point.honestAt_iff_zero Q.constant _ _).mpr hv,
    fun τ hτ hτt => hh.2.1.2 v τ ?_ (hτt.trans htb)
      ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mpr hv)⟩
  change max Q.gst 0 + Q.duration + 1 ≤ t at hr
  exact le_trans (show max Q.gst 0 ≤ t - Q.duration - 1 by linarith)
    ((le_max_right 0 _).trans hτ)

/-- The end-of-time cut of a ready validator: `CutAfter` at its trace cut, the stored clock,
and `cutTime (endCut t) = t` (`now_bounds_cut` gives the lower bound). -/
private theorem confirmed_end_cut (Q : ConfirmedQuery S A V) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ Q.run.2.horizon) (hr : Q.run.2.point.Ready Q.duration v t) :
    Regimes.CutAfter Q.trace (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t ∧
      (stateAt S Q.run.2 Q.hn v ((chainTrace Q.run.2).endCut t)).now = t ∧
      (chainTrace Q.run.2).cutTime ((chainTrace Q.run.2).endCut t) = t ∧
      (chainTrace Q.run.2).endCut t ≤ Q.run.2.events.length := by
  obtain ⟨hcut, -, hnow⟩ := ready_read_cut S Q.run.2 Q.hn Q.constant Q.valid (c := Q.duration)
    ((mul_nonneg (by norm_num) Q.params.toParams.hΔ.le :
      (0 : Time) ≤ Regimes.catchUp Q.params).trans
      (confirmed_duration_supply S A V Q)) ht hth hr
  have hle : (chainTrace Q.run.2).endCut t ≤ Q.run.2.events.length := Nat.findGreatest_le _
  have hup : (chainTrace Q.run.2).cutTime ((chainTrace Q.run.2).endCut t) ≤ t :=
    Nat.findGreatest_spec (P := fun i => (chainTrace Q.run.2).cutTime i ≤ t)
      (Nat.zero_le _) ht
  have hlo := (now_bounds_cut S Q.run.2 Q.hn Q.valid v hle).2
  rw [hnow] at hlo
  exact ⟨hcut, hnow, le_antisymm hup hlo, hle⟩

/-- `CutAfter` determines its cut. -/
private theorem confirmed_cutAfter_unique (Q : ConfirmedQuery S A V) {i j : Nat} {t : Time}
    (hi : Regimes.CutAfter Q.trace i t) (hj : Regimes.CutAfter Q.trace j t) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (hj.1 i h) (not_le.2 hi.2)
  · exact h
  · exact absurd (hi.1 j h) (not_le.2 hj.2)

/-- **The healthy confirmed supply, conditional on the preparation initializer.** The statement
of `healthy_confirmed_supply`, with one more hypothesis: the type of the initializer
`healthy_preparation_initialize`, which `healthy_confirmed_supply` supplies. -/
theorem healthy_confirmed_supply_of_initializer (Q : ConfirmedQuery S A V)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) Q.gst Q.run)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon Q.run)
    (ht : (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst Q.run ≤ Q.query)
    (hinit : ∀ Q' : HealthyPreparationQuery S A V, 0 ≤ Q'.heal → Q'.heal ≤ Q'.run.2.horizon →
      (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q'.cap Q'.index
        Q'.ready Q'.heal Q'.run →
      ∃ W : HealthyBaseTiming S A V Q', Nonempty (HealthyPreparationSchedule S A V Q' W)) :
    ∃ P : ConfirmedProposal S A V Q,
      ∀ y j, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration y Q.deadline →
        Regimes.CutAfter Q.trace j Q.deadline →
        Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) P.block
          (Regimes.readAfter Q.trace y j Q.deadline) := by
  classical
  let Q' : HealthyPreparationQuery S A V :=
    ⟨Q.run, Q.constant, Q.hn, Q.cap, Q.nonfinal, Q.index, Q.gst, Q.valid, Q.noCollision, hh⟩
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hΔ := Q.params.toParams.hΔ
  -- the preparation query: `0 ≤ heal ≤ query ≤ deadline ≤ horizon`, progress on `[ready, heal]`
  have h0 : 0 ≤ Q'.heal := by
    change 0 ≤ max Q.gst 0 + ((K S A).params.heal Q.cap Q.index : Time) * Q.run.1.ΔAC
    exact add_nonneg (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd))
  have hqD : Q.query ≤ Q.deadline :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd))
  have hb : Q'.heal ≤ Q'.run.2.horizon := ht.trans (hqD.trans Q.bounded)
  have hp' : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q'.cap Q'.index
      Q'.ready Q'.heal Q'.run := (shapeProgress (goldilocks S) V).mono le_rfl hb hp
  obtain ⟨W, ⟨Dprep⟩⟩ := hinit Q' h0 hb hp'
  have hrh : Q'.ready ≤ Q'.heal := by
    linarith only [W.ready_le, W.records, hΔ]
  -- the selected proposal at the query's own readiness
  obtain ⟨Ws⟩ := healthy_query_slot S A V Q hp (max_le (hrh.trans ht) (h0.trans ht))
  obtain ⟨B, k, hBp, he, htk⟩ := confirmed_slot_event S A V Q Ws
  have hr : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) Q.duration B.proposer
      (Q.trace.time k) := by rw [hBp, htk]; exact Ws.ready
  have hacc := Compose.proposal_accepted (simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid)
    (noCollRun_simTrace S Q.run.2 Q.hn Q.constant Q.valid Q.noCollision) hr.1 he
  have hmargin := Ws.margin
  have hbound : Q.trace.time k ≤ Q.deadline := by rw [htk]; linarith only [hmargin, hΔ]
  refine ⟨⟨B, k, he, hacc, hr, htk ▸ Ws.fresh, hbound⟩, ?_⟩
  have hPs : B.slot = Ws.slot := by
    have h1 : Q.params.ts B.slot = Q.params.ts Ws.slot :=
      ((Q.params.slotTime_eq _).symm.trans he.2.2.symm).trans htk
    have h2 := (SA.ts_le_iff Q.params).1 h1.le
    have h3 := (SA.ts_le_iff Q.params).1 h1.ge
    exact_mod_cast le_antisymm h2 h3
  -- the finite inputs of `healthy_confirmed_coverage_of_service`
  have hc := healthy_repair_catch S A V Q'
  have hfresh := Ws.fresh
  have hq : Dprep.query < Q.params.ts Ws.slot := by
    have := Dprep.reserve
    have : (0 : Time) ≤ (4 * (Q.index : Time) + 6) * Q.params.Δ :=
      mul_nonneg (by positivity) hΔ.le
    change Q'.heal ≤ Q.query at ht
    linarith only [Dprep.reserve, this, ht, hfresh]
  have hlow := Dprep.lower
  simp only [max_le_iff] at hlow
  obtain ⟨-, hdr, -, hgr, -, -⟩ := hlow
  have hR : Healing.drainTime Q.params Dprep.resetTime ≤ Q.params.ts Ws.slot := hdr.trans hq.le
  have hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts Ws.slot := hgr.trans hq.le
  have hTb : Q.params.ts Ws.slot + 6 * Q.params.Δ ≤ Q.run.2.horizon := hmargin.trans Q.bounded
  have hlocks : ∀ y ∈ honestKeys S Q.run.2, ∀ j ell,
      SA.UpdateAt Q.trace.projAC y j Ws.slot ell →
      ∃ e, Ws.slot + 2 ≤ e ∧ (⟨B.root, Ws.slot, true, e⟩ : SA.Lock) ∈
        (Q.trace.projAC.post j).locks :=
    fun y hy j ell hup => UpTo.operational_update_fresh_lock Dprep.reset hc hr.1 hBp he hPs
      hR hgu hTb hy hup
  -- readiness and end-of-time cuts at `T = t_u + 6Δ` and at the deadline
  have hhT : Q'.heal ≤ Q.params.ts Ws.slot + 6 * Q.params.Δ := by
    change Q'.heal ≤ Q.query at ht
    linarith only [ht, hfresh, hΔ]
  have hrT : Q'.ready ≤ Q.params.ts Ws.slot + 6 * Q.params.Δ := hrh.trans hhT
  have hT0 : 0 ≤ Q.params.ts Ws.slot + 6 * Q.params.Δ := h0.trans hhT
  have hcut : ∃ i, Regimes.CutAfter Q.trace i (Q.params.ts Ws.slot + 6 * Q.params.Δ) := by
    obtain ⟨v, hv⟩ := Q.reader
    exact ⟨_, (confirmed_end_cut S A V Q hT0 hTb
      (confirmed_ready_of_healthy S A V Q hh
        ((Q.run.2.point.honestAt_iff_zero Q.constant _ _).mp hv.1) hrT hTb)).1⟩
  refine healthy_confirmed_coverage_of_service S A V Q ⟨B, k, he, hacc, hr, htk ▸ Ws.fresh,
    hbound⟩ Dprep.reset hc hBp hPs hR hgu hmargin hlocks hcut ?_
  -- the later-read continuation from the preparation schedule
  intro y i j hy hi hj
  have hhon := (mem_honestKeys_iff S Q.run.2 y).mp hy.1
  have hvT := confirmed_ready_of_healthy S A V Q hh (v := Q.run.2.key y) hhon hrT hTb
  have hvD := confirmed_ready_of_healthy S A V Q hh (v := Q.run.2.key y) hhon
    (hrT.trans hmargin) Q.bounded
  obtain ⟨hcT, hnT, htT, hlT⟩ := confirmed_end_cut S A V Q hT0 hTb hvT
  obtain ⟨hcD, hnD, htD, hlD⟩ := confirmed_end_cut S A V Q (hT0.trans hmargin) Q.bounded hvD
  obtain rfl := confirmed_cutAfter_unique S A V Q hi hcT
  obtain rfl := confirmed_cutAfter_unique S A V Q hj hcD
  have hanc := healthy_cut_tips_ancestor_of_preparation S A V Q' h0 hb hp' W Dprep
    (Q.run.2.key y) ((chainTrace Q.run.2).endCut (Q.params.ts Ws.slot + 6 * Q.params.Δ))
    ((chainTrace Q.run.2).endCut Q.deadline) ⟨hlT, by rw [htT]; exact hhT⟩
    (Nat.le_findGreatest hlT (by rw [htT]; exact hmargin))
    ⟨hlD, by rw [htD]; exact hhT.trans hmargin⟩
    (by rw [htT]; exact hvT) (by rw [htD]; exact hvD)
  rw [hnT, hnD, show Q.run.2.ownKey (Q.run.2.key y) = y from
    Q.run.2.key.symm_apply_apply _] at hanc
  exact hanc

end Consensus.Goldilocks.Obligations
