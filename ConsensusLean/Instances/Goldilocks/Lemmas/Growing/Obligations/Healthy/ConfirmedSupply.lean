module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UpdateReadAfter
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalUnanimous
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyConfirmedEndpoint
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # The healthy confirmed supply under growing faults

`healthy_confirmed_supply_at`, the growing form of `Obligations.healthy_confirmed_supply`: on a
healthy run with progress from the ready point, a confirmed proposal after the heal point is in the
confirmed read of every node ready at the deadline.

* `operational_update_fresh_lock_at`: every update of the post-drain operational proposal `P` of
  slot `u`, by a node honest at it, writes the fresh fast lock `(P, u, true, e)`, `e ≥ u + 2`;
* `operational_proposal_read_after_at`: with those locks, every reader honest at `t_u + 6Δ` holds
  `P` under its confirmed read at the first cut after it (`operational_update_read_after_at`);
* `healthy_confirmed_supply_at`: the selected slot of the recurrence at the query's readiness, its
  actual proposal, the read at `t_u + 6Δ`, and the reader's tip ancestry from there to the deadline
  (`healthy_cut_tips_ancestor_at`).

Each node is honest at its own cut or read; ancestry is in the blocks held while honest. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The frame of a node honest at a cut is well formed. -/
private theorem frameOK_state_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    {i : Nat} (hy : y ∈ H (tr.time i)) : FrameOK (Node.frame (tr.state y i)) := by
  have h := Compose.frameOK_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- A fast update writes its fast lock with an expiry of at least `u + 2` (`s + k` or
`fastExpiry`), so it is live at every `t` of slot at most `u + 2`. -/
private theorem fastLock_mem_updateConfirmation_floor {FGP : Type} {A : SA.SAState sp.n}
    {Φ : SA.Frm sp.n FGP} {t : Time} {u : Nat} {P : SA.Blk sp.n FGP} (hPt : P ∈ Φ.tree)
    (hva : Φ.viableAncestor P = P) (hconf : SA.getConfirmation sp A Φ u = some P)
    (hnv : ¬ SA.conflictsWithLock sp A.locks Φ t P) (hfast : SA.fastSelect sp A Φ u P = some P)
    (hage : sp.slot t ≤ u + 2) :
    ∃ e, u + 2 ≤ e ∧
      (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (SA.updateConfirmation sp A Φ t u).locks := by
  have hD := Obligations.UpTo.deepest_of_subset (S := {B | B ∈ {B | B ∈
      SA.confirmationPath sp Φ P ∧ ¬ SA.conflictsWithLock sp A.locks Φ t B} ∧
      SA.FastTest sp A Φ u B}) hfast
    (fun B hB => ⟨hB.1.1, hB.2⟩)
    ⟨⟨(SA.deepest_mem hfast).1.1, hnv⟩, (SA.deepest_mem hfast).1.2⟩
  unfold SA.updateConfirmation
  simp only [hconf]
  rw [ite_eq_right hnv]
  exact ⟨_, SA.le_fastExpiry sp _ _ _ _, ⟨P.root, u, true, _⟩,
    Or.inr ⟨_, Or.inl ⟨P, hD, rfl⟩, rfl⟩, P, hPt, rfl,
    hage.trans (SA.le_fastExpiry sp _ _ _ _), by rw [hva]⟩

/-- **The fresh fast lock at an actual update.** Every update of slot `u` after the drain, by a
node honest at it, writes `(P, u, true, e)` for the actual designated proposal `P` of slot `u`,
whose proposer is honest through `t_u + Δ`, with an expiry `e ≥ u + 2`. -/
theorem operational_update_fresh_lock_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks := by
  have hΔ := sp.toParams.hΔ
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  obtain ⟨hPt, hconf, hnv, hfast, hpost, -⟩ :=
    operational_update_selection_at hp hc hhold hdesignated hactual hPs hR hgu hTb hy hup
  have hframe := Compose.Growing.frame_of_projAC_at hp.run hy hup.1
  have hPj : P ∈ (Node.frame (tr.state y j)).tree := hframe ▸ hPt
  have hPU : P ∈ tr.HonestBlocksAt H :=
    ⟨y, j, tr.time j, hp.run.time_nonneg j, fun q hq => hp.run.time_mono hq.le, hy, hPj.1⟩
  have hun0 := hp.operational_unanimous_at hc hhold hdesignated hactual hPs hR
    (show sp.ts u ≤ b by linarith only [hTb, hΔ])
  have hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root :=
    fun z q e hz hv hqb hs => hun0 z q e hz hv hs hqb
  have hRnext := hR.trans ((SA.ts_le_iff sp).mpr
    (show (u : Int) ≤ (u + 1 : Nat) by exact_mod_cast Nat.le_succ u))
  have hu : 0 < u := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    exact (Nat.succ_pos _).trans_le (by exact_mod_cast this)
  obtain ⟨v, r, m, S, hseed, hrb, -, hrt⟩ := hp.reset_seed_before_slot_at hRnext
  have hSP := high_origins_before_next_slot_below_at hp hc hPU hun hgu hRnext
    (by linarith only [hTb, hΔ]) hseed hrt hrb
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hva : (Node.frame (tr.state y j)).viableAncestor P = P := by
    apply SA.viableAncestor_self (frameOK_state_at hp.run hy) hPj
    exact (hp.held_target_ancestor_candidate_at_state_at (hp.run.time_nonneg j)
      (fun q hq => hp.run.time_mono hq.le) hy hjb hPj hseed hrb hSP
      (fun x q l B hqe ho => (high_origin_compatible_before_update_at hp hc hPU hPs hu hun
        hgu hRnext hTb ho ((hp.run.time_mono hqe.le).trans ht.le)).symm)).symm
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    apply SA.slot_of_mem sp (u + 1)
    · simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ]
    · simp only [SA.SAParams.ts]; push_cast; linarith only [hΔ]
  rw [hpost]
  exact fastLock_mem_updateConfirmation_floor hPt (hframe ▸ hva) hconf hnv hfast
    (by rw [hslot]; exact Nat.le_succ _)

/-- **Every reader honest at `t_u + 6Δ` holds the operational proposal** under its confirmed read
at the first cut after `t_u + 6Δ`, when every update of slot `u` by a node honest at it writes the
fresh fast lock. -/
theorem operational_proposal_read_after_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hTb : sp.ts u + 6 * sp.Δ ≤ b)
    (hlocks : ∀ y j (ell : ACLabel (goldilocksNode sp ro)), y ∈ H (tr.time j) →
      SA.UpdateAt tr.projAC y j u ell →
      ∃ e, u + 2 ≤ e ∧ (⟨P.root, u, true, e⟩ : SA.Lock) ∈ (tr.projAC.post j).locks) :
    ∀ y J, y ∈ H (sp.ts u + 6 * sp.Δ) → Regimes.CutAfter tr J (sp.ts u + 6 * sp.Δ) →
      Anc (tr.HonestBlocksAt H) P (Regimes.readAfter tr y J (sp.ts u + 6 * sp.Δ)) := by
  intro y J hy hJ
  have hstart : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hg := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) (sp.slot (SA.gbar g))).mpr le_rfl
    have hbound : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) =
        sp.ts (sp.slot (SA.gbar g)) + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [hbound]
    linarith
  obtain ⟨j, ell, -, hup, -⟩ := hp.update_toFG_calls_at hy hstart hTb
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  exact operational_update_read_after_at hp hc hhold hdesignated hactual hPs hR hgu hTb hy hup
    (hlocks y j ell (ht ▸ hy) hup) hJ

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- Engine readiness from health: a validator honest at `t ∈ [ready, horizon]` is ready at `t`
(`HealthyOn` keeps it awake on `[max g 0, horizon]` while honest). -/
private theorem confirmed_ready_of_healthy_at (Q : ConfirmedQueryAt S A V)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) Q.gst Q.run) {v : V} {t : Time}
    (hv : Q.run.2.point.HonestAt v t)
    (hr : (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run ≤ t) (htb : t ≤ Q.run.2.horizon) :
    Q.run.2.point.Ready Q.duration v t := by
  refine ⟨hv, fun τ hτ hτt => hh.2.1.2 v τ ?_ (hτt.trans htb)
    (fun h => hv (Q.run.2.point.faultyAt_mono hτt h))⟩
  change max Q.gst 0 + Q.duration + 1 ≤ t at hr
  exact le_trans (show max Q.gst 0 ≤ t - Q.duration - 1 by linarith)
    ((le_max_right 0 _).trans hτ)

/-- The end-of-time cut of a ready validator: `CutAfter` at its trace cut, the stored clock, and
`cutTime (endCut t) = t`. -/
private theorem confirmed_end_cut_at (Q : ConfirmedQueryAt S A V) {v : V} {t : Time}
    (ht : 0 ≤ t) (hth : t ≤ Q.run.2.horizon) (hr : Q.run.2.point.Ready Q.duration v t) :
    Regimes.CutAfter Q.trace (cutMap S Q.run.2 Q.hn ((chainTrace Q.run.2).endCut t)) t ∧
      (stateAt S Q.run.2 Q.hn v ((chainTrace Q.run.2).endCut t)).now = t ∧
      (chainTrace Q.run.2).cutTime ((chainTrace Q.run.2).endCut t) = t ∧
      (chainTrace Q.run.2).endCut t ≤ Q.run.2.events.length := by
  obtain ⟨hcut, -, hnow⟩ := ready_read_cut_at S Q.run.2 Q.hn Q.valid (c := Q.duration)
    ((mul_nonneg (by norm_num) Q.params.toParams.hΔ.le :
      (0 : Time) ≤ Regimes.catchUp Q.params).trans (confirmed_duration_supply_at S A V Q))
    ht hth hr
  have hle : (chainTrace Q.run.2).endCut t ≤ Q.run.2.events.length := Nat.findGreatest_le _
  have hup : (chainTrace Q.run.2).cutTime ((chainTrace Q.run.2).endCut t) ≤ t :=
    Nat.findGreatest_spec (P := fun i => (chainTrace Q.run.2).cutTime i ≤ t)
      (Nat.zero_le _) ht
  have hlo := (now_bounds_cut S Q.run.2 Q.hn Q.valid v hle).2
  rw [hnow] at hlo
  exact ⟨hcut, hnow, le_antisymm hup hlo, hle⟩

/-- `CutAfter` determines its cut. -/
private theorem confirmed_cutAfter_unique (Q : ConfirmedQueryAt S A V) {i j : Nat} {t : Time}
    (hi : Regimes.CutAfter Q.trace i t) (hj : Regimes.CutAfter Q.trace j t) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (hj.1 i h) (not_le.2 hi.2)
  · exact h
  · exact absurd (hi.1 j h) (not_le.2 hj.2)

/-- The read of a node at the trace cut after its last own event before an engine cut is its read
at the trace cut of that engine cut. -/
private theorem readAfter_lastOwn (Q : ConfirmedQueryAt S A V) {v : V} {n : Nat}
    (hn : n ≤ Q.run.2.events.length) (t : Time) :
    Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v n)) t =
      Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn n) t := by
  have hq := (lastOwn_spec S Q.run.2 v n).1
  have h₁ := simTraceAt_state_all S Q.run.2 Q.hn Q.valid v _ (hq.trans hn)
  have h₂ := simTraceAt_state_all S Q.run.2 Q.hn Q.valid v n hn
  rw [← stateAt_lastOwn S Q.run.2 Q.hn v n] at h₁
  unfold Regimes.readAfter
  rw [← h₁, ← h₂]

/-- **Healthy selected-proposal service under growing faults**: a confirmed proposal after the
heal point, in the confirmed read of every node ready at the deadline. The proposal is the actual
proposal of the slot that the recurrence selects at the query's readiness, whose proposer is
honest through its slot time plus `Δ`; every reader honest at `t_u + 6Δ` holds it then, and a
reader ready at the deadline keeps it by its tip ancestry. -/
theorem healthy_confirmed_supply_at (Q : ConfirmedQueryAt S A V)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) Q.gst Q.run)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon Q.run)
    (ht : (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst Q.run ≤ Q.query) :
    ∃ P : ConfirmedProposalAt Q,
      ∀ y j, Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration y Q.deadline →
        Regimes.CutAfter Q.trace j Q.deadline →
        Anc (Q.trace.HonestBlocksAt Q.keys) P.block
          (Regimes.readAfter Q.trace y j Q.deadline) := by
  classical
  let Q' : HealthyPreparationQueryAt S A V :=
    ⟨Q.run, Q.hn, Q.cap, Q.nonfinal, Q.index, Q.gst, Q.valid, Q.noCollision, hh⟩
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hΔ := Q.params.toParams.hΔ
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  -- the preparation query: `0 ≤ heal ≤ query ≤ deadline ≤ horizon`, progress on `[ready, heal]`
  have h0 : 0 ≤ Q'.heal := by
    change 0 ≤ max Q.gst 0 + ((K S A).params.heal Q.cap Q.index : Time) * Q.run.1.ΔAC
    exact add_nonneg (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd))
  have hqD : Q.query ≤ Q.deadline :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd))
  have hb : Q'.heal ≤ Q'.run.2.horizon := ht.trans (hqD.trans Q.bounded)
  have hp' : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q'.cap Q'.index
      Q'.ready Q'.heal Q'.run := (shapeProgress (goldilocks S) V).mono le_rfl hb hp
  obtain ⟨W, ⟨Dprep⟩⟩ := healthy_preparation_initialize_at S A V Q' h0 hb hp'
  have hrh : Q'.ready ≤ Q'.heal := by
    linarith only [W.ready_le, W.records, hΔ]
  -- the selected proposal at the query's own readiness
  obtain ⟨Ws⟩ := confirmed_query_slot_at S A V Q hp (max_le (hrh.trans ht) (h0.trans ht))
  obtain ⟨B, k, hBp, he, htk⟩ := confirmed_slot_event_at S A V Q Ws
  have hr : Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration B.proposer (Q.trace.time k) := by
    rw [hBp, htk]; exact Ws.ready
  have hacc := proposal_accepted_at hrun hnc hr.1 he
  have hmargin := Ws.margin
  have hbound : Q.trace.time k ≤ Q.deadline := by rw [htk]; linarith only [hmargin, hΔ]
  refine ⟨⟨B, k, he, hacc, hr, htk ▸ Ws.fresh, hbound⟩, ?_⟩
  have hPs : B.slot = Ws.slot := by
    have h1 : Q.params.ts B.slot = Q.params.ts Ws.slot :=
      ((Q.params.slotTime_eq _).symm.trans he.2.2.symm).trans htk
    have h2 := (SA.ts_le_iff Q.params).1 h1.le
    have h3 := (SA.ts_le_iff Q.params).1 h1.ge
    exact_mod_cast le_antisymm h2 h3
  have hhold : B.proposer ∈ Q.keys (Q.params.ts Ws.slot + Q.params.Δ) := hBp ▸ Ws.hold
  -- the finite inputs of the read at `t_u + 6Δ`
  have hc := healthy_repair_catch_at S A V Q'
  have hfresh := Ws.fresh
  have hq : Dprep.query < Q.params.ts Ws.slot := by
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
  have hlocks : ∀ y j ell, y ∈ Q.keys (Q.trace.time j) →
      SA.UpdateAt Q.trace.projAC y j Ws.slot ell →
      ∃ e, Ws.slot + 2 ≤ e ∧ (⟨B.root, Ws.slot, true, e⟩ : SA.Lock) ∈
        (Q.trace.projAC.post j).locks :=
    fun y j ell hy hup => Healing.Growing.operational_update_fresh_lock_at Dprep.reset hc hhold
      hBp he hPs hR hgu hTb hy hup
  have hread := Healing.Growing.operational_proposal_read_after_at Dprep.reset hc hhold hBp he
    hPs hR hgu hTb hlocks
  -- readiness and end-of-time cuts at `T = t_u + 6Δ` and at the deadline
  have hhT : Q'.heal ≤ Q.params.ts Ws.slot + 6 * Q.params.Δ := by
    change Q'.heal ≤ Q.query at ht
    linarith only [ht, hfresh, hΔ]
  have hrT : Q'.ready ≤ Q.params.ts Ws.slot + 6 * Q.params.Δ := hrh.trans hhT
  have hT0 : 0 ≤ Q.params.ts Ws.slot + 6 * Q.params.Δ := h0.trans hhT
  intro y j hy hj
  have hhonD : Q.run.2.point.HonestAt (Q.run.2.key y) Q.deadline := by
    have h := (mem_honestKeysAt_iff S Q.run.2 _ y).mp hy.1
    rwa [min_eq_left Q.bounded] at h
  have hhonT : Q.run.2.point.HonestAt (Q.run.2.key y) (Q.params.ts Ws.slot + 6 * Q.params.Δ) :=
    fun h => hhonD (Q.run.2.point.faultyAt_mono hmargin h)
  have hvT := confirmed_ready_of_healthy_at S A V Q hh hhonT hrT hTb
  have hvD := confirmed_ready_of_healthy_at S A V Q hh hhonD (hrT.trans hmargin) Q.bounded
  obtain ⟨hcT, hnT, htT, hlT⟩ := confirmed_end_cut_at S A V Q hT0 hTb hvT
  obtain ⟨hcD, hnD, htD, hlD⟩ := confirmed_end_cut_at S A V Q (hT0.trans hmargin) Q.bounded hvD
  obtain rfl := confirmed_cutAfter_unique S A V Q hj hcD
  have hyT : y ∈ Q.keys (Q.params.ts Ws.slot + 6 * Q.params.Δ) := by
    rw [mem_honestKeysAt_iff, min_eq_left hTb]
    exact hhonT
  have hfirst := hread y _ hyT hcT
  have hanc := healthy_cut_tips_ancestor_at S A V Q' h0 hb hp'
    (Q.run.2.key y) ((chainTrace Q.run.2).endCut (Q.params.ts Ws.slot + 6 * Q.params.Δ))
    ((chainTrace Q.run.2).endCut Q.deadline) ⟨hlT, by rw [htT]; exact hhT⟩
    (Nat.le_findGreatest hlT (by rw [htT]; exact hmargin))
    ⟨hlD, by rw [htD]; exact hhT.trans hmargin⟩
    (by rw [htT]; exact hvT) (by rw [htD]; exact hvD)
  rw [hnT, hnD, readAfter_lastOwn S A V Q hlT, readAfter_lastOwn S A V Q hlD,
    show Q.run.2.ownKey (Q.run.2.key y) = y from Q.run.2.key.symm_apply_apply _] at hanc
  exact hfirst.trans hanc

end Consensus.Goldilocks.Obligations.Growing

end
