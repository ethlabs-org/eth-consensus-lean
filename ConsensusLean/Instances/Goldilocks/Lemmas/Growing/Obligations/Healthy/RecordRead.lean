module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.MatureOrAnchor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CurrentChecks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Opening
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Windows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResetSuppliers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRepairTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The current-record read of a healthy reader under growing faults

An engine reader ready from the heal point is read at the trace cut after its last own event, at
its stored clock `t` (`engine_read_point`), past the repair reserve:

* `healthy_read_label_at`: after the drain, the latest view is a label after the reset whose
  voting time is before `t`;
* `healthy_current_read_context_at`: the read context at that read point (the prefix windows from
  the reset through `t`, the fault bound at `t`, the reader awake and joined at `t`);
* `healthy_current_record_read_at`: the read is the effective record, from the live candidates,
  the live chain and the mature-or-anchor source (with the reader's updates due by `t`, before its
  read cut) through `read_eq_record_of_current_votes_at`. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

section Trace

variable {sp : AC.ACParams}
  {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- A label `2k + 1` past a clean label is `k + 2` past it. -/
private theorem clean_add_k_two_le {c k s : Nat} (hk : 2 ≤ k) (h : c + 2 * k + 1 ≤ s) :
    c + k + 2 ≤ s := by
  omega

/-- After the drain, the latest view is a natural label beyond the reset, and its voting time is
no later than the read. -/
private theorem healthy_read_label_at (D : RepairSchedule tr H proposer dg g b cm βK)
    (ac : AC.ACState sp.n) (frame : AC.Frm sp.n (List (FG.Att sp.n)))
    {t : Time} (ht0 : 0 ≤ t) (ht : Healing.drainTime sp D.resetTime ≤ t) :
    ∃ L : Nat, (L : Int) = (AC.latestView sp ac frame t).2 ∧
      D.resetTime ≤ sp.ts L ∧ sp.ts L + sp.Δ ≤ t := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hslot : (sp.slot D.resetTime + 2 * sp.k + 5 : Nat) ≤ sp.slot t := by
    rw [Healing.drainTime_eq] at ht
    exact_mod_cast (AC.ts_le_iff_le_slot sp ht0 _).mp ht
  have hslot1 : sp.slot D.resetTime + 1 ≤ sp.slot t - 1 := by omega
  have hpos : 0 < sp.slot t := (Nat.succ_pos _).trans_le (hslot1.trans (Nat.sub_le _ _))
  have ha0 : 0 ≤ D.resetTime := by
    obtain ⟨⟨_, k, _, _, _, _, he⟩, _⟩ := D.reset.reset
    exact he ▸ D.reset.run.time_nonneg k
  have ha : D.resetTime < sp.ts (sp.slot D.resetTime + 1 : Nat) := by
    have hh := Int.lt_ediv_add_one_mul_self D.resetTime
      (by linarith only [hΔ] : 0 < 4 * sp.Δ)
    rw [← AC.slot_eq sp ha0] at hh
    rw [AC.ACParams.ts, mul_comm]; exact_mod_cast hh
  have htlo := (AC.ts_le_iff_le_slot sp ht0 (sp.slot t)).mpr le_rfl
  by_cases hphase : sp.ts (sp.slot t) + 2 * sp.Δ ≤ t
  · refine ⟨sp.slot t, ?_, ?_, by linarith only [hphase, hΔ]⟩
    · simp only [AC.latestView, ite_eq_left hphase]
    · exact ha.le.trans ((AC.ts_le_iff sp).mpr
        (by exact_mod_cast hslot1.trans (Nat.sub_le _ _)))
  · refine ⟨sp.slot t - 1, ?_, ?_, ?_⟩
    · simp only [AC.latestView, ite_eq_right hphase]
      exact Nat.cast_pred hpos
    · exact ha.le.trans ((AC.ts_le_iff sp).mpr (by exact_mod_cast hslot1))
    · have hs : ((sp.slot t - 1 : Nat) : Int) = (sp.slot t : Int) - 1 :=
        Nat.cast_pred hpos
      simp only [AC.ACParams.ts] at htlo ⊢
      rw [hs]
      linarith only [htlo, hΔ]

/-- **The current-record read** at a read point of a read context after a repaired opening: with
the reader's updates of labels past the join due by its read time made before its read cut, the
read is its effective record, from the live candidates, the live chain and the mature-or-anchor
source through `read_eq_record_of_current_votes_at`. -/
theorem current_record_read_of_context_at (D : RepairSchedule tr H proposer dg g b cm βK)
    {O : RepairOpening D} {y : Fin sp.n} {n : Nat} {t : Time} (C : RepairReadContext D O y n t)
    (hupd : ∀ u : Nat, sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u →
      sp.ts u + 6 * sp.Δ ≤ t → sp.ts u + 6 * sp.Δ < tr.time n →
      ∃ j ell, AC.UpdateAt tr.projAC y j u ell ∧ j < n) :
    Regimes.readAfter tr y n t =
      (AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F := by
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hΦ : FrameOK (Node.frame (tr.state y n)) := by
    have h := Compose.frameOK_state (hrun.upTo C.time_nonneg).toLocalRun C.honest n
    rwa [Trace.upTo_state tr _ C.readPoint.1] at h
  refine read_eq_record_of_current_votes_at hrun hnc C.time_nonneg C.honest C.readPoint C.awake
    C.joined C.sync C.catchup C.latest C.reset_le (fun R hR =>
      ⟨healthy_current_live_candidates_at D C hR, ?_⟩)
      D.reset.committeeFacts C.label_le C.fault
  by_cases hc : Healing.Growing.HighSourceCover tr H g D.resetTime b
  · apply read_source_of_healed_result_at D.reset
      (rL := Healing.Growing.healedLockFloor sp D.resetTime)
      (rO := Healing.Growing.healedOriginFloor sp D.resetTime)
      (fun _ => Compose.Growing.healedVotesBelow_iff.mpr
        (fun B s hB z q e hv hqb hs _ => hc.s2 B s hB z q e hv hqb hs)) C.time_bound
    by_cases hfc : (Node.frame (tr.state y n)).Anc R (Node.frame (tr.state y n)).F
    · exact Or.inl (hfc.trans ((AC.anc_getAnchor hΦ (healthy_current_live_chain_at D C)).2 _
        (Or.inr rfl)))
    rcases healthy_current_mature_or_anchor_at D C hupd hR with
      ha | ⟨x, r, s, B, CV, hx, hr, hRB, hrb, hs, hlate, hL⟩
    · exact Or.inl ha
    have hfloor : Healing.Growing.healedOriginFloor sp D.resetTime ≤ s := by
      change Healing.cleanLabel sp D.resetTime + sp.k + 2 + sp.k - 1 ≤ s
      rw [← D.cleanLabel_eq]
      omega
    exact Or.inr ⟨healthy_current_record_viable_at D C hx hr hRB hrb hs hL hfc hR,
      x, r, s, B, CV, hx, hr, hRB, hrb, hfloor, hL⟩
  apply read_source_of_recent_result_at D.reset C.time_bound
  by_cases hfc : (Node.frame (tr.state y n)).Anc R (Node.frame (tr.state y n)).F
  · exact Or.inl (hfc.trans ((AC.anc_getAnchor hΦ (healthy_current_live_chain_at D C)).2 _
      (Or.inr rfl)))
  rcases healthy_current_mature_or_anchor_at D C hupd hR with
    ha | ⟨x, r, s, B, CV, hx, hr, hRB, hrb, hs, hlate, hL⟩
  · exact Or.inl ha
  exact Or.inr ⟨healthy_current_record_viable_at D C hx hr hRB hrb hs hL hfc hR,
    x, r, s, B, CV, hx, hr, hRB, hrb, hs, hL,
    healthy_current_vote_domain_of_quarantine_at D hx hr hRB hrb
      (clean_add_k_two_le sp.two_le_k hlate)
      (fun Dd hD => (D.reset.deepCover Dd hD).resolve_right hc),
    healthy_current_stored_locks_at D hx hr hRB hrb hlate⟩

/-- **The read context** at a read point `(n, t)` by the horizon of a reader honest at `t` and
awake over its catch-up window `[t − c − 1, t]` (`c + 1 ≥ 8Δ`), at or after the opening's
update, whose read cut is after the update: the latest view is a label after the reset voted on
by `t`, the reader is awake and joined at `t`, the reset's windows serve the prefix through `t`,
and the latest label's committee fault bound is charged at `t`. -/
theorem repair_read_context_at (D : RepairSchedule tr H proposer dg g b cm βK)
    (O : RepairOpening D) {y : Fin sp.n} {n : Nat} {t c : Time}
    (hrp : Regimes.ReadPoint tr n t) (ht0 : 0 ≤ t) (htb : t ≤ b) (hy : y ∈ H t)
    (hc : 8 * sp.Δ ≤ c + 1) (hawake : ∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → tr.awake y u)
    (hrep : sp.ts O.slot + 6 * sp.Δ ≤ t) (hcut : sp.ts O.slot + 6 * sp.Δ < tr.time n) :
    Nonempty (RepairReadContext D O y n t) := by
  have hΔ := sp.toParams.hΔ
  have hdrain : Healing.drainTime sp D.resetTime ≤ t := by linarith only [O.drain, hrep, hΔ]
  obtain ⟨L, hL, haL, hLt⟩ := healthy_read_label_at D (tr.state y n).ac
    (Node.frame (tr.state y n)) ht0 hdrain
  obtain ⟨hw, hj⟩ := ready_implies_joined_at D.reset.run.toLocalRun hy ht0 hc hawake
  have hca := D.reset.cutZ_lt_reset_at
  obtain ⟨hsync, hcatch⟩ := D.reset.windows_at_reset_at ht0 htb
  have hgL : AC.gbar g ≤ sp.ts L := by
    have := Healing.lt_cutZ sp g
    linarith only [this, hca, haL, hΔ]
  have hfault := Healing.Growing.KernelProof.faultBoundK_late_at D.reset hgL
    (by linarith only [hLt, htb, hΔ]) (by linarith only [hca, haL, hΔ]) hLt htb
  exact ⟨{ label := L
           time_nonneg := ht0
           time_bound := htb
           repaired := hrep
           repairedCut := hcut
           readPoint := hrp
           honest := hy
           awake := hw
           joined := hj
           latest := hL
           reset_le := haL
           label_le := hLt
           sync := hsync
           catchup := hcatch
           fault := hfault }⟩

end Trace

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The read point of a ready engine reader from the heal point, with its catch-up `cDur - 1`
read at its stored clock, past the repair reserve. -/
private theorem healthy_engine_read_point_at {Q : HealthyPreparationQueryAt S A V}
    (D : HealthyRepairScheduleAt S A V Q) {v : V} {i : Nat}
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    Regimes.ReadPoint Q.trace (cutMap S Q.run.2 Q.hn
      (lastOwn S Q.run.2 v i))
        (stateAt S Q.run.2 Q.hn v i).now ∧
      0 ≤ (stateAt S Q.run.2 Q.hn v i).now ∧
      (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon ∧
      Regimes.Growing.ReadyAt Q.trace Q.keys
        ((Sys (goldilocks S) V).cDur (K S A) Q.run - 1)
        (Q.run.2.ownKey v) (stateAt S Q.run.2 Q.hn v i).now ∧
      D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ <
          (stateAt S Q.run.2 Q.hn v i).now := by
  have hΔ := Q.params.toParams.hΔ
  have hΔ1 : 1 ≤ Q.params.Δ := hΔ
  have hc : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run - 1 := by
    linarith only [(healthy_repair_lower S A V Q.run Q.hn Q.gst D.resetTime).1, hΔ1]
  have hr : Q.run.2.point.Ready
      (((Sys (goldilocks S) V).cDur (K S A) Q.run - 1) + 1) v
      (Q.run.2.cutTime i) := by simpa only [sub_add_cancel, chainTrace] using hv
  obtain ⟨hrp, h0, hh, hra, -⟩ := engine_read_point
    S Q.run.2 Q.hn Q.valid hc hi.1 hr
  have hlag := stored_now_ge_cutTime_sub_one
    S Q.run.2 Q.hn Q.valid hi.1 hc hr
  have hhi : Q.heal ≤ Q.run.2.cutTime i := hi.2
  exact ⟨hrp, h0, hh, hra, by linarith only [D.reserve, hhi, hlag]⟩

/-- **The read context** of a ready engine reader from the heal point, at its read point within
the query's bound. -/
theorem healthy_current_read_context_at (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) (O : HealthyRepairOpeningAt S A V Q D) {v : V} {i : Nat}
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (htb : (stateAt S Q.run.2 Q.hn v i).now ≤ Q.bound) :
    Nonempty (RepairReadContext D.toRepairSchedule O.toRepairOpening (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i))
          (stateAt S Q.run.2 Q.hn v i).now) := by
  obtain ⟨hrp, ht0, -, hra, hrep⟩ := healthy_engine_read_point_at S A V D hi hv
  have hΔ := Q.params.toParams.hΔ
  have hT : Q.params.ts O.slot + 6 * Q.params.Δ < (stateAt S Q.run.2 Q.hn v i).now := by
    have hb := O.bounded
    rw [add_mul, ← add_assoc] at hrep
    linarith only [hb, hrep]
  refine repair_read_context_at D.toRepairSchedule O.toRepairOpening hrp ht0 htb hra.1
    (by linarith only [(healthy_repair_lower S A V Q.run Q.hn Q.gst D.resetTime).1, hΔ]) hra.2
    hT.le (hT.trans_le hrp.2)

/-- **The current-record read**: a ready engine reader from the heal point, read at its read
point within the query's bound, reads its effective record; its updates are due by its stored
clock (`update_before_stored_clock_at`). -/
theorem healthy_current_record_read_at
    (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q)
    (O : HealthyRepairOpeningAt S A V Q D) {v : V} {i : Nat}
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (htb : (stateAt S Q.run.2 Q.hn v i).now ≤ Q.bound) :
    Regimes.readAfter Q.trace (Q.run.2.ownKey v)
        (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i))
        (stateAt S Q.run.2 Q.hn v i).now =
      (AC.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i))))
        (Q.trace.state (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i))).ac.latestConfirmed).getD
        (Q.trace.state (Q.run.2.ownKey v)
          (cutMap S Q.run.2 Q.hn (lastOwn S Q.run.2 v i))).fg.F := by
  obtain ⟨C⟩ := healthy_current_read_context_at S A V Q D O hi hv htb
  have hhon : v ∉ Q.run.2.faultyAt (stateAt S Q.run.2 Q.hn v i).now :=
    fun h =>
      hv.1 (Q.run.2.faultyAt_mono
        (now_bounds_cut S Q.run.2 Q.hn Q.valid v hi.1).2 h)
  exact current_record_read_of_context_at D.toRepairSchedule C fun u hslot ht _ =>
    update_before_stored_clock_at S Q.run.2 Q.hn Q.valid D.reset Q.bound_le hhon hslot ht
      C.time_bound

end Consensus.Goldilocks.Obligations.Growing

end
