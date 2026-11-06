module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyResetEnvelope
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRecordWriters
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.CoefficientAdapters
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NetworkTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Accountable
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Current healthy reads and healed safety -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Coverage of the effective current record, not recency of its own setter.
Maturity and anchor geometry are separate read-certificate obligations. -/
def HealthyRecordCover (Q : HealthyPreparationQuery S A V) (cleanLabel : Nat)
    (y : Fin Q.params.n) (n : Nat) (R : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  R = (Q.trace.state y n).fg.F ∨ ∃ x ∈ honestKeys S Q.run.2, ∃ q s C CV,
    q < n ∧ Q.trace.time q ≤ Q.run.2.horizon ∧ cleanLabel + 2 * Q.params.k + 1 ≤ s ∧
    (SA.ResultAt Q.trace.projAC x q s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R C

/-- A label `2k + 1` past a clean label is `k + 2` past it. -/
private theorem clean_add_k_two_le {c k s : Nat} (hk : 2 ≤ k) (h : c + 2 * k + 1 ≤ s) :
    c + k + 2 ≤ s := by
  omega

/-- The fault bound of a repair schedule, at the quorum arithmetic of the protocol. -/
private theorem healthy_faults_lt_quorum (Q : HealthyPreparationQuery S A V)
    (D : HealthyRepairSchedule S A V Q) :
    (honestKeys S Q.run.2)ᶜ.ncard < 2 * Q.params.toParams.q - Q.params.n := by
  have hf := D.reset.faults
  have hn := Q.hn
  change (honestKeys S Q.run.2)ᶜ.ncard < 2 * ((2 * Fintype.card V + 2) / 3) - Fintype.card V
  change 3 * (honestKeys S Q.run.2)ᶜ.ncard ≤ Fintype.card V - 1 at hf
  omega

section EndpointProducers
variable (Q : HealthyPreparationQuery S A V)
  (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
  (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
    Q.ready Q.heal Q.run)
  (W : HealthyBaseTiming S A V Q)
  (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
    HealthyStateFacts S A V Q W.slot k)

include h0 hb hp W states

set_option linter.unusedSectionVars false in
/-- Immediate receiver repair transports to the current record, independently of read geometry. -/
theorem healthy_current_record_sources (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    HealthyRecordCover S A V Q D.cleanLabel (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
      ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) := by
  rcases healthy_current_record_sources_before_now S A V Q h0 hb hp W states D O hrepair hi hv with
    hF | ⟨x, hx, q, s, B, CV, hq, ht, hs, hB, hRB⟩
  · exact Or.inl hF
  · have hbound : Q.trace.time q ≤ Q.run.2.horizon := by
      apply healthy_query_call_time_le S A V Q
      rcases hB with ⟨ell, hu, _⟩ | ⟨ell, A, ho, _⟩
      · exact ⟨_, Compose.projAC_callAt.mp hu.1⟩
      · exact ⟨_, Compose.projAC_callAt.mp ho.1⟩
    exact Or.inr ⟨x, hx, q, s, B, CV, hq, hbound, hs, hB, hRB⟩

omit h0 hb hp W states in
/-- The representative of a healthy stored-clock read is after the repair deadline,
including observations at heal before the reader's same-time tick. -/
theorem healthy_read_representative (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    ∃ q ≤ Q.run.2.events.length,
      Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i) =
        Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q) ∧
      Regimes.ReadPoint Q.trace (cutMap S Q.run.2 Q.hn q) (stateAt S Q.run.2 Q.hn v i).now ∧
      0 ≤ (stateAt S Q.run.2 Q.hn v i).now ∧
      (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon ∧
      D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ <
        (stateAt S Q.run.2 Q.hn v i).now ∧
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (goldilocks S) V).cDur (K S A) Q.run - 1) (Q.run.2.ownKey v)
        (stateAt S Q.run.2 Q.hn v i).now := by
  have hi' : i ≤ Q.run.2.events.length := hi.1
  have hc : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run - 1 := by
    have hd := D.duration_bound
    have hΔ := Q.params.toParams.hΔ
    change 0 < Q.params.Δ at hΔ
    have hΔ1 : 1 ≤ Q.params.Δ := hΔ
    linarith only [hd, hΔ1]
  have hr : Q.run.2.point.Ready (((Sys (goldilocks S) V).cDur (K S A) Q.run - 1) + 1)
      v (Q.run.2.cutTime i) := by simpa only [sub_add_cancel, chainTrace] using hv
  have hlag := stored_now_ge_cutTime_sub_one S Q.run.2 Q.hn Q.valid hi.1 hc hr
  have hfloor : D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ <
      (stateAt S Q.run.2 Q.hn v i).now := by
    have hh : Q.heal ≤ Q.run.2.cutTime i := hi.2
    linarith only [D.reserve, hh, hlag]
  have ht0 := (now_bounds_cut S Q.run.2 Q.hn Q.valid v hi.1).1
  obtain ⟨q, hq, hs, hrp, hth⟩ : ∃ q ≤ Q.run.2.events.length,
      stateAt S Q.run.2 Q.hn v i = stateAt S Q.run.2 Q.hn v q ∧
      Regimes.ReadPoint Q.trace (cutMap S Q.run.2 Q.hn q)
        (stateAt S Q.run.2 Q.hn v i).now ∧
      (stateAt S Q.run.2 Q.hn v i).now ≤ Q.run.2.horizon := by
    rcases stateAt_last_local_event S Q.run.2 Q.hn Q.valid v i with hs | ⟨j, hj, e, he, hev, hs, ht⟩
    · refine ⟨0, Nat.zero_le _, hs, ?_, ?_⟩
      · rw [hs, cutMap_zero, stateAt_eq]
        exact ⟨fun k hk => absurd hk (Nat.not_lt_zero k), D.reset.run.time_nonneg 0⟩
      · rw [hs, stateAt_eq]
        exact Q.valid.horizon_nonneg
    · refine ⟨j + 1, hj.trans_le hi', hs, ?_, ?_⟩
      · rw [ht]
        exact readPoint_after_event S Q.run.2 Q.hn Q.valid he
      · rw [ht]
        exact (Q.valid.in_horizon e (List.mem_of_getElem? he)).2
  refine ⟨q, hq, ?_, hrp, ht0, hth, hfloor, ?_⟩
  · rw [← simTrace_state S Q.run.2 Q.hn Q.valid v hv.1 i hi.1,
      ← simTrace_state S Q.run.2 Q.hn Q.valid v hv.1 q hq, hs]
  · exact ready_transport S Q.run.2 Q.hn Q.valid ht0 hth
      (ready_at_stored_now S Q.run.2 Q.hn Q.valid hi.1 hc hr)

omit h0 hb hp W states in
/-- After drain, the latest view is a natural label beyond the reset, and its
voting time is no later than the read. -/
theorem healthy_read_label (D : HealthyRepairSchedule S A V Q)
    (ac : SA.SAState Q.params.n) (frame : SA.Frm Q.params.n (List (FG.Att Q.params.n)))
    {t : Time} (ht0 : 0 ≤ t)
    (ht : Healing.drainTime Q.params D.resetTime ≤ t) :
    ∃ L : Nat, (L : Int) = (SA.latestView Q.params ac frame t).2 ∧
      D.resetTime ≤ Q.params.ts L ∧ Q.params.ts L + Q.params.Δ ≤ t := by
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hslot : (Q.params.slot D.resetTime + 2 * Q.params.k + 5 : Nat) ≤ Q.params.slot t := by
    rw [Healing.drainTime_eq] at ht
    exact_mod_cast (SA.ts_le_iff_le_slot Q.params ht0 _).mp ht
  have hslot1 : Q.params.slot D.resetTime + 1 ≤ Q.params.slot t - 1 := by omega
  have hpos : 0 < Q.params.slot t := (Nat.succ_pos _).trans_le (hslot1.trans (Nat.sub_le _ _))
  have ha0 : 0 ≤ D.resetTime := by
    obtain ⟨⟨y, hy, k, att, hk, _, he⟩, _⟩ := D.reset.reset
    exact he ▸ D.reset.run.time_nonneg k
  have ha : D.resetTime < Q.params.ts (Q.params.slot D.resetTime + 1 : Nat) := by
    have hh := Int.lt_ediv_add_one_mul_self D.resetTime
      (by linarith only [hΔ] : 0 < 4 * Q.params.Δ)
    rw [← SA.slot_eq Q.params ha0] at hh
    rw [SA.SAParams.ts, mul_comm]; exact_mod_cast hh
  have htlo := (SA.ts_le_iff_le_slot Q.params ht0 (Q.params.slot t)).mpr le_rfl
  by_cases hphase : Q.params.ts (Q.params.slot t) + 2 * Q.params.Δ ≤ t
  · refine ⟨Q.params.slot t, ?_, ?_, by linarith only [hphase, hΔ]⟩
    · simp only [SA.latestView, ite_eq_left hphase]
    · exact ha.le.trans ((SA.ts_le_iff Q.params).mpr
        (by exact_mod_cast hslot1.trans (Nat.sub_le _ _)))
  · refine ⟨Q.params.slot t - 1, ?_, ?_, ?_⟩
    · simp only [SA.latestView, ite_eq_right hphase]
      exact Nat.cast_pred hpos
    · exact ha.le.trans ((SA.ts_le_iff Q.params).mpr (by exact_mod_cast hslot1))
    · have hs : ((Q.params.slot t - 1 : Nat) : Int) = (Q.params.slot t : Int) - 1 :=
        Nat.cast_pred hpos
      simp only [SA.SAParams.ts] at htlo ⊢
      rw [hs]
      linarith only [htlo, hΔ]

set_option linter.unusedSectionVars false in
/-- The original progress interval supplies an actual opening; finite catch and
operational selection then repair every ready receiver without read geometry. -/
theorem healthy_bounded_repairing_opening (D : HealthyRepairSchedule S A V Q) :
    ∃ O : HealthyRepairOpening S A V Q D, HealthyReceiverRepair S A V Q D O := by
  classical
  have hcap : Q.cap ≠ .final := by rcases Q.nonfinal with h | h <;> simp [h]
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (goldilocks S (Model.pubOf Q.run.1)).skel.grid
      ⟨Pattern.single, Q.index⟩ ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      Q.ready Q.heal := by
    simpa only [System.prog, shapeProgress, shapeHolds, goldilocksContract, ite_eq_right hcap,
      Model.sysExternal, System.cDur, System.pt, Sys, Model.sysOf, Model.Run.point] using hp
  have hq0 : 0 ≤ D.query := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))
  have hq : max Q.ready 0 ≤ D.query := max_le ((le_max_left _ _).trans D.lower) hq0
  have hd := Q.params.toParams.hΔ
  have hwin : D.query + (Q.index : Time) * (4 * Q.params.Δ) ≤ Q.heal := by
    linarith only [D.reserve, hd]
  obtain ⟨s, hlo, hhi, hr⟩ := hrec D.query hq
    hwin (hwin.trans hb)
  have htime : (goldilocks S (Model.pubOf Q.run.1)).skel.grid.slotTime s = Q.params.ts s := by
    change (s : Time) * (4 * Q.run.1.ΔAC) = 4 * Q.run.1.ΔAC * s
    ring
  rw [htime] at hlo hhi
  have hbound : Q.params.ts s ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ := by
    change Q.params.ts s ≤ D.query + (Q.index : Time) * (4 * Q.params.Δ) at hhi
    linarith only [hhi]
  have hsb : Q.params.ts s ≤ Q.run.2.horizon := by linarith only [hbound, D.reserve, hb, hd]
  have hready := hr 0 (by simp [Pattern.single])
  simp only [Nat.add_zero] at hready
  have hmem : runProposer S Q.run.2 Q.hn s ∈ Q.run.2.sel (.proposer s) := by
    simp only [runProposer_eq, dite_eq_left hready.1]
    exact Finset.min'_mem _ _
  have hR := hready.2 _ hmem
  rw [htime] at hR
  have hnode := ready_transport S Q.run.2 Q.hn Q.valid (hq0.trans hlo.le) hsb hR
  rw [show Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn s)) =
    runProposer S Q.run.2 Q.hn s from Q.run.2.key.symm_apply_apply _] at hnode
  have hold : D.oldLabel < s := by
    exact_mod_cast (SA.ts_lt_iff Q.params).mp
      (lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans D.lower))) hlo)
  have hshort : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) (Regimes.catchUp Q.params)
      (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) := by
    refine ⟨hnode.1, fun t ht hts => hnode.2 t ?_ hts⟩
    apply le_trans _ ht
    apply max_le_max_left
    have : Regimes.catchUp Q.params ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run := by
      simpa only [Regimes.catchUp] using D.duration_bound
    linarith only [this]
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision
  obtain ⟨k, P, hP, ht⟩ := Regimes.ready_proposer_proposes hrun hnc (s := s)
    (Nat.zero_le D.oldLabel |>.trans_lt hold) hshort
  have hlabel : P.slot = s := by
    have := hP.2.2
    rw [ht] at this
    rw [Q.params.slotTime_eq] at this
    have he : (P.slot : Time) = (s : Time) := by
      simp only [SA.SAParams.ts] at this
      exact (mul_left_cancel₀ (mul_pos (by norm_num : (0 : Time) < 4) hd).ne' this).symm
    exact_mod_cast he
  let O : HealthyRepairOpening S A V Q D :=
    ⟨s, k, P, hlo, hbound, hold, hlabel, hP, Compose.proposal_accepted hrun hnc hnode.1 hP,
      ht, hnode⟩
  exact ⟨O, healthy_receiver_repair_of_opening S A V Q hb D O (healthy_repair_catch S A V Q)⟩

omit h0 hb hp W states in
/-- A time past the repair reserve of a query is past the query. -/
private theorem healthy_lt_of_reserve {q t : Time}
    (h : q + (4 * (Q.index : Time) + 6) * Q.params.Δ < t) : q < t := by
  linarith only [h, mul_nonneg (Int.natCast_nonneg Q.index) Q.params.toParams.hΔ.le,
    Q.params.toParams.hΔ]

omit h0 hb hp W states in
/-- The opening's update is before every repaired read. -/
private theorem healthy_opening_before_read {D : HealthyRepairSchedule S A V Q}
    (O : HealthyRepairOpening S A V Q D) {v : V} {i : Nat}
    (C : HealthyReadContext S A V Q D v i) :
    Q.params.ts O.slot + 6 * Q.params.Δ < (stateAt S Q.run.2 Q.hn v i).now := by
  linarith only [O.bounded, C.repaired]

omit h0 hb hp W states in
/-- The opening's slot is after the slot that follows the network's join time. -/
private theorem healthy_opening_join {D : HealthyRepairSchedule S A V Q}
    (O : HealthyRepairOpening S A V Q D) :
    Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤ Q.params.ts O.slot := by
  have hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts O.slot :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))).trans O.fresh.le
  have hbase := (SA.ts_le_iff_le_slot Q.params (SA.gbar_nonneg Q.gst)
    (Q.params.slot (SA.gbar Q.gst))).mpr le_rfl
  simp only [SA.SAParams.ts] at hbase hgu ⊢
  push_cast
  linarith only [hbase, hgu]

/-- Current anchor candidates are compatible with the current looked-up record. -/
theorem healthy_current_live_candidates (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (C : HealthyReadContext S A V Q D v i)
    {R : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
      (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.latestConfirmed = some R) :
    ∀ X ∈ SA.liveLockBlocks Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.locks
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now ∪
        {(Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).fcRoot},
      Goldilocks.Compatible (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree X R := by
  have hq := D.lower
  simp only [max_le_iff] at hq
  obtain ⟨_, hqd, _, hqg, hq0⟩ := hq
  have hΔ := Q.params.toParams.hΔ
  have htpos : 0 < (stateAt S Q.run.2 Q.hn v i).now :=
    hq0.trans_lt (healthy_lt_of_reserve S A V Q C.repaired)
  have hv : v ∈ Q.run.2.honest := by
    rcases stateAt_last_local_event S Q.run.2 Q.hn Q.valid v i with
      hs | ⟨j, _, e, he, hev, _, _⟩
    · rw [hs, stateAt_eq] at htpos
      change 0 < (0 : Time) at htpos
      exact (lt_irrefl (0 : Time) htpos).elim
    · exact hev ▸ Q.valid.honest_only e (List.mem_of_getElem? he)
  have hy := honest_ownKey (S := S) hv
  have hc := healthy_repair_catch S A V Q
  obtain ⟨O, _⟩ := healthy_bounded_repairing_opening S A V Q h0 hb hp W states D
  have hdrain := hqd.trans O.fresh.le
  have hgu := hqg.trans O.fresh.le
  have hbefore := healthy_opening_before_read S A V Q O C
  have hTb := hbefore.le.trans C.time_bound
  have hjoin := healthy_opening_join S A V Q O
  obtain ⟨j, ell, _, hup, _⟩ := D.reset.update_toFG_calls hy hjoin hTb
  have hjn : j < C.cut := by
    by_contra h
    have := C.readPoint.2.trans (D.reset.run.time_mono (Nat.le_of_not_gt h))
    have ht : Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ := hup.2.2.1
    linarith only [this, ht, hbefore]
  obtain ⟨x, hx, r, s, CV, hrn, hus, hsource⟩ :=
    UpTo.record_source_after_operational_update D.reset hc O.ready.1 rfl O.proposes O.label
      hdrain hgu hTb hy hup hjn hR
  have hrb := (C.readPoint.1 r hrn).trans C.time_bound
  have hs : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 1 ≤ s := by
    rw [← D.cleanLabel_eq]
    exact D.old_bound.trans (O.old_lt.le.trans hus)
  have hib : ∀ q < C.cut, Q.trace.time q ≤ Q.run.2.horizon :=
    fun q hq => (C.readPoint.1 q hq).trans C.time_bound
  have hU := D.reset.honest_coherent
  have hPhi := Compose.frameOK_state D.reset.run.toLocalRun hy C.cut
  have hsub : (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree ⊆
      Q.trace.HonestBlocks (honestKeys S Q.run.2) := fun X hX => ⟨_, hy, _, hX.1⟩
  have hRm := (SA.lookup_eq_some hR).1
  intro X hX
  rcases hX with hX | hX
  · have hdrainNow := hdrain.trans (show Q.params.ts O.slot ≤
        (stateAt S Q.run.2 Q.hn v i).now by linarith only [hbefore, hΔ])
    obtain ⟨l, hl, E, hE, hEr, hlive, rfl⟩ := SA.mem_liveLockBlocks_of_wf hPhi
      (Compose.locksWF_state D.reset.run D.reset.noColl hy C.cut) hX
    rw [← Compose.projAC_state D.reset.run.toLocalRun hy C.cut] at hl
    have hRE := D.reset.clean_source_stored_lock_compatible hc hx hy hsource hs hrb hib hl
      (Healing.drain_stored_lock_label hdrainNow hlive) (hsub hE) hEr
    have hXE := (SA.viableAncestor_anc hPhi hE).2.mono hsub
    have hXR := tips_comparable_of_origin_witnesses S A V Q hXE (.refl (a := R)) hRE.symm
    rcases hXR with h | h
    · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi hsub hX.1 h hRm)
    · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi hsub hRm h hX.1)
  · obtain rfl := Set.mem_singleton_iff.mp hX
    obtain ⟨z, q, l, B, hseed, hqb, _, _, hhold⟩ :=
      D.reset.reset_seed_held_at_read hc hy C.readPoint C.time_bound hdrain hgu hbefore
    have hcandidate := UpTo.guarded_seed_ancestor_candidate_at_state D.reset hy hib hRm
      hseed hqb hhold (D.reset.clean_source_compatible_high_origin hc hx hsource hs hrb hseed hqb)
      (fun z q l B hqn ho =>
        D.reset.clean_source_compatible_high_origin hc hx hsource hs hrb ho (hib q hqn))
    exact hcandidate.elim Or.inr (fun h => Or.inl h.2.1)

-- Keep the existing signature: operational repair supplies a fresh source, so
-- the independently supplied mature-result witness is not needed by this proof.
set_option linter.unusedVariables false in
/-- Current viability follows from the repaired record's clean source and guarded
reset-seed geometry, without strengthening the supplied mature-result witness. -/
theorem healthy_current_record_viable (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (C : HealthyReadContext S A V Q D v i)
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x r s CV}
    (hx : x ∈ honestKeys S Q.run.2) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B)
    (hrb : Q.trace.time r ≤ Q.run.2.horizon)
    (hs : Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s) (hL : s < C.label)
    (hfc : ¬ (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).Anc R
      (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).fcRoot)
    (hR : SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
      (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.latestConfirmed = some R) :
    R ∈ (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).viableTree
      (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree := by
  have hq0 : 0 ≤ D.query := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))
  have ht0 : 0 < (stateAt S Q.run.2 Q.hn v i).now :=
    hq0.trans_lt (healthy_lt_of_reserve S A V Q C.repaired)
  have hv : v ∈ Q.run.2.honest := by
    rcases stateAt_last_local_event S Q.run.2 Q.hn Q.valid v i with hinit |
      ⟨j, _, e, he, hev, _, _⟩
    · rw [hinit, stateAt_eq] at ht0
      change (0 : Time) < 0 at ht0
      exact (lt_irrefl (0 : Time) ht0).elim
    · exact hev ▸ Q.valid.honest_only e (List.mem_of_getElem? he)
  have hy := honest_ownKey (S := S) hv
  obtain ⟨O, _⟩ := healthy_bounded_repairing_opening S A V Q h0 hb hp W states D
  have hc := healthy_repair_catch S A V Q
  have hbefore := healthy_opening_before_read S A V Q O C
  have hTb := hbefore.le.trans C.time_bound
  have hdrain : Healing.drainTime Q.params D.resetTime ≤ Q.params.ts O.slot :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans D.lower)).trans O.fresh.le
  have hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts O.slot :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))).trans O.fresh.le
  have hjoin := healthy_opening_join S A V Q O
  obtain ⟨j, ell, _, hup, _⟩ := D.reset.update_toFG_calls hy hjoin hTb
  have hjtime : Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ := hup.2.2.1
  have hjn : j < C.cut := by
    by_contra h
    have := C.readPoint.2.trans (D.reset.run.time_mono (Nat.le_of_not_lt h))
    rw [hjtime] at this
    linarith only [this, hbefore]
  obtain ⟨z, hz, q, l, DV, hqn, hul, hsource⟩ :=
    UpTo.record_source_after_operational_update D.reset hc O.ready.1 rfl O.proposes O.label
      hdrain hgu hTb hy hup hjn hR
  have hclean : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 1 ≤ l := by
    rw [← D.cleanLabel_eq]
    exact D.old_bound.trans (O.old_lt.le.trans hul)
  have hbound : ∀ q < C.cut, Q.trace.time q ≤ Q.run.2.horizon :=
    fun q hq => (C.readPoint.1 q hq).trans C.time_bound
  obtain ⟨zS, qS, lS, S₀, hseed, hqb, _, _, hhold⟩ :=
    D.reset.reset_seed_held_at_read hc hy C.readPoint C.time_bound hdrain hgu hbefore
  have hcompare : ∀ z r l B, Q.trace.time r ≤ Q.run.2.horizon →
      Healing.HighOrigin Q.trace (honestKeys S Q.run.2) Q.gst z r l B →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B := by
    intro z r l B hrb ho
    exact D.reset.clean_source_compatible_high_origin hc hz hsource hclean (hbound q hqn) ho hrb
  rcases UpTo.guarded_seed_ancestor_candidate_at_state D.reset hy hbound
    (SA.lookup_eq_some hR).1 hseed hqb hhold (hcompare zS qS lS S₀ hqb hseed)
    (fun z r l B hrc ho => hcompare z r l B (hbound r hrc) ho) with hroot | hviable
  · exact False.elim (hfc hroot)
  · exact hviable

omit h0 hb hp W states in
/-- The vote-domain input `hdomain` of `Healing.ResetPremisesUpTo.late_result_prefix_votes_before`,
from the bounded actual-result theorem. -/
theorem healthy_current_vote_domain (D : HealthyRepairSchedule S A V Q)
    (hc : Healing.CatchRun Q.trace (honestKeys S Q.run.2) Q.gst (2 * Q.params.Δ))
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x r s CV}
    (hx : x ∈ honestKeys S Q.run.2) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B)
    (hrb : Q.trace.time r ≤ Q.run.2.horizon)
    (hs : D.cleanLabel + Q.params.k + 2 ≤ s) :
    ∀ z ∈ honestKeys S Q.run.2, ∀ q ell e, SA.CastAt Q.trace.projAC z q ell e →
      Q.trace.time q ≤ Q.run.2.horizon → s < e.msg.slot →
      (∀ w ∈ honestKeys S Q.run.2, ∀ p < q, ∀ e', SA.VoteAt Q.trace.projAC w p e' →
        s < e'.msg.slot → SA.VoteExtends (Q.trace.HonestBlocks (honestKeys S Q.run.2)) e'.msg R) →
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R ell.frame.fcRoot ∨
        R ∈ ell.frame.viableTree (SA.voterBlockTree Q.params e.readPoint ell.frame e.msg.slot) := by
  intro z hz q ell e he hqb hse hprior
  exact D.reset.result_prefix_vote_domain_before hc hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb he hse hqb hprior

-- Preserve the producer's existing section hypotheses although the finite adapter needs fewer.
set_option linter.unusedSectionVars false in
/-- Comparison against actually stored time-live locks at the first successor. -/
theorem healthy_current_stored_locks (D : HealthyRepairSchedule S A V Q)
    {R B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {x r s CV}
    (hx : x ∈ honestKeys S Q.run.2) (hr : SA.ResultAt Q.trace.projAC x r s B CV)
    (hRB : Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B)
    (hrb : Q.trace.time r ≤ Q.run.2.horizon)
    (hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s) :
    ∀ z ∈ honestKeys S Q.run.2, ∀ q ell e, SA.CastAt Q.trace.projAC z q ell e →
      Q.trace.time q ≤ Q.run.2.horizon → e.msg.slot = s + 1 →
      ∀ l ∈ (Q.trace.projAC.state z q).locks, Q.params.slot (Q.trace.time q) ≤ l.slot + Q.params.k →
        l.slot ≤ s → ∀ Y ∈ Q.trace.HonestBlocks (honestKeys S Q.run.2), Y.root = l.block →
          Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) Y R := by
  intro z hz q ell e he hqb hes
  have hrun := (Compose.goldilocks_ac_projection _ _ _ _ _ _
    D.reset.run D.reset.noColl).localRun
  have hslot := (SA.castAt_spec hrun hz he).2.1
  exact D.reset.result_prefix_stored_locks (healthy_repair_catch S A V Q) hx hz hr hRB
    (by simpa only [D.cleanLabel_eq] using hs) hrb hqb (by
      change s + 1 ≤ Q.params.slot (Q.trace.time q)
      change e.msg.slot = Q.params.slot (Q.trace.time q) at hslot
      exact (hes.symm.trans hslot).le)

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Stored-clock representative, repair floor and finite service producer.
The existing endpoint signature is retained; record repair is not needed for service. -/
theorem healthy_current_read_context (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) : Nonempty (HealthyReadContext S A V Q D v i) := by
  obtain ⟨q, hq, heq, hread, ht0, htb, hrepairTime, hready⟩ :=
    healthy_read_representative S A V Q D hi hv
  have hΔ := Q.params.toParams.hΔ
  have hquery : D.query ≤ (stateAt S Q.run.2 Q.hn v i).now :=
    (healthy_lt_of_reserve S A V Q hrepairTime).le
  have hdrain := (le_max_of_le_right (le_max_left _ _)).trans D.lower
  obtain ⟨L, hL, haL, hLt⟩ := healthy_read_label S A V Q D
    (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q)).ac
    (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn q)))
    ht0 (hdrain.trans hquery)
  have haw := Compose.ready_implies_joined Q.params _ _ _ _ _ D.reset.run
    (Q.run.2.ownKey v) (honest_ownKey (S := S) hv.1) _
    ((Sys (goldilocks S) V).cDur (K S A) Q.run - 1) ht0
    (by linarith only [D.duration_bound, hΔ]) hready.2
  have hza : Healing.cutZ Q.params.toParams Q.gst < D.resetTime :=
    Healing.cutZ_lt_reset_of_snapshot D.reset.run
      (by obtain ⟨k, hk, _⟩ := D.reset.snapshot; exact ⟨k, hk⟩) D.reset.reset
  exact ⟨{ cut := cutMap S Q.run.2 Q.hn q
           state_eq := heq
           label := L
           time_nonneg := ht0
           time_bound := htb
           repaired := hrepairTime
           readPoint := hread
           awake := haw.1
           joined := haw.2
           latest := hL
           reset_le := haL
           sync := Healing.sync_window_at_reset_of_reset_before D.reset htb
           catchup := Healing.catch_window_at_reset_of_reset_catch_before D.reset
             (healthy_repair_catch S A V Q) htb
           fault := Healing.fault_bound_late_before D.reset
             (by linarith only [hza, haL, hΔ]) (hLt.trans htb) }⟩

omit h0 hb hp W states in
/-- Normalized current live locks compare using their protected source provenance.
The endpoint supplies honesty from its ready-reader hypothesis. -/
theorem healthy_current_live_chain (D : HealthyRepairSchedule S A V Q)
    {v : V} {i : Nat} (hv : v ∈ Q.run.2.honest) (C : HealthyReadContext S A V Q D v i) :
    ∀ X ∈ SA.liveLockBlocks Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.locks
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now,
      ∀ Y ∈ SA.liveLockBlocks Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.locks
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now,
      Goldilocks.Compatible (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree X Y := by
  have hy := honest_ownKey (S := S) hv
  have hU := Compose.honest_blocks_coherent D.reset.run.toLocalRun D.reset.noColl
  have hPhi := (Store.frame_realization _ _ _ _
    (Compose.fg_reachable D.reset.run.toLocalRun hy C.cut)).1
  have hsub : (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).tree ⊆
      Q.trace.HonestBlocks (honestKeys S Q.run.2) := fun X hX => ⟨_, hy, _, hX.1⟩
  have hquery : D.query ≤ (stateAt S Q.run.2 Q.hn v i).now :=
    (healthy_lt_of_reserve S A V Q C.repaired).le
  have hdrain : Healing.drainTime Q.params D.resetTime ≤
      (stateAt S Q.run.2 Q.hn v i).now :=
    ((le_max_of_le_right (le_max_left _ _)).trans D.lower).trans hquery
  intro X hX Y hY
  have hwf := Compose.locksWF_state D.reset.run D.reset.noColl hy C.cut
  obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := SA.mem_liveLockBlocks_of_wf hPhi hwf hX
  obtain ⟨m, hm, E, hE, hEr, hmive, rfl⟩ := SA.mem_liveLockBlocks_of_wf hPhi hwf hY
  rw [← Compose.projAC_state D.reset.run.toLocalRun hy C.cut] at hl hm
  have hBE := D.reset.clean_stored_locks_compatible (healthy_repair_catch S A V Q) hy
    (fun q hq => (C.readPoint.1 q hq).trans C.time_bound) hl hm
    (Healing.drain_stored_lock_label hdrain hlive)
    (Healing.drain_stored_lock_label hdrain hmive) (hsub hB) hBr (hsub hE) hEr
  have hXB := (SA.viableAncestor_anc hPhi hB).2.mono hsub
  have hYE := (SA.viableAncestor_anc hPhi hE).2.mono hsub
  have hXY := tips_comparable_of_origin_witnesses S A V Q hXB hYE hBE
  rcases hXY with h | h
  · exact Or.inl (SA.anc_tree_of_anc_U hU hPhi hsub hX.1 h hY.1)
  · exact Or.inr (SA.anc_tree_of_anc_U hU hPhi hsub hY.1 h hX.1)

set_option linter.unusedSectionVars false in
-- The unchanged signature retains hrepair; the operational opening gives a stronger writer fact.
set_option linter.unusedVariables false in
/-- Actual anchor coverage or a mature raw witness. Young optimistic writers
retain their normalized lock until the next-result deadline. -/
theorem healthy_current_mature_or_anchor (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (C : HealthyReadContext S A V Q D v i)
    {R : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
      (Q.trace.state (Q.run.2.ownKey v) C.cut).ac.latestConfirmed = some R) :
    (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).Anc R
      (SA.getAnchor Q.params (Q.trace.state (Q.run.2.ownKey v) C.cut).ac
        (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut))
        (stateAt S Q.run.2 Q.hn v i).now) ∨
    ∃ x ∈ honestKeys S Q.run.2, ∃ r s B CV,
      SA.ResultAt Q.trace.projAC x r s B CV ∧
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R B ∧
      Q.trace.time r ≤ Q.run.2.horizon ∧ Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s ∧
      D.cleanLabel + 2 * Q.params.k + 1 ≤ s ∧ s < C.label := by
  let y := Q.run.2.ownKey v
  let n := C.cut
  let t := (stateAt S Q.run.2 Q.hn v i).now
  let U := Q.trace.HonestBlocks (honestKeys S Q.run.2)
  let Phi := Node.frame (Q.trace.state y n)
  have hΔ := Q.params.toParams.hΔ
  obtain ⟨hready, hdrain, hOld, hgu, hquery0⟩ :=
    (show Q.ready ≤ D.query ∧ Healing.drainTime Q.params D.resetTime ≤ D.query ∧
      Q.params.ts D.oldLabel ≤ D.query ∧ SA.gbar Q.gst + 4 * Q.params.Δ ≤ D.query ∧
      0 ≤ D.query by simpa only [max_le_iff] using D.lower)
  have ht0 : 0 < t := hquery0.trans_lt (healthy_lt_of_reserve S A V Q C.repaired)
  have hv : v ∈ Q.run.2.honest := by
    rcases stateAt_last_local_event S Q.run.2 Q.hn Q.valid v i with
      hinit | ⟨j, hji, e, he, hnode, hstate, htime⟩
    · have : t = 0 := by change (stateAt S Q.run.2 Q.hn v i).now = 0; rw [hinit, stateAt_eq]; rfl
      exact False.elim ((ne_of_gt ht0) this)
    · exact hnode ▸ Q.valid.honest_only e (List.mem_of_getElem? he)
  have hy : y ∈ honestKeys S Q.run.2 := honest_ownKey hv
  have hc := healthy_repair_catch S A V Q
  have hU := D.reset.honest_coherent
  have hPhi := Compose.frameOK_state D.reset.run.toLocalRun hy n
  obtain ⟨hRm, hRroot⟩ := SA.lookup_eq_some hR
  have hsub : Phi.tree ⊆ U := fun B hB => ⟨y, hy, n, hB.1⟩
  have hchain := healthy_current_live_chain S A V Q D hv C
  have hfc := (SA.anc_getAnchor hPhi hchain).2 _ (Or.inr rfl)
  have hfinal : Anc U R (Q.trace.state y n).fg.F →
      Phi.Anc R (SA.getAnchor Q.params (Q.trace.state y n).ac Phi t) := by
    intro hRF
    exact (SA.anc_tree_of_anc_U hU hPhi hsub hRm hRF hPhi.rooted.1).trans
      (hPhi.F_anc_fcRoot.trans hfc)
  by_cases hgen : R.root = Q.params.genesisRoot
  · left
    apply hfinal
    have htree := Store.accepted_tree _ _ _ _ (Compose.fg_reachable D.reset.run.toLocalRun hy n)
    have heq : R = Q.params.toParams.genesisBlock
        (goldilocksNode Q.params (S.ro _)).genesisPayload :=
      htree.2.1.1 hRm.1 htree.2.2.1 hgen
    rw [heq]
    exact (htree.2.2.2 _ hPhi.rooted.1.1).mono (Compose.fg_tree_subset_honest hy n)
  have hTt : Q.params.ts O.slot + 6 * Q.params.Δ < t :=
    healthy_opening_before_read S A V Q O C
  have hTb := hTt.le.trans C.time_bound
  have hjoin := healthy_opening_join S A V Q O
  obtain ⟨d, ellD, _, hup, _⟩ := D.reset.update_toFG_calls hy hjoin hTb
  have hdt : Q.trace.time d = Q.params.ts O.slot + 6 * Q.params.Δ := hup.2.2.1
  have hdn : d < n := by
    by_contra h
    have := C.readPoint.2.trans (D.reset.run.time_mono (Nat.le_of_not_lt h))
    rw [hdt] at this
    linarith only [this, hTt]
  obtain ⟨q, hqn, ell, hcall, hRq, hrest, hwriter⟩ :=
    last_record_writer D.reset.run D.reset.noColl hy hR hgen
  have hqt : Q.trace.time q ≤ t := C.readPoint.1 q hqn
  have hqb := hqt.trans C.time_bound
  have hslotq := UpTo.retained_writer_slot_after_update D.reset hc O.ready.1 rfl
    O.proposes O.label (hdrain.trans O.fresh.le) (hgu.trans O.fresh.le) hTb hy hup hdn
    hR hcall hRq hrest
  change O.slot ≤ Q.params.slot (Q.trace.time q) at hslotq
  have hframe : ∀ e, q ≤ e → e ≤ n → R ∈ (Node.frame (Q.trace.state y e)).tree :=
    fun e hqe hen => writer_mem_frame_between D.reset.run D.reset.noColl hy hqe hen
      ((Compose.frame_of_projAC D.reset.run hy hcall ▸ hRq).1) hRm
  have hraw : ∀ (x : Fin Q.params.n), x ∈ honestKeys S Q.run.2 → ∀ r s B CV,
      SA.ResultAt Q.trace.projAC x r s B CV → Anc U R B →
      Q.trace.time r ≤ t → D.cleanLabel + 2 * Q.params.k + 1 ≤ s →
      ∃ x ∈ honestKeys S Q.run.2, ∃ r s B CV,
        SA.ResultAt Q.trace.projAC x r s B CV ∧ Anc U R B ∧
        Q.trace.time r ≤ Q.run.2.horizon ∧
        Healing.cutZ Q.params.toParams Q.gst ≤ Q.params.ts s ∧
        D.cleanLabel + 2 * Q.params.k + 1 ≤ s ∧ s < C.label := by
    intro x hx r s B CV hres hRB hrt hs
    have htime : Q.trace.time r = Q.params.ts s + 6 * Q.params.Δ :=
      hres.choose_spec.1.2.2.1
    have hlatest := result_label_lt_latest_of_time C.time_nonneg (htime ▸ hrt)
      (A := (Q.trace.state y n).ac) (Φ := Phi)
    rw [← C.latest] at hlatest
    have hclean : Healing.cleanLabel Q.params D.resetTime + Q.params.k + 2 ≤ s := by
      rw [D.cleanLabel_eq] at hs
      exact clean_add_k_two_le Q.params.two_le_k hs
    have hwindow : (s : Int) - Q.params.k < s :=
      sub_lt_self _ (Int.natCast_pos.mpr (Nat.zero_lt_two.trans_le Q.params.two_le_k))
    exact ⟨x, hx, r, s, B, CV, hres, hRB, hrt.trans C.time_bound,
      D.reset.clean_window_timing hclean s hwindow, hs,
      by exact_mod_cast hlatest⟩
  rcases hwriter with ⟨s, CV, hres⟩ | ⟨⟨CV, hop⟩, hlock⟩
  · right
    have htime : Q.trace.time q = Q.params.ts s + 6 * Q.params.Δ :=
      hres.choose_spec.1.2.2.1
    have hslot : Q.params.slot (Q.trace.time q) = s + 1 := by
      rw [htime]
      apply SA.slot_of_mem Q.params (s + 1) <;>
        simp only [SA.SAParams.ts] <;> push_cast <;> linarith only [hΔ]
    apply hraw y hy q s R CV hres .refl hqt
    rw [hslot] at hslotq
    exact Nat.lt_succ_iff.mp (D.old_bound.trans_lt (O.old_lt.trans_le hslotq))
  · let s := Q.params.slot (Q.trace.time q)
    have hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s := by
      exact D.old_bound.trans (O.old_lt.le.trans hslotq)
    have hsc : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 1 ≤ s := by
      simpa only [D.cleanLabel_eq] using hs
    have hcand : ∀ e, q ≤ e → e ≤ n →
        (Node.frame (Q.trace.state y e)).AncestorCandidate R := by
      exact UpTo.clean_optimistic_writer_candidate_interval D.reset hc hy hop hsc hqn
        (fun r hr => (C.readPoint.1 r hr).trans C.time_bound) hRm
    by_cases hyoung : t < Q.params.ts (s + 1 : Nat) + 6 * Q.params.Δ
    · left
      have hnorm : ell.frame.viableAncestor R = R := by
        rw [Compose.frame_of_projAC D.reset.run hy hcall]
        exact SA.viableAncestor_self (Compose.frameOK_state D.reset.run.toLocalRun hy q)
          (hframe q le_rfl hqn.le) (hcand q le_rfl hqn.le).symm
      rw [hnorm] at hlock
      obtain ⟨e, hlock⟩ := hlock
      have hwf := SA.locksWF_state (Compose.goldilocks_ac_projection _ _ _ _ _ _
        D.reset.run D.reset.noColl).localRun hy (q + 1)
      rw [Compose.projAC_state D.reset.run.toLocalRun hy (q + 1)] at hwf
      have he := hwf.floor hlock
      have hl := UpTo.young_optimistic_lock_persists D.reset hc hy hy hop hsc hqb
        hqn C.readPoint.1 C.time_bound hyoung he hlock
        (fun e hqe hen => ⟨hframe e (Nat.le_of_succ_le hqe) hen.le,
          hcand e (Nat.le_of_succ_le hqe) hen.le⟩)
      apply record_below_anchor_of_stored_live_lock hPhi hl hRm rfl ?_ ?_ hchain
      · have hfloor := (SA.ts_le_iff_le_slot Q.params C.time_nonneg
          (Q.params.slot t)).2 le_rfl
        simp only [SA.SAParams.ts] at hfloor hyoung
        push_cast at hyoung
        change Q.params.slot t ≤ e
        change s + 2 ≤ e at he
        by_contra h
        have : (s : Int) + 3 ≤ Q.params.slot t := by
          exact_mod_cast he.trans_lt (Nat.lt_of_not_le h)
        linarith only [mul_le_mul_of_nonneg_left this
          (by linarith only [hΔ] : (0 : Time) ≤ 4 * Q.params.Δ), hfloor, hyoung, hΔ]
      · rw [SA.viableAncestor_self hPhi hRm (hcand n hqn.le le_rfl).symm]
        exact .refl
    · have hnext : Q.params.ts (s + 1 : Nat) + 6 * Q.params.Δ ≤ t := le_of_not_gt hyoung
      have hjoinNext : Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤
          Q.params.ts (s + 1 : Nat) :=
        hjoin.trans ((SA.ts_le_iff Q.params).2 (by exact_mod_cast hslotq.trans (Nat.le_succ _)))
      obtain ⟨j, ellJ, hu, hji⟩ := update_before_stored_clock S Q.run.2 Q.hn Q.valid
        D.reset hv hjoinNext hnext C.time_bound
      have hjt : Q.trace.time j = Q.params.ts (s + 1 : Nat) + 6 * Q.params.Δ := hu.2.2.1
      have hjb := hjt ▸ hnext.trans C.time_bound
      have hRnext : Healing.drainTime Q.params D.resetTime ≤ Q.params.ts (s + 1 + 1 : Nat) := by
        rw [Healing.drainTime_eq]
        apply (SA.ts_le_iff Q.params).2
        have hs' := hsc
        rw [Healing.cleanLabel_eq] at hs'
        exact_mod_cast (show Q.params.slot D.resetTime + 2 * Q.params.k + 5 ≤
          s + 1 + 1 by omega)
      rcases UpTo.optimistic_result_or_finalized_at_update D.reset hc hy hy hop hsc hqb
          hu hjb hRnext with hRF | ⟨B, DV, hres, hRB⟩
      · left
        apply hfinal
        have hFN := Healing.run_F_mono D.reset.run.toLocalRun hy hji.le
        rw [C.state_eq] at hFN
        exact hRF.trans hFN
      · right
        exact hraw y hy j (s + 1) B DV hres hRB (hjt ▸ hnext) (hs.trans (Nat.le_succ s))

/-- Assemble the current whole-record certificate through the landed scoped adapters. -/
theorem healthy_current_record_read (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    Regimes.readAfter Q.trace (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)
        (stateAt S Q.run.2 Q.hn v i).now =
      (SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F := by
  obtain ⟨C⟩ := healthy_current_read_context S A V Q h0 hb hp W states D O hrepair hi hv
  have hc := healthy_repair_catch S A V Q
  have heq := read_eq_record_of_current_votes D.reset.run D.reset.noColl
    (honest_ownKey (S := S) hv.1) C.time_nonneg C.readPoint C.awake C.joined
    C.sync C.catchup C.latest C.reset_le (fun R hR => ⟨
      healthy_current_live_candidates S A V Q h0 hb hp W states D C hR, ?_⟩) C.fault
  · simpa only [Regimes.readAfter, C.state_eq] using heq
  apply read_source_of_recent_result D.reset hc C.time_bound
  by_cases hfc : (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).Anc R
      (Node.frame (Q.trace.state (Q.run.2.ownKey v) C.cut)).fcRoot
  · exact Or.inl (hfc.trans ((SA.anc_getAnchor
      (Compose.frameOK_state D.reset.run.toLocalRun (honest_ownKey (S := S) hv.1) C.cut)
      (healthy_current_live_chain S A V Q D hv.1 C)).2 _ (Or.inr rfl)))
  rcases healthy_current_mature_or_anchor S A V Q h0 hb hp W states D O hrepair C hR with
    ha | ⟨x, hx, r, s, B, CV, hr, hRB, hrb, hs, hlate, hL⟩
  · exact Or.inl ha
  exact Or.inr ⟨healthy_current_record_viable S A V Q h0 hb hp W states D C
    hx hr hRB hrb hs hL hfc hR, x, hx, r, s, B, CV, hr, hRB, hrb, hs, hL,
    healthy_current_vote_domain S A V Q D hc hx hr hRB hrb
      (clean_add_k_two_le Q.params.two_le_k hlate),
    healthy_current_stored_locks S A V Q h0 hb hp W states D hx hr hRB hrb hlate⟩

omit h0 hb hp W states in
/-- Bound completed events, not the next-event clock of a terminal observation. -/
theorem healthy_cut_prefix_time {i : Nat} (hi : i ≤ Q.run.2.events.length) :
    ∀ q < cutMap S Q.run.2 Q.hn i, Q.trace.time q ≤ Q.run.2.horizon := by
  intro q hq
  apply simTrace_labelled_time_le S Q.run.2 Q.hn Q.valid
  have hlen : q < (allCuts S Q.run.2 Q.hn).length := by
    rw [length_allCuts]
    exact hq.trans_le (cutMap_mono S Q.run.2 Q.hn hi)
  rw [simTrace_label, List.getElem?_eq_getElem hlen]
  simp

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Mixed-source compatibility uses only completed-prefix bounds at each observation.
The existing endpoint signature is retained. -/
theorem healthy_current_sources_compatible (D : HealthyRepairSchedule S A V Q)
    {u v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hbi : ∀ q < cutMap S Q.run.2 Q.hn i, Q.trace.time q ≤ Q.run.2.horizon)
    (hbj : ∀ q < cutMap S Q.run.2 Q.hn j, Q.trace.time q ≤ Q.run.2.horizon)
    (hu : u ∈ Q.run.2.honest) (hv : v ∈ Q.run.2.honest)
    {R R' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : HealthyRecordCover S A V Q D.cleanLabel (Q.run.2.ownKey u)
      (cutMap S Q.run.2 Q.hn i) R)
    (hR' : HealthyRecordCover S A V Q D.cleanLabel (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn j) R') :
    Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2)) R R' := by
  have hc := healthy_repair_catch S A V Q
  have hu' := honest_ownKey (S := S) hu
  have hv' := honest_ownKey (S := S) hv
  rcases hR with rfl | ⟨x, hx, r, s, B, CV, _, hrb, hs, hB, hRB⟩
  · rcases hR' with rfl | ⟨y, hy, q, t, E, DV, _, hqb, ht, hE, hRE⟩
    · have hf' := healthy_faults_lt_quorum S A V Q D
      exact Regimes.finalized_safe _ _ _ _ _ _ D.reset.run D.reset.noColl hf'
        _ hu' _ hv' _ _
    · exact tips_comparable_of_origin_witnesses S A V Q .refl hRE
        (D.reset.finalized_compatible_clean_source hc hy hu' hE
          (by simpa only [D.cleanLabel_eq] using ht) hqb hbi)
  · rcases hR' with rfl | ⟨y, hy, q, t, E, DV, _, hqb, ht, hE, hRE⟩
    · exact (tips_comparable_of_origin_witnesses S A V Q .refl hRB
        (D.reset.finalized_compatible_clean_source hc hx hv' hB
          (by simpa only [D.cleanLabel_eq] using hs) hrb hbj)).symm
    · exact tips_comparable_of_origin_witnesses S A V Q hRB hRE
        (D.reset.clean_sources_compatible hc hx hy hB hE
          (by simpa only [D.cleanLabel_eq] using hs)
          (by simpa only [D.cleanLabel_eq] using ht) hrb hqb)

omit h0 hb hp W states in
/-- Every actual call after an engine cut is at or after that cut's public time. -/
theorem healthy_call_after_cut_time {i q : Nat} {y : Fin Q.params.n}
    (hiq : cutMap S Q.run.2 Q.hn i ≤ q) (hq : Q.trace.IsCall y q) :
    Q.run.2.cutTime i ≤ Q.trace.time q := by
  obtain ⟨ell, _, hlabel⟩ := hq
  obtain ⟨_, p, e, _, he, _, hqp, _, _, htime, _⟩ :=
    simTrace_cut S Q.run.2 Q.hn (by rw [hlabel]; simp)
  have hip : i ≤ p := Nat.le_of_not_lt fun h =>
    lt_irrefl q (hqp.trans_le ((cutMap_mono S Q.run.2 Q.hn h).trans hiq))
  rw [htime]
  cases i with
  | zero => exact (Q.valid.in_horizon e (List.mem_of_getElem? he)).1
  | succ i =>
    have hplen := (List.getElem?_eq_some_iff.mp he).1
    have hil : i < Q.run.2.events.length := ((Nat.lt_succ_self i).trans_le hip).trans hplen
    have hei : Q.run.2.events[i]? = some Q.run.2.events[i] := List.getElem?_eq_getElem hil
    simp only [Model.Run.cutTime, hei]
    rcases keyLe_of_lt S Q.run.2 Q.valid hei he hip with ht | ht
    · exact ht.le
    · exact ht.1.le

set_option linter.unusedVariables false in
/-- Actual interval candidates compare with the named current-record cover.
The repair reserve makes every candidate label clean enough for raw comparison. -/
theorem healthy_current_record_candidates (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j) (hij : i ≤ j)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    ∀ q, cutMap S Q.run.2 Q.hn i ≤ q → q < cutMap S Q.run.2 Q.hn j → ∀ B s CV,
      SA.ResultAt Q.trace.projAC (Q.run.2.ownKey v) q s B CV ∨
        SA.OptimisticLockAt Q.trace.projAC (Q.run.2.ownKey v) q s B CV →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2))
        ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
            (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) B := by
  have hcover := healthy_current_record_sources S A V Q h0 hb hp W states D O hrepair hi hv
  have hy := honest_ownKey (S := S) hv.1
  intro q hiq hqj B s CV hB
  have hqb := healthy_cut_prefix_time S A V Q hj.1 q hqj
  have hcall : Q.trace.IsCall (Q.run.2.ownKey v) q := by
    rcases hB with ⟨ell, hu, _⟩ | ⟨ell, A, ho, _⟩
    · exact ⟨_, Compose.projAC_callAt.mp hu.1⟩
    · exact ⟨_, Compose.projAC_callAt.mp ho.1⟩
  have ht : Q.heal ≤ Q.trace.time q :=
    hi.2.trans (healthy_call_after_cut_time S A V Q hiq hcall)
  have hbudget : Q.params.ts D.oldLabel + 6 * Q.params.Δ < Q.trace.time q := by
    have hlo : Q.params.ts D.oldLabel ≤ D.query :=
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans D.lower
    linarith only [hlo, D.reserve, ht,
      mul_nonneg (Int.natCast_nonneg Q.index) Q.params.toParams.hΔ.le]
  have hs : D.cleanLabel + 2 * Q.params.k + 1 ≤ s := by
    apply D.old_bound.trans
    rcases hB with ⟨ell, hu, _⟩ | ⟨ell, A, ho, hslot, _⟩
    · have htime : Q.trace.time q = Q.params.ts s + 6 * Q.params.Δ := hu.2.2.1
      have hlt := (SA.ts_lt_iff Q.params).mp (show Q.params.ts D.oldLabel < Q.params.ts s by
        linarith only [htime, hbudget])
      exact_mod_cast hlt.le
    · have hh := (SA.ts_le_iff_le_slot Q.params (D.reset.run.time_nonneg q) D.oldLabel).mp
        (show Q.params.ts D.oldLabel ≤ Q.trace.time q by
          linarith only [hbudget, Q.params.toParams.hΔ])
      change Q.params.slot (Q.trace.time q) = s at hslot
      rw [← hslot]
      exact_mod_cast hh
  rcases hcover with hF | ⟨x, hx, r, t, E, DV, _, hrb, hts, hE, hRE⟩
  · rw [hF]
    exact D.reset.finalized_compatible_clean_source (healthy_repair_catch S A V Q) hy hy hB
      (by simpa only [D.cleanLabel_eq] using hs) hqb (healthy_cut_prefix_time S A V Q hi.1)
  · exact tips_comparable_of_origin_witnesses S A V Q hRE .refl
      (D.reset.clean_sources_compatible (healthy_repair_catch S A V Q) hx hy hE hB
        (by simpa only [D.cleanLabel_eq] using hts)
        (by simpa only [D.cleanLabel_eq] using hs) hrb hqb)

set_option linter.unusedVariables false in
/-- Next-floor comparison from the named current-record cover producer,
independently of candidate comparison and current viability. -/
theorem healthy_current_record_next_floor (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j) (hij : i ≤ j)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    ∀ q, cutMap S Q.run.2 Q.hn i ≤ q → q < cutMap S Q.run.2 Q.hn j →
      Goldilocks.Compatible (Q.trace.HonestBlocks (honestKeys S Q.run.2))
        (Q.trace.state (Q.run.2.ownKey v) (q + 1)).fg.F
        ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
            (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) := by
  have hcover := healthy_current_record_sources S A V Q h0 hb hp W states D O hrepair hi hv
  have hy := honest_ownKey (S := S) hv.1
  intro q hiq hqj
  have hqb : ∀ p < q + 1, Q.trace.time p ≤ Q.run.2.horizon :=
    fun p hpq => healthy_cut_prefix_time S A V Q hj.1 p ((Nat.lt_succ_iff.mp hpq).trans_lt hqj)
  rcases hcover with hF | ⟨x, hx, r, s, B, CV, _, hrb, hs, hB, hRB⟩
  · rw [hF]
    have hf' := healthy_faults_lt_quorum S A V Q D
    exact Regimes.finalized_safe _ _ _ _ _ _ D.reset.run D.reset.noColl hf' _ hy _ hy _ _
  · exact tips_comparable_of_origin_witnesses S A V Q .refl hRB
      (D.reset.finalized_compatible_clean_source (healthy_repair_catch S A V Q) hx hy hB
        (by simpa only [D.cleanLabel_eq] using hs) hrb hqb)

/-- Candidate and next-floor inputs produce the original directed cut interval. -/
theorem healthy_current_record_interval (D : HealthyRepairSchedule S A V Q)
    (O : HealthyRepairOpening S A V Q D) (hrepair : HealthyReceiverRepair S A V Q D O)
    {v : V} {i j : Nat} (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j) (hij : i ≤ j)
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i)) :
    EffectiveRecordInterval Q.trace (honestKeys S Q.run.2) (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn i) (cutMap S Q.run.2 Q.hn j)
      ((SA.lookup (Node.frame (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)))
        (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).ac.latestConfirmed).getD
          (Q.trace.state (Q.run.2.ownKey v) (cutMap S Q.run.2 Q.hn i)).fg.F) := by
  exact effectiveRecordInterval_of_candidates_before D.reset (honest_ownKey (S := S) hv.1)
    (healthy_current_record_candidates S A V Q h0 hb hp W states D O hrepair hi hj hij hv)
    (healthy_current_record_next_floor S A V Q h0 hb hp W states D O hrepair hi hj hij hv)

end EndpointProducers

/-- OPEN comparability of actual stored-clock tips. Old-attestation realization,
label replacement and head/lock/frame comparability remain obligations. InCuts
includes cuts at heal before endCut heal; the state facts do not cover these. -/
theorem healthy_cut_tips_comparable (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    let C := fun v i => Regimes.readAfter Q.trace (Q.run.2.ownKey v)
      (cutMap S Q.run.2 Q.hn i) (stateAt S Q.run.2 Q.hn v i).now
    Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C u i) (C v j) ∨
      Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (C v j) (C u i) := by
  obtain ⟨D⟩ := healthy_repair_schedule S A V Q h0 hb hp W states
  obtain ⟨O, hr⟩ := healthy_bounded_repairing_opening S A V Q h0 hb hp W states D
  have hri := healthy_current_record_read S A V Q h0 hb hp W states D O hr hi hu
  have hrj := healthy_current_record_read S A V Q h0 hb hp W states D O hr hj hv
  dsimp only
  rw [hri, hrj]
  exact healthy_current_sources_compatible S A V Q h0 hb hp W states D hi hj
    (healthy_cut_prefix_time S A V Q hi.1) (healthy_cut_prefix_time S A V Q hj.1) hu.1 hv.1
    (healthy_current_record_sources S A V Q h0 hb hp W states D O hr hi hu)
    (healthy_current_record_sources S A V Q h0 hb hp W states D O hr hj hv)

/-- OPEN temporal ancestry, not merely common-chain membership. The stored
clock and equality-time boundary are retained exactly as in the engine reads. -/
theorem healthy_cut_tips_ancestor (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
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
  obtain ⟨D⟩ := healthy_repair_schedule S A V Q h0 hb hp W states
  obtain ⟨O, hr⟩ := healthy_bounded_repairing_opening S A V Q h0 hb hp W states D
  rw [healthy_current_record_read S A V Q h0 hb hp W states D O hr hi hvi,
    healthy_current_record_read S A V Q h0 hb hp W states D O hr hj hvj]
  exact effective_record_of_interval D.reset.run D.reset.noColl
    (honest_ownKey (S := S) hvi.1) (cutMap_mono S Q.run.2 Q.hn hij)
    (healthy_current_record_interval S A V Q h0 hb hp W states D O hr hi hj hij hvi) .refl

/-- Arbitrary-cut engine agreement reduces to the named open tip comparability
obligation. No equality between stored clock and cut time is assumed. -/
theorem healthy_cut_agreement (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (u v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hu : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) u
      ((chainTrace Q.run.2).cutTime i))
    (hv : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    Consensus.Compatible ((chainTrace Q.run.2).read .confirmed u i)
      ((chainTrace Q.run.2).read .confirmed v j) := by
  have hs := simTrace_simulates S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision
  rcases healthy_cut_tips_comparable S A V Q h0 hb hp W states u v i j hi hj hu hv with h | h
  · exact Or.inl (confirmed_prefix_of_anc hs hnc hu.1 hv.1 hi.1 hj.1 h)
  · exact Or.inr (confirmed_prefix_of_anc hs hnc hv.1 hu.1 hj.1 hi.1 h)

/-- Arbitrary-cut monotonicity reduces to directed tip ancestry. Agreement
alone is not used to infer temporal movement. -/
theorem healthy_cut_monotone (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (W : HealthyBaseTiming S A V Q)
    (states : ∀ k, Q.cut ≤ k → k ≤ cutMap S Q.run.2 Q.hn Q.run.2.events.length →
      HealthyStateFacts S A V Q W.slot k)
    (v : V) (i j : Nat)
    (hi : (chainTrace Q.run.2).InCuts Q.heal i) (hij : i ≤ j)
    (hj : (chainTrace Q.run.2).InCuts Q.heal j)
    (hvi : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime i))
    (hvj : Q.run.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) Q.run) v
      ((chainTrace Q.run.2).cutTime j)) :
    (chainTrace Q.run.2).read .confirmed v i <+:
      (chainTrace Q.run.2).read .confirmed v j := by
  exact confirmed_prefix_of_anc (simTrace_simulates S Q.run.2 Q.hn Q.valid)
    (noCollRun_simTrace S Q.run.2 Q.hn Q.valid Q.noCollision) hvi.1 hvj.1 hi.1 hj.1
    (healthy_cut_tips_ancestor S A V Q h0 hb hp W states v i j hi hij hj hvi hvj)

/-- Assembly with finite preparation; only the two named cut adapters remain
for projection. Their OPEN types retain the exact equality-time boundary case. -/
theorem healthy_ready_safety (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    (chainTrace Q.run.2).ReadySafe ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      .confirmed Q.heal := by
  obtain ⟨W, ⟨D⟩⟩ := healthy_preparation_initialize S A V Q h0 hb hp
  have base := healthy_prepare S A V Q h0 hb hp W D
  have states := healthy_preserve S A V Q h0 hb W base
  exact ⟨healthy_cut_agreement S A V Q h0 hb hp W states,
    healthy_cut_monotone S A V Q h0 hb hp W states⟩

end Consensus.Goldilocks.Obligations
end
