module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Pending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ConditionalPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.ServedHead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Conditional read safety and the healthy repair schedule, under growing faults

The growing form of `Obligations/HealedSafetyConditional`. Each node is honest at its own cut;
a reader is honest at its read time `t`, after the read state's cuts (`Regimes.ReadPoint`); every
vote, cast and source is by a node honest at its own cut; ancestry is read in the blocks held while
honest (`HonestBlocksAt`). The pure SA lemmas `result_label_lt_latest_of_time` and
`record_below_anchor_of_stored_live_lock` are reused unchanged.

* `read_eq_record_of_current_votes_at`, `read_source_of_recent_result_at`: whole-record read
  equality at a read point, and the recent-result source arm it consumes;
* `tips_comparable_of_origin_witnesses_at`;
* `healthy_query_call_time_le_at`;
* `healthy_repair_schedule_of_reset_at`, `healthy_repair_schedule_of_preparation_at`,
  `healthy_repair_schedule_at`: the finite repair schedule;
* `healthy_receiver_repair_of_opening_at`: the receiver repair at an operational opening;
* `healthy_current_record_sources_before_now_at`: the record cover at a read point after the
  repair. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

/-- **Whole-record equality at a read point**, under growing faults. A reader honest, awake and
joined at its read time `t`, with the prefix service through `t`, a record whose live-candidate
compatibility holds and whose source is the anchor or a viable block extended by every vote of
label `L` by `t` of a node honest at its vote, and the fault bound at `t_L + Δ ≤ t`: the read is
the record. -/
theorem read_eq_record_of_current_votes_at
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {a : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t)
    (hrp : Regimes.ReadPoint tr i t) (hw : tr.awake y t) (hj : tr.JoinedAt y t)
    (hsync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t))
    (hcatch : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (SA.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L)
    (hrecord : ∀ R, SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed = some R →
      (∀ X ∈ SA.liveLockBlocks sp (tr.state y i).ac.locks (Node.frame (tr.state y i)) t ∪
          {(Node.frame (tr.state y i)).fcRoot},
        Goldilocks.Compatible (Node.frame (tr.state y i)).tree X R) ∧
      ((Node.frame (tr.state y i)).Anc R
          (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          ∀ z q e, Compose.Growing.HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
            SA.VoteExtends (tr.HonestBlocksAt H) e.msg R)))
    (hLt : sp.ts L + sp.Δ ≤ t) (hfault : tr.FaultBoundAt H (sp.ts L + sp.Δ) t) :
    Regimes.readAfter tr y i t =
      (SA.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F := by
  have hΦ : FrameOK (Node.frame (tr.state y i)) := by
    have h := Compose.frameOK_state (hrun.upTo ht0).toLocalRun hy i
    rwa [Trace.upTo_state tr y hrp.1] at h
  cases hl : SA.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
  | none => exact SA.acConfirmed_eq_F hΦ (SA.lookup_eq_none hl)
  | some R =>
    obtain ⟨hR, hRr⟩ := SA.lookup_eq_some hl
    obtain ⟨hcomp, hsource⟩ := hrecord R hl
    have hanchor := Compose.anchor_compatible_of_live_candidates hΦ hcomp
    obtain ⟨hc, hs⟩ := Compose.Growing.read_head_support_of_target_votes_at hrun hnc ht0 hy
      hrp.1 hrp.2 hw hj hsync hcatch hL ha hR hanchor hsource hLt hfault
    exact SA.acConfirmed_eq hΦ hR hRr (SA.anc_acHead hΦ hR hc hs)

/-- The source arm consumed by `read_eq_record_of_current_votes_at`: either actual anchor
coverage, or a recent result of a node honest at its cut covering the whole record, with its
domain and stored-lock comparisons over casts and votes of nodes honest at their own cuts. -/
theorem read_source_of_recent_result_at
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {g ΔF a b t : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {y : Fin sp.n} {i L : Nat}
    {R : SA.Blk sp.n (List (FG.Att sp.n))} (htb : t ≤ b)
    (hsource : (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∃ x r s C CV, x ∈ H (tr.time r) ∧ SA.ResultAt tr.projAC x r s C CV ∧
          Anc (tr.HonestBlocksAt H) R C ∧ tr.time r ≤ b ∧
          Healing.cutZ sp.toParams g ≤ sp.ts s ∧ s < L ∧
          (∀ z q ell e, z ∈ H (tr.time q) → SA.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → s < e.msg.slot →
            (∀ w p e', p < q → Compose.Growing.HVoteAt tr H w p e' →
              s < e'.msg.slot → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg R) →
            Anc (tr.HonestBlocksAt H) R ell.frame.fcRoot ∨
              R ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) ∧
          (∀ z q ell e, z ∈ H (tr.time q) → SA.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state z q).locks,
              sp.slot (tr.time q) ≤ l.slot + sp.k → l.slot ≤ s →
              ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block →
                Goldilocks.Compatible (tr.HonestBlocksAt H) Y R))) :
    (Node.frame (tr.state y i)).Anc R
        (SA.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∀ z q e, Compose.Growing.HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
          SA.VoteExtends (tr.HonestBlocksAt H) e.msg R) := by
  rcases hsource with h | ⟨hv, x, r, s, C, CV, hx, hres, hRC, hrb, hts, hsL, hd, hl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hv,
      hp.latest_votes_of_recent_result_at hc hx hres hRC hrb hts hd hl htb hsL⟩

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- Actual tips below compatible origin witnesses are comparable, in the blocks held while
honest. -/
theorem tips_comparable_of_origin_witnesses_at (Q : HealthyPreparationQueryAt S A V)
    {R R' C C' : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hR : Anc (Q.trace.HonestBlocksAt Q.keys) R C)
    (hR' : Anc (Q.trace.HonestBlocksAt Q.keys) R' C')
    (hCC : Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys) C C') :
    Goldilocks.Compatible (Q.trace.HonestBlocksAt Q.keys) R R' := by
  have hU := Compose.Growing.honest_blocks_coherent
    (simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid)
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision)
  rcases hCC with h | h
  · exact Anc.total hU (hR.trans h) hR'
  · exact Anc.total hU hR (hR'.trans h)

/-- Every call of the canonical trace of a query is within the engine horizon. -/
theorem healthy_query_call_time_le_at (Q : HealthyPreparationQueryAt S A V)
    {y : Fin Q.params.n} {j : Nat} (hj : Q.trace.IsCall y j) :
    Q.trace.time j ≤ Q.run.2.horizon := by
  obtain ⟨ell, _, hlabel⟩ := hj
  exact simTraceAt_labelled_time_le S Q.run.2 Q.hn Q.valid (by rw [hlabel]; simp)

/-- A supplied finite reset and its strict joint reserve suffice for the canonical repair
schedule. Neither the reset nor the reserve is produced here. -/
theorem healthy_repair_schedule_of_reset_at
    (Q : HealthyPreparationQueryAt S A V) {ΔF a : Time}
    (hreset : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
      (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2)
      Q.gst ΔF a Q.run.2.horizon)
    (hreserve : max Q.ready (Healing.drainTime Q.params a) +
      (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1) :
    ∃ D : HealthyRepairScheduleAt S A V Q,
      D.resetTime = a ∧ D.deltaF = ΔF ∧
      D.query = max Q.ready (Healing.drainTime Q.params a) ∧
      D.oldLabel = Q.params.slot a + 2 * Q.params.k + 4 := by
  have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hduration : 18 * Q.params.Δ + 1 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run := by
    simp only [System.cDur, Params.standard, contract_coefficients_catchUp]
    change 18 * Q.run.1.ΔAC + 1 ≤ (contract_catchUp S A : Nat) * Q.run.1.ΔAC
    linarith [mul_le_mul_of_nonneg_right hc (by linarith : (0 : Time) ≤ Q.run.1.ΔAC)]
  have hΔ := Q.params.toParams.hΔ
  have hready : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.ready := by
    change max Q.gst 0 + 4 * Q.params.Δ ≤
      max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1
    linarith
  have hzero : 0 ≤ Q.ready := by
    change 0 ≤ max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1
    linarith [le_max_right Q.gst 0]
  have hold : Q.params.ts (Q.params.slot a + 2 * Q.params.k + 4 : Nat) ≤
      Healing.drainTime Q.params a := by
    rw [Healing.drainTime_eq]
    exact (SA.ts_le_iff Q.params).mpr (by omega)
  refine ⟨{
    resetTime := a
    deltaF := ΔF
    reset := hreset
    cleanLabel := Healing.cleanLabel Q.params a
    cleanLabel_eq := rfl
    duration_bound := by linarith
    oldLabel := Q.params.slot a + 2 * Q.params.k + 4
    old_bound := by rw [Healing.cleanLabel_eq]; omega
    query := max Q.ready (Healing.drainTime Q.params a)
    lower := ?_
    reserve := hreserve }, rfl, rfl, rfl, rfl⟩
  exact max_le (le_max_left _ _) (max_le (le_max_right _ _)
    (max_le (hold.trans (le_max_right _ _))
      (max_le (hready.trans (le_max_left _ _)) (hzero.trans (le_max_left _ _)))))

/-- A preparation schedule for the same query supplies a repair schedule with the very same
reset time, service delay and query, without a base-slot comparison. -/
theorem healthy_repair_schedule_of_preparation_at
    (Q : HealthyPreparationQueryAt S A V)
    (W : HealthyBaseTimingAt S A V Q)
    (Dprep : HealthyPreparationScheduleAt S A V Q W) :
    ∃ D : HealthyRepairScheduleAt S A V Q,
      D.resetTime = Dprep.resetTime ∧ D.deltaF = Dprep.deltaF ∧ D.query = Dprep.query := by
  have hlower : max Q.ready (Healing.drainTime Q.params Dprep.resetTime) ≤ Dprep.query :=
    max_le ((le_max_left _ _).trans Dprep.lower)
      ((le_max_left _ _).trans ((le_max_right _ _).trans Dprep.lower))
  obtain ⟨D, hreset, hdelta, hquery, _⟩ := healthy_repair_schedule_of_reset_at S A V Q
    Dprep.reset (by linarith [Dprep.reserve])
  refine ⟨{ D with query := Dprep.query, lower := ?_, reserve := Dprep.reserve },
    hreset, hdelta, rfl⟩
  exact D.lower.trans (hquery ▸ hlower)

/-- The repair schedule of the preparation initializer: its finite preparation schedule keeps
its reset time, service delay and query (`healthy_repair_schedule_of_preparation_at`). -/
theorem healthy_repair_schedule_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    Nonempty (HealthyRepairScheduleAt S A V Q) := by
  obtain ⟨W', ⟨Dprep⟩⟩ := healthy_preparation_initialize_at S A V Q h0 hb hp
  obtain ⟨D, -⟩ := healthy_repair_schedule_of_preparation_at S A V Q W' Dprep
  exact ⟨D⟩

/-- **Any bounded operational opening repairs the post-update source cover**, under growing
faults. No current-read geometry or prior repair invariant is used. -/
theorem healthy_receiver_repair_of_opening_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.run.2.horizon) (D : HealthyRepairScheduleAt S A V Q)
    (O : HealthyRepairOpeningAt S A V Q D)
    (hc : Healing.Growing.CatchRun Q.trace Q.keys Q.gst (2 * Q.params.Δ)) :
    HealthyReceiverRepairAt S A V Q D O := by
  rw [healthyReceiverRepairAt_iff]
  have hd := Q.params.toParams.hΔ
  have hTb : Q.params.ts O.slot + 6 * Q.params.Δ ≤ Q.run.2.horizon := by
    linarith [O.bounded, D.reserve]
  have hR : Healing.drainTime Q.params D.resetTime ≤ Q.params.ts O.slot := by
    have := (le_max_left _ _).trans ((le_max_right _ _).trans D.lower)
    exact this.trans O.fresh.le
  have hgu : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.params.ts O.slot := by
    have := (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))
    exact this.trans O.fresh.le
  have hjoin : Q.params.ts (Q.params.slot (SA.gbar Q.gst) + 1 : Nat) ≤ Q.params.ts O.slot := by
    have hbase := (SA.ts_le_iff_le_slot Q.params (SA.gbar_nonneg Q.gst)
      (Q.params.slot (SA.gbar Q.gst))).mpr le_rfl
    simp only [SA.SAParams.ts] at hbase hgu ⊢
    push_cast at hbase hgu ⊢
    linarith
  intro y hy
  obtain ⟨j, ell, _, hu, _⟩ := D.reset.update_toFG_calls_at hy.1 hjoin hTb
  have ht : Q.trace.time j = Q.params.ts O.slot + 6 * Q.params.Δ := hu.2.2.1
  refine ⟨j, ell, hu, ht, ht ▸ hTb, ?_⟩
  intro R hlookup
  have hyj : y ∈ Q.keys (Q.trace.time j) := ht ▸ hy.1
  obtain ⟨x, q, s, CV, hx, hqj, hqt, hs, hsource⟩ :=
    Healing.Growing.operational_update_recent_source_at D.reset hc O.held rfl O.proposes
      O.label hR hgu hTb hyj hu hlookup
  exact ⟨x, q, s, R, CV, hx, hqj, hqt, O.old_lt.le.trans hs, hsource, .refl⟩

/-- **Repair cover at a read point**, under growing faults. For a reader honest at its read time
`t` after the repair window, the record before cut `n` (read at `t`) is its finalized block or
below a result or optimistic lock of a node honest at its own cut, before `n` and by `t`. -/
theorem healthy_current_record_sources_before_now_at (Q : HealthyPreparationQueryAt S A V)
    (D : HealthyRepairScheduleAt S A V Q) (O : HealthyRepairOpeningAt S A V Q D)
    (hrepair : HealthyReceiverRepairAt S A V Q D O) {y : Fin Q.params.n} {n : Nat} {t : Time}
    (hrp : Regimes.ReadPoint Q.trace n t) (htb : t ≤ Q.run.2.horizon) (hy : y ∈ Q.keys t)
    (hrep : D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ < t) :
    HealthyRecordCoverAt S A V Q D.cleanLabel y n t
      ((SA.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed).getD
        (Q.trace.state y n).fg.F) := by
  rw [healthyRecordCoverAt_iff]
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have hd := Q.params.toParams.hΔ
  have h6 : (0 : Time) ≤ 6 * Q.params.Δ := mul_nonneg (by decide) hd.le
  have hTt : Q.params.ts O.slot + 6 * Q.params.Δ < t := by
    refine lt_of_le_of_lt ?_ hrep
    rw [add_mul, ← add_assoc]
    exact add_le_add O.bounded le_rfl
  have hready : Q.ready < Q.params.ts O.slot + 6 * Q.params.Δ :=
    ((le_max_left _ _).trans D.lower).trans_lt (lt_add_of_lt_of_nonneg O.fresh h6)
  have hzero : 0 ≤ Q.ready := by
    change 0 ≤ max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1
    exact add_nonneg (add_nonneg (le_max_right _ _)
      ((mul_nonneg (by decide) hd.le).trans D.duration_bound)) zero_le_one
  have ht0 : 0 ≤ t := (hzero.trans hready.le).trans hTt.le
  -- the receiver is ready at the update time
  have hyT : y ∈ Q.keys (Q.params.ts O.slot + 6 * Q.params.Δ) :=
    honestKeysAt_antitone S Q.run.2 hTt.le hy
  have hr : Regimes.Growing.ReadyAt Q.trace Q.keys
      ((Sys (goldilocks S) V).cDur (K S A) Q.run) y
      (Q.params.ts O.slot + 6 * Q.params.Δ) := by
    refine ⟨hyT, fun τ hτ hτT => ?_⟩
    have hgτ : max Q.gst 0 ≤ τ := by
      change max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 <
        Q.params.ts O.slot + 6 * Q.params.Δ at hready
      refine (le_of_lt ?_).trans ((le_max_right _ _).trans hτ)
      rw [sub_sub, lt_sub_iff_add_lt, ← add_assoc]
      exact hready
    have hτb : τ ≤ Q.run.2.horizon := hτT.trans (hTt.le.trans htb)
    have hyτ : y ∈ Q.keys τ := honestKeysAt_antitone S Q.run.2 hτT hyT
    rw [mem_honestKeysAt_iff, min_eq_left hτb] at hyτ
    rw [simTraceAt_awake_iff, awakeAt_iff]
    exact ⟨Q.healthy.2.1.2 _ τ hgτ hτb hyτ, (le_max_right _ _).trans hgτ, hτb⟩
  obtain ⟨a, ell, ha, hat, -, hcover⟩ := healthyReceiverRepairAt_iff.mp hrepair y hr
  have han : a < n := by
    by_contra h
    have := hrun.time_mono (Nat.le_of_not_lt h)
    linarith [hrp.2]
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hind : ∀ k, a + 1 ≤ k → k ≤ n → ∀ R,
      SA.lookup (Node.frame (Q.trace.state y k)) (Q.trace.state y k).ac.latestConfirmed =
        some R →
      ∃ x q s C CV, x ∈ Q.keys (Q.trace.time q) ∧ q < k ∧ Q.trace.time q ≤ t ∧
        D.oldLabel ≤ s ∧
        (SA.ResultAt Q.trace.projAC x q s C CV ∨ SA.OptimisticLockAt Q.trace.projAC x q s C CV) ∧
        Anc (Q.trace.HonestBlocksAt Q.keys) R C := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _ R hR
      obtain ⟨x, q, s, C, CV, hx, hqa, hqt, hs, hC, hRC⟩ := hcover R hR
      exact ⟨x, q, s, C, CV, hx, Nat.lt_succ_of_le hqa, hqt.trans (hat ▸ hTt.le), hs, hC, hRC⟩
    | succ k hak ih =>
      intro hkn R hR
      have hle1 : ∀ q < k + 1, Q.trace.time q ≤ t := fun q hq => hrp.1 q (by omega)
      have hle0 : ∀ q < k, Q.trace.time q ≤ t := fun q hq => hrp.1 q (by omega)
      have hkt : Q.trace.time k ≤ t := hrp.1 k (by omega)
      have hyk : y ∈ Q.keys (Q.trace.time k) := honestKeysAt_antitone S Q.run.2 hkt hy
      rcases record_step_origin_at hrun hyk with heq | ⟨C, hC, hCr, s, CV, hs⟩
      · obtain ⟨x, q, s, B, DV, hx, hqk, hqb, hsl, hB, hRB⟩ :=
          ih (Nat.le_of_succ_le hkn) R
            (record_lookup_of_later_at hrun hnc ht0 hle1 hy (Nat.le_succ k) heq hR)
        exact ⟨x, q, s, B, DV, hx, Nat.lt_succ_of_lt hqk, hqb, hsl, hB, hRB⟩
      · obtain ⟨hRm, hRr⟩ := SA.lookup_eq_some hR
        have hRC : R = C := hU.1 ⟨y, k + 1, t, ht0, hle1, hy, hRm.1⟩
          ⟨y, k, t, ht0, hle0, hy, hC⟩ (hRr.trans hCr.symm)
        have htk : Q.params.ts O.slot + 6 * Q.params.Δ ≤ Q.trace.time k := by
          rw [← hat]
          exact hrun.time_mono (Nat.le_of_succ_le hak)
        have hsl : D.oldLabel ≤ s := by
          have hus : O.slot ≤ s := by
            rcases hs with ⟨ell, hu, _⟩ | ⟨ell, A, ho, hslot, _⟩
            · have ht : Q.trace.time k = Q.params.ts s + 6 * Q.params.Δ := hu.2.2.1
              have hh := (SA.ts_le_iff Q.params).mp
                (le_of_add_le_add_right (htk.trans_eq ht))
              omega
            · have hh := (SA.ts_le_iff_le_slot Q.params (hrun.time_nonneg k) O.slot).mp
                ((le_add_of_nonneg_right h6).trans htk)
              change Q.params.slot (Q.trace.time k) = s at hslot
              omega
          exact O.old_lt.le.trans hus
        exact ⟨y, k, s, C, CV, hyk, Nat.lt_succ_self _, hkt, hsl, hs, by rw [hRC]; exact .refl⟩
  cases hl : SA.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed with
  | none => exact Or.inl (by simp only [Option.getD_none])
  | some R =>
    obtain ⟨x, q, s, C, CV, hx, hqn, hqb, hs, hC, hRC⟩ := hind n han le_rfl R hl
    exact Or.inr ⟨x, q, s, C, CV, hx, hqn, hqb, D.old_bound.trans hs, hC,
      by simpa only [hl, Option.getD_some] using hRC⟩

end Consensus.Goldilocks.Obligations.Growing

end
