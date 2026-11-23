module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Selection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.ServedHead
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.LatestVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RecordGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRepairTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Conditional read safety and the healthy repair schedule, under growing faults

The growing form of `Obligations/HealedSafetyConditional`. Each node is honest at its own cut;
a reader is honest at its read time `t`, after the read state's cuts (`Regimes.ReadPoint`); every
vote, cast and source is by a node honest at its own cut; ancestry is read in the blocks held while
honest (`HonestBlocksAt`). The pure AC lemmas `result_label_lt_latest_of_time` and
`record_below_anchor_of_stored_live_lock` are reused unchanged.

* `read_eq_record_of_current_votes_at`, `read_source_of_recent_result_at`: whole-record read
  equality at a read point, and the recent-result source arm it consumes;
* `tips_comparable_of_origin_witnesses_at`;
* `healthy_repair_schedule_of_reset_at`, `healthy_repair_schedule_of_preparation_at`,
  `healthy_repair_schedule_at`: the finite repair schedule of a query;
* on any trace with a repair schedule: `repair_opening_join`, `receiver_repair_of_opening_at`
  (every opening repairs the receivers honest at its update) and `record_sources_before_now_at`
  (the record cover at a read point after the opening's update). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape

/-- **Whole-record equality at a read point**, under growing faults. A reader honest, awake and
joined at its read time `t`, with the prefix service through `t`, a record whose live-candidate
compatibility holds and whose source is the anchor or a viable block extended by every vote of
label `L` by `t` of a node honest at its vote, and the slot-`L` committee's fault bound charged
at `t`, with awake and joined members at `t_L + Δ ≤ t`: the read is the record. -/
theorem read_eq_record_of_current_votes_at
    {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {a : Time}
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t)
    (hrp : Regimes.ReadPoint tr i t) (hw : tr.awake y t) (hj : tr.JoinedAt y t)
    (hsync : SyncACWindowBefore (H t) ((tr.upTo t).HonestBlocks (H t)) a t (tr.projAC.upTo t))
    (hcatch : CatchACWindowBefore (tr.projAC.upTo t) (H t) ((tr.upTo t).HonestBlocks (H t)) a
      (2 * sp.Δ) t)
    {L : Nat} (hL : (L : Int) =
      (AC.latestView sp (tr.state y i).ac (Node.frame (tr.state y i)) t).2)
    (ha : a ≤ sp.ts L)
    (hrecord : ∀ R, AC.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed = some R →
      (∀ X ∈ AC.liveLockBlocks sp (tr.state y i).ac.locks (Node.frame (tr.state y i)) t ∪
          {(Node.frame (tr.state y i)).fcRoot},
        Goldilocks.Compatible (Node.frame (tr.state y i)).tree X R) ∧
      ((Node.frame (tr.state y i)).Anc R
          (AC.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
        (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
          ∀ z q e, Compose.Growing.HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
            AC.VoteExtends (tr.HonestBlocksAt H) e.msg R)))
    {K : AC.CommitteeDict sp.n} (hKB : Compose.Growing.CommitteeFacts tr H K)
    (hLt : sp.ts L + sp.Δ ≤ t) (hfb : AC.FaultBoundK K L tr.projAC (H t) (sp.ts L + sp.Δ)) :
    Regimes.readAfter tr y i t =
      (AC.lookup (Node.frame (tr.state y i))
        (tr.state y i).ac.latestConfirmed).getD (tr.state y i).fg.F := by
  have hΦ : FrameOK (Node.frame (tr.state y i)) := by
    have h := Compose.frameOK_state (hrun.upTo ht0).toLocalRun hy i
    rwa [Trace.upTo_state tr y hrp.1] at h
  cases hl : AC.lookup (Node.frame (tr.state y i)) (tr.state y i).ac.latestConfirmed with
  | none => exact AC.acConfirmed_eq_F hΦ (AC.lookup_eq_none hl)
  | some R =>
    obtain ⟨hR, hRr⟩ := AC.lookup_eq_some hl
    obtain ⟨hcomp, hsource⟩ := hrecord R hl
    have hanchor := Compose.anchor_compatible_of_live_candidates hΦ hcomp
    obtain ⟨hc, hs⟩ := Compose.Growing.read_head_support_of_target_votes_at hrun hnc ht0 hy
      hrp.1 hrp.2 hw hj hsync hcatch hL ha hR hanchor hsource hKB hLt hfb
    exact AC.acConfirmed_eq hΦ hR hRr (AC.anc_acHead hΦ hR hc hs)

/-- The source arm consumed by `read_eq_record_of_current_votes_at`: either actual anchor
coverage, or a recent result of a node honest at its cut covering the whole record, with its
domain and stored-lock comparisons over casts and votes of nodes honest at their own cuts. -/
theorem read_source_of_recent_result_at
    {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}
    {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g ΔF a b t : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
    {y : Fin sp.n} {i L : Nat}
    {R : AC.Blk sp.n (List (FG.Att sp.n))} (htb : t ≤ b)
    (hsource : (Node.frame (tr.state y i)).Anc R
        (AC.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∃ x r s C CV, x ∈ H (tr.time r) ∧ AC.ResultAt tr.projAC x r s C CV ∧
          Anc (tr.HonestBlocksAt H) R C ∧ tr.time r ≤ b ∧
          Healing.cutZ sp.toParams g ≤ sp.ts s ∧ s < L ∧
          (∀ z q ell e, z ∈ H (tr.time q) → AC.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → s < e.msg.slot →
            (∀ w p e', p < q → Compose.Growing.HVoteAt tr H w p e' →
              s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg R) →
            Anc (tr.HonestBlocksAt H) R ell.frame.fcRoot ∨
              R ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) ∧
          (∀ z q ell e, z ∈ H (tr.time q) → AC.CastAt tr.projAC z q ell e →
            tr.time q ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state z q).locks,
              sp.slot (tr.time q) ≤ l.slot + sp.k → l.slot ≤ s →
              ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block →
                Goldilocks.Compatible (tr.HonestBlocksAt H) Y R))) :
    (Node.frame (tr.state y i)).Anc R
        (AC.getAnchor sp (tr.state y i).ac (Node.frame (tr.state y i)) t) ∨
      (R ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree ∧
        ∀ z q e, Compose.Growing.HVoteAt tr H z q e → tr.time q ≤ t → e.msg.slot = L →
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg R) := by
  rcases hsource with h | ⟨hv, x, r, s, C, CV, hx, hres, hRC, hrb, hts, hsL, hd, hl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hv,
      hp.latest_votes_of_recent_result_at hx hres hRC hrb hts hd hl htb hsL⟩

variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- A supplied finite reset and its strict joint reserve suffice for the canonical repair
schedule. Neither the reset nor the reserve is produced here. -/
theorem healthy_repair_schedule_of_reset_at
    (Q : HealthyPreparationQueryAt S A V) {ΔF a : Time}
    (hreset : Healing.Growing.ResetPremisesUpTo Q.trace Q.keys
      (runProposer S Q.run.2 Q.hn)
      (digestOf S Q.run.2)
      Q.gst ΔF a Q.bound
        (runCommittee S Q.run.2 Q.hn) (K S A).params.βK)
    (hreserve : max Q.ready (Healing.drainTime Q.params a) +
      (4 * (Q.index : Time) + 6) * Q.params.Δ < Q.heal - 1) :
    ∃ D : HealthyRepairScheduleAt S A V Q,
      D.resetTime = a ∧ D.deltaF = ΔF ∧
      D.query = max Q.ready (Healing.drainTime Q.params a) ∧
      D.oldLabel = Q.params.slot a + 2 * Q.params.k + 4 := by
  obtain ⟨-, hlower⟩ := healthy_repair_lower S A V Q.run Q.hn Q.gst a
  exact ⟨{
    resetTime := a
    deltaF := ΔF
    reset := hreset
    cleanLabel := Healing.cleanLabel Q.params a
    cleanLabel_eq := rfl
    oldLabel := Q.params.slot a + 2 * Q.params.k + 4
    old_bound := by
      change Healing.cleanLabel Q.params a + 2 * Q.params.k + 1 ≤
        Q.params.slot a + 2 * Q.params.k + 4
      rw [Healing.cleanLabel_eq]; omega
    query := max Q.ready (Healing.drainTime Q.params a)
    lower := hlower
    reserve := hreserve }, rfl, rfl, rfl, rfl⟩

/-- A preparation schedule for the same query supplies a repair schedule with the very same
reset time, service delay and query, without a base-slot comparison. -/
theorem healthy_repair_schedule_of_preparation_at
    (Q : HealthyPreparationQueryAt S A V)
    (W : HealthyBaseTimingAt S A V Q) (Dprep : HealthyPreparationScheduleAt S A V Q W) :
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
theorem healthy_repair_schedule_at
    (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    Nonempty (HealthyRepairScheduleAt S A V Q) := by
  obtain ⟨W', ⟨Dprep⟩⟩ := healthy_preparation_initialize_at S A V Q h0 hb hp
  obtain ⟨D, -⟩ := healthy_repair_schedule_of_preparation_at S A V Q W' Dprep
  exact ⟨D⟩

section Trace

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (AC.Payload sp.n)} {g b : Time}
  {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- Actual tips below compatible origin witnesses are comparable, in the blocks held while
honest. -/
theorem tips_comparable_of_origin_witnesses_at (hU : Coherent (tr.HonestBlocksAt H))
    {R R' C C' : AC.Blk sp.n (List (FG.Att sp.n))}
    (hR : Anc (tr.HonestBlocksAt H) R C) (hR' : Anc (tr.HonestBlocksAt H) R' C')
    (hCC : Goldilocks.Compatible (tr.HonestBlocksAt H) C C') :
    Goldilocks.Compatible (tr.HonestBlocksAt H) R R' := by
  rcases hCC with h | h
  · exact Anc.total hU (hR.trans h) hR'
  · exact Anc.total hU hR (hR'.trans h)

/-- An opening is after the joining slot `slot ḡ + 1`. -/
theorem repair_opening_join (D : RepairSchedule tr H proposer dg g b cm βK)
    (O : RepairOpening D) : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts O.slot := by
  have hgu := O.late
  have hbase := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g) (sp.slot (AC.gbar g))).mpr le_rfl
  simp only [AC.ACParams.ts] at hbase hgu ⊢
  push_cast at hbase hgu ⊢
  linarith

/-- **Any operational opening repairs the post-update source cover**, under growing faults. No
current-read geometry or prior repair invariant is used. -/
theorem receiver_repair_of_opening_at (D : RepairSchedule tr H proposer dg g b cm βK)
    (O : RepairOpening D) : ReceiverRepair D O := by
  rw [receiverRepair_iff]
  have hTb := O.service
  intro y hy
  obtain ⟨j, ell, _, hu, _⟩ := D.reset.update_toFG_calls_at hy (repair_opening_join D O) hTb
  have ht : tr.time j = sp.ts O.slot + 6 * sp.Δ := hu.2.2.1
  refine ⟨j, ell, hu, ht, ht ▸ hTb, ?_⟩
  intro R hlookup
  have hyj : y ∈ H (tr.time j) := ht ▸ hy
  obtain ⟨x, q, s, CV, hx, hqj, hqt, hs, hsource⟩ :=
    Healing.Growing.operational_update_recent_source_at D.reset O.held rfl O.proposes
      O.label O.drain O.late hTb hyj hu hlookup
  exact ⟨x, q, s, R, CV, hx, hqj, hqt, O.old_lt.le.trans hs, hsource, .refl⟩

/-- **Repair cover at a read point**, under growing faults. For a reader honest at its read time
`t`, at or after the opening's update, whose read cut `n` is after the update, the record before
cut `n` (read at `t`) is its finalized block or below a result or optimistic lock of a node honest
at its own cut, before `n` and by `t`. The reader is honest at the update, so the opening repaired
it (`receiver_repair_of_opening_at`); its update cut, at time `t_slot + 6Δ < tr.time n`, is before
`n`. -/
theorem record_sources_before_now_at (D : RepairSchedule tr H proposer dg g b cm βK)
    (O : RepairOpening D) {y : Fin sp.n} {n : Nat} {t : Time}
    (hrp : Regimes.ReadPoint tr n t) (hy : y ∈ H t)
    (hTt : sp.ts O.slot + 6 * sp.Δ ≤ t) (hTn : sp.ts O.slot + 6 * sp.Δ < tr.time n) :
    RecordCover tr H D.cleanLabel y n t
      ((AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed).getD
        (tr.state y n).fg.F) := by
  rw [recordCover_iff]
  have hrun := D.reset.run
  have hnc := D.reset.noColl
  have h6 : (0 : Time) ≤ 6 * sp.Δ := mul_nonneg (by decide) sp.toParams.hΔ.le
  have ht0 : 0 ≤ t := by linarith [Compose.Growing.ts_natCast_nonneg (sp := sp) O.slot]
  obtain ⟨a, ell, ha, hat, -, hcover⟩ := receiverRepair_iff.mp (receiver_repair_of_opening_at D O)
    y (hrun.antitone hTt hy)
  have han : a < n := by
    by_contra h
    have := hrun.time_mono (Nat.le_of_not_lt h)
    linarith
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hind : ∀ k, a + 1 ≤ k → k ≤ n → ∀ R,
      AC.lookup (Node.frame (tr.state y k)) (tr.state y k).ac.latestConfirmed =
        some R →
      ∃ x q s C CV, x ∈ H (tr.time q) ∧ q < k ∧ tr.time q ≤ t ∧
        D.oldLabel ≤ s ∧
        (AC.ResultAt tr.projAC x q s C CV ∨ AC.OptimisticLockAt tr.projAC x q s C CV) ∧
        Anc (tr.HonestBlocksAt H) R C := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro _ R hR
      obtain ⟨x, q, s, C, CV, hx, hqa, hqt, hs, hC, hRC⟩ := hcover R hR
      exact ⟨x, q, s, C, CV, hx, Nat.lt_succ_of_le hqa, hqt.trans (hat ▸ hTt), hs, hC, hRC⟩
    | succ k hak ih =>
      intro hkn R hR
      have hle1 : ∀ q < k + 1, tr.time q ≤ t := fun q hq => hrp.1 q (by omega)
      have hle0 : ∀ q < k, tr.time q ≤ t := fun q hq => hrp.1 q (by omega)
      have hkt : tr.time k ≤ t := hrp.1 k (by omega)
      have hyk : y ∈ H (tr.time k) :=
        hrun.antitone hkt hy
      rcases record_step_origin_at hrun hyk with heq | ⟨C, hC, hCr, s, CV, hs⟩
      · obtain ⟨x, q, s, B, DV, hx, hqk, hqb, hsl, hB, hRB⟩ :=
          ih (Nat.le_of_succ_le hkn) R
            (record_lookup_of_later_at hrun hnc ht0 hle1 hy (Nat.le_succ k) heq hR)
        exact ⟨x, q, s, B, DV, hx, Nat.lt_succ_of_lt hqk, hqb, hsl, hB, hRB⟩
      · obtain ⟨hRm, hRr⟩ := AC.lookup_eq_some hR
        have hRC : R = C := hU.1 ⟨y, k + 1, t, ht0, hle1, hy, hRm.1⟩
          ⟨y, k, t, ht0, hle0, hy, hC⟩ (hRr.trans hCr.symm)
        have htk : sp.ts O.slot + 6 * sp.Δ ≤ tr.time k := by
          rw [← hat]
          exact hrun.time_mono (Nat.le_of_succ_le hak)
        have hsl : D.oldLabel ≤ s := by
          have hus : O.slot ≤ s := by
            rcases hs with ⟨ell, hu, _⟩ | ⟨ell, A, ho, hslot, _⟩
            · have ht : tr.time k = sp.ts s + 6 * sp.Δ := hu.2.2.1
              have hh := (AC.ts_le_iff sp).mp
                (le_of_add_le_add_right (htk.trans_eq ht))
              omega
            · have hh := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg k) O.slot).mp
                ((le_add_of_nonneg_right h6).trans htk)
              change sp.slot (tr.time k) = s at hslot
              omega
          exact O.old_lt.le.trans hus
        exact ⟨y, k, s, C, CV, hyk, Nat.lt_succ_self _, hkt, hsl, hs, by rw [hRC]; exact .refl⟩
  cases hl : AC.lookup (Node.frame (tr.state y n)) (tr.state y n).ac.latestConfirmed with
  | none => exact Or.inl (by simp only [Option.getD_none])
  | some R =>
    obtain ⟨x, q, s, C, CV, hx, hqn, hqb, hs, hC, hRC⟩ := hind n han le_rfl R hl
    exact Or.inr ⟨x, q, s, C, CV, hx, hqn, hqb, D.old_bound.trans hs, hC,
      by simpa only [hl, Option.getD_some] using hRC⟩


end Trace

end Consensus.Goldilocks.Obligations.Growing

end
