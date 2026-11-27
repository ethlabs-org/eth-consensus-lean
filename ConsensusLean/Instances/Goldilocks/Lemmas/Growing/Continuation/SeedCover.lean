module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frontier.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Opening
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SeedCall
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignCalendar
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.SignGap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Attest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HealedMembers
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.SignGap

public section

/-! # The hand-over seed of a healed-safety query

`Obligations.Growing.handover_seed_cover_at`: a healed-safety query healthy up to its bound, with
`heal ≤ bound` and progress on `[ready, heal]`, gives a seed at `T = bound` at the preparation
reset's FG delay and release hold, and its record cover from a start `t₀ ∈ [t_{r+k}, T]` with
`t₀ + 8Δ + 1 ≤ heal`. Split from `Healing/Frontier/Seed`, which stays below the healthy
preparation modules this one reads. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The hand-over seed of a healed-safety query, with its record cover** healthy up to its bound
`T`, with `0 ≤ heal ≤ T` and progress on `[ready, heal]`. The repair schedule supplies the reset `a`
and the record cover from `t₀ = query + (4i + 6)Δ + 1` on; its reset premises are the
preparation's, at its FG delay and release hold. The lock floor
is `r = cleanLabel a + k + 2` and the split slot is `σ = slot T − 2`, so
`t_σ + 8Δ = t_{slot T} ≤ T`. The schedule puts `drainTime a = t_{r+k}` at or
before the query, so `t_{r+k+2} < T`, `r + k ≤ σ` and `t_{r+k} ≤ t₀`. The canonical preparation
query is at most `ready + (R + 8k + 20)Δ`, and the heal margin leaves `8Δ + 1` after the cover
start: `t₀ + 8Δ + 1 ≤ heal`. -/
theorem handover_seed_cover_at
    (Q : HealthyPreparationQueryAt
    S A V) (h0 : 0 ≤ Q.heal)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (hcover : HealthyQueryCover S A V Q) :
    ∃ r σ ΔF, 0 < ΔF ∧ Compose.Growing.HandoverSeed Q.trace Q.keys
        (runProposer S Q.run.2 Q.hn)
        (digestOf S Q.run.2) Q.gst ΔF Q.bound r σ
        (cm := runCommittee S Q.run.2 Q.hn)
        (βK := (K S A).params.βK) ∧
      ∃ t₀, t₀ ≤ Q.bound ∧ Q.params.ts (r + Q.params.k : Nat) ≤ t₀ ∧
        t₀ + 8 * Q.params.Δ + 1 ≤ Q.heal ∧
        ∀ y n t, t₀ ≤ t → t ≤ Q.bound → y ∈ Q.keys t → Regimes.ReadPoint Q.trace n t →
          Compose.Growing.HealedRecordCoverAt Q.trace Q.keys (r + Q.params.k - 1) y n t
            ((AC.lookup (Node.frame (Q.trace.state y n))
              (Q.trace.state y n).ac.latestConfirmed).getD (Q.trace.state y n).fg.F) := by
  obtain ⟨W, Dprep, hlate⟩ := healthy_preparation_initialize_late_at
    S A V Q h0 hb hp
    (simTraceAt_signCalendar S Q.run.2 Q.hn _) (Obligations.signGapAt_of_assumptions A _ _)
    (Obligations.signGap_δt A) (Obligations.contract_heal_ge_reset_signGap A Q.cap Q.index)
    A.fgSlots_releaseGap_signGap_le hcover
  obtain ⟨D, -, -, hDq⟩ := healthy_repair_schedule_of_preparation_at
    S A V Q W Dprep
  obtain ⟨O⟩ := healthy_bounded_repairing_opening_at
      S A V Q hb hp D
  have hreset := D.reset
  have hΔ := Q.params.toParams.hΔ
  have hX : (1 : Time) ≤ (Q.index : Time) := by exact_mod_cast Q.index.1.pos
  have hdrain : Healing.drainTime Q.params D.resetTime ≤ D.query :=
    (le_max_left _ _).trans ((le_max_right _ _).trans D.lower)
  have hres := D.reserve
  have hT0 : 0 ≤ Q.bound := h0.trans hb
  -- the drain slot `r + k` ends two slots before the slot of `T`
  have hslot : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 4 ≤
      Q.params.slot Q.bound := by
    have h := (AC.ts_le_iff_le_slot Q.params hT0
      ((Q.params.slot D.resetTime + 2 * Q.params.k + 7 : Nat) : Int)).mp (by
        rw [Healing.drainTime_eq] at hdrain
        have h : Q.params.ts (Q.params.slot D.resetTime + 2 * Q.params.k + 7 : Nat) =
            Q.params.ts (Q.params.slot D.resetTime + 2 * Q.params.k + 5 : Nat) +
              8 * Q.params.Δ := by
          simp only [AC.ACParams.ts]; push_cast; ring
        linarith [mul_le_mul_of_nonneg_right hX hΔ.le])
    rw [Healing.cleanLabel_eq]
    omega
  have hcov : ∀ y n t, D.query + (4 * (Q.index : Time) + 6) * Q.params.Δ + 1 ≤ t →
      t ≤ Q.bound → y ∈ Q.keys t → Regimes.ReadPoint Q.trace n t →
      Compose.Growing.HealedRecordCoverAt Q.trace Q.keys
        (Healing.cleanLabel Q.params D.resetTime + Q.params.k + 2 + Q.params.k - 1) y n t
        ((AC.lookup (Node.frame (Q.trace.state y n)) (Q.trace.state y n).ac.latestConfirmed).getD
          (Q.trace.state y n).fg.F) := by
    intro y n t ht htb hy hrp
    have hT : Q.params.ts O.slot + 6 * Q.params.Δ < t := by linarith [O.bounded]
    have hcover := record_sources_before_now_at D.toRepairSchedule O.toRepairOpening hrp hy hT.le
      (hT.trans_le hrp.2)
    rw [recordCover_iff, D.cleanLabel_eq] at hcover
    rw [Compose.Growing.healedRecordCoverAt_iff]
    rcases hcover with h | ⟨x, q, s, C, CV, hx, hqn, hqt, hs, hC, hRC⟩
    · exact Or.inl h
    · have hs' : Healing.cleanLabel Q.params D.resetTime + 2 * Q.params.k + 1 ≤ s := hs
      exact Or.inr ⟨x, q, s, C, CV, hx, hqn, hqt, by omega, hC, hRC⟩
  have hdr : Q.params.ts (Healing.cleanLabel Q.params D.resetTime + Q.params.k + 2 +
      Q.params.k : Nat) = Healing.drainTime Q.params D.resetTime := by
    rw [Healing.drainTime_eq, Healing.cleanLabel_eq]
    congr 2
    omega
  have hkk : Q.params.k = (S.params (Model.pubOf Q.run.fst) Q.hn).k := rfl
  refine ⟨Healing.cleanLabel Q.params D.resetTime + Q.params.k + 2, Q.params.slot Q.bound - 2,
    D.deltaF, hreset.sync.deltaF, Compose.Growing.HandoverSeed.of_reset hreset rfl ?_
      (by omega) ⟨_, by linarith, hcov⟩,
    _, by linarith, by rw [hdr]; linarith [mul_le_mul_of_nonneg_right hX hΔ.le],
    by rw [hDq]; linarith, hcov⟩
  have h : Q.params.ts ((Q.params.slot Q.bound - 2 : Nat) : Int) + 8 * Q.params.Δ =
      Q.params.ts (Q.params.slot Q.bound : Int) := by
    simp only [AC.ACParams.ts]; push_cast [show 2 ≤ Q.params.slot Q.bound by omega]; ring
  rw [h]
  exact (AC.ts_le_iff_le_slot Q.params hT0 _).mpr le_rfl

end Consensus.Goldilocks.Obligations.Growing

end
