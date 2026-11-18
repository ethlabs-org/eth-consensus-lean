module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.RepairDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.PSync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Selection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Preparation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.SuffixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyRepairTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed

public section

/-! # The repairing opening of a healed-safety query under growing faults

`healthy_bounded_repairing_opening_at`: the progress recurrence on `[ready, heal]` supplies an
opening, a proposal of a proposer ready at its slot start and still honest `Δ` later, within the
repair window. Every receiver ready at its update is then repaired
(`receiver_repair_of_opening_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The repairing opening**: the progress recurrence on `[ready, heal]` supplies an actual
opening of a proposer ready at its slot start and still honest `Δ` later, within the progress
window after the schedule's query. -/
theorem healthy_bounded_repairing_opening_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (D : HealthyRepairScheduleAt S A V Q) :
    Nonempty (HealthyRepairOpeningAt S A V Q D) := by
  classical
  have hcap : Q.cap ≠ .final := by rcases Q.nonfinal with h | h <;> simp [h]
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s))
          (goldilocks S (Model.pubOf Q.run.1)).skel.grid
      ⟨Pattern.single, Q.index, 1⟩
      ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      Q.ready Q.heal := by
    simpa only [System.prog, shapeProgress, shapeHolds, goldilocksContract, ite_eq_right hcap,
      Model.sysExternal, System.cDur, System.pt, Sys, Model.sysOf, Model.Run.point] using hp
  have hq0 : 0 ≤ D.query := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))
  have hq : max Q.ready 0 ≤ D.query := max_le ((le_max_left _ _).trans D.lower) hq0
  have hd := Q.params.toParams.hΔ
  have hwin : D.query + (Q.index : Time) * (4 * Q.params.Δ) ≤ Q.heal := by
    linarith only [D.reserve, hd]
  have hbh : Q.heal ≤ Q.run.2.horizon := hb.trans Q.bound_le
  obtain ⟨s, hlo, hhi, hr⟩ := hrec D.query hq hwin (hwin.trans hbh)
  have htime : (goldilocks S (Model.pubOf Q.run.1)).skel.grid.slotTime s =
      Q.params.ts s := by
    change (s : Time) * (4 * Q.run.1.ΔAC) = 4 * Q.run.1.ΔAC * s
    ring
  rw [htime] at hlo hhi
  have hbound : Q.params.ts s ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ := by
    change Q.params.ts s ≤ D.query + (Q.index : Time) * (4 * Q.params.Δ) at hhi
    linarith only [hhi]
  have hsΔ : Q.params.ts s + Q.params.Δ ≤ Q.run.2.horizon := by
    linarith only [hbound, D.reserve, hbh, hd]
  have hsb : Q.params.ts s ≤ Q.run.2.horizon := by linarith only [hsΔ, hd]
  have hready := hr 0 (by simp [Pattern.single])
  simp only [Nat.add_zero] at hready
  have hmem : runProposer S Q.run.2 Q.hn s ∈ Q.run.2.sel (.proposer s) := by
    rw [runProposer_eq S Q.run.2 Q.hn]
    split
    · exact Finset.min'_mem _ _
    · exact absurd hready.1 ‹_›
  obtain ⟨hR, hH⟩ := hready.2 _ hmem
  rw [htime] at hR hH
  have hkey : Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn s)) =
      runProposer S Q.run.2 Q.hn s := Q.run.2.key.symm_apply_apply _
  have hnode := ready_transport_at S Q.run.2 Q.hn Q.valid
    (hq0.trans hlo.le) hsb hR
  rw [hkey] at hnode
  have hheld : runProposer S Q.run.2 Q.hn s ∈
      Q.keys (Q.params.ts s + Q.params.Δ) := by
    have hla : Q.run.2.point.lookAhead (((1 : Nat) : Time) * Q.run.2.point.env.ΔAC)
        (Q.params.ts s) = Q.params.ts s + Q.params.Δ := by
      change min (Q.params.ts s + ((1 : Nat) : Time) * Q.run.1.ΔAC) Q.run.2.horizon =
        Q.params.ts s + Q.run.1.ΔAC
      rw [Nat.cast_one, one_mul]
      exact min_eq_left hsΔ
    rw [hla] at hH
    have h := honest_ownKey_at S Q.run.2 hH hsΔ
    rw [hkey] at h
    exact h
  have hold : D.oldLabel < s := by
    exact_mod_cast (SA.ts_lt_iff Q.params).mp
      (lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans D.lower))) hlo)
  have hshort : Regimes.Growing.ReadyAt Q.trace Q.keys (Regimes.catchUp Q.params)
      (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) := by
    refine ⟨hnode.1, fun t ht hts => hnode.2 t ?_ hts⟩
    apply le_trans _ ht
    apply max_le_max_left
    have : Regimes.catchUp Q.params ≤
        (Sys (goldilocks S) V).cDur (K S A) Q.run := by
      simpa only [Regimes.catchUp] using
        (healthy_repair_lower S A V Q.run Q.hn Q.gst D.resetTime).1
    linarith only [this]
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  obtain ⟨k, P, hP, ht⟩ := Regimes.Growing.ready_proposer_proposes_at hrun hnc (s := s)
    (Nat.zero_le D.oldLabel |>.trans_lt hold) hshort
  have hlabel : P.slot = s := by
    have := hP.2.2
    rw [ht] at this
    rw [Q.params.slotTime_eq] at this
    have he : (P.slot : Time) = (s : Time) := by
      simp only [SA.SAParams.ts] at this
      exact (mul_left_cancel₀ (mul_pos (by norm_num : (0 : Time) < 4) hd).ne' this).symm
    exact_mod_cast he
  have hpk : runProposer S Q.run.2 Q.hn s ∈ Q.keys (Q.trace.time k) := by
    rw [ht]; exact hnode.1
  obtain ⟨hservice, hdrain, hlate, -⟩ := healthy_opening_timing D.lower hlo hbound D.reserve hb
  exact ⟨{ toRepairOpening := ⟨s, k, P, hdrain, hlate, hservice, hold, hlabel, hP,
             proposal_accepted_at hrun hnc hpk hP, ht, hheld⟩
           bounded := hbound }⟩

end Consensus.Goldilocks.Obligations.Growing

end
