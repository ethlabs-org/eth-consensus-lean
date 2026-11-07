module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Pending
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.SysLog

public section

/-! # The repairing opening of a healed-safety query under growing faults

* `healthy_repair_catch_at`: the query's catch-up from its partial synchrony and awake honest
  nodes;
* `healthy_bounded_repairing_opening_at`: the progress recurrence on `[ready, heal]` supplies an
  opening, a proposal of a proposer ready at its slot start and still honest `Δ` later, within the
  repair window; every receiver ready at its update is then repaired
  (`healthy_receiver_repair_of_opening_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The catch-up service of a healed-safety query. -/
theorem healthy_repair_catch_at (Q : HealthyPreparationQueryAt S A V) :
    Healing.Growing.CatchRun Q.trace Q.keys Q.gst (2 * Q.params.Δ) := by
  have hnet : Q.run.2.log.PSync Q.run.2.point Q.gst :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.healthy.1
  exact catchRun_of_psync_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) hnet
    (fun v u hu hub hv => Q.healthy.2.1.2 v u hu hub hv)

/-- An honest proposal is accepted by its proposer, honest at the proposal. -/
private theorem proposal_accepted_at {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hp : p ∈ H (tr.time k))
    (hP : tr.ProposesAt p k P) : tr.AcceptAt p k P := by
  have hd := hrun.time_nonneg k
  have h := Compose.proposal_accepted (hrun.upTo hd) (hnc.upTo _) hp
    ⟨(RunTrace.upTo_ownBlockAt tr).2 ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  exact ((RunTrace.upTo_acceptAt tr).1 h).2

/-- **The repairing opening**: the progress recurrence on `[ready, heal]` supplies an actual
opening of a proposer ready at its slot start and still honest `Δ` later; finite catch and the
operational selection then repair every receiver ready at its update. -/
theorem healthy_bounded_repairing_opening_at (Q : HealthyPreparationQueryAt S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run)
    (D : HealthyRepairScheduleAt S A V Q) :
    ∃ O : HealthyRepairOpeningAt S A V Q D, HealthyReceiverRepairAt S A V Q D O := by
  classical
  have hcap : Q.cap ≠ .final := by rcases Q.nonfinal with h | h <;> simp [h]
  have hrec : PatternRecurrence Q.run.2.point Q.run.2.key
      (fun s => Q.run.2.sel (.proposer s)) (goldilocks S (Model.pubOf Q.run.1)).skel.grid
      ⟨Pattern.single, Q.index, 1⟩ ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      Q.ready Q.heal := by
    simpa only [System.prog, shapeProgress, shapeHolds, goldilocksContract, ite_eq_right hcap,
      Model.sysExternal, System.cDur, System.pt, Sys, Model.sysOf, Model.Run.point] using hp
  have hq0 : 0 ≤ D.query := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans D.lower)))
  have hq : max Q.ready 0 ≤ D.query := max_le ((le_max_left _ _).trans D.lower) hq0
  have hd := Q.params.toParams.hΔ
  have hwin : D.query + (Q.index : Time) * (4 * Q.params.Δ) ≤ Q.heal := by
    linarith only [D.reserve, hd]
  obtain ⟨s, hlo, hhi, hr⟩ := hrec D.query hq hwin (hwin.trans hb)
  have htime : (goldilocks S (Model.pubOf Q.run.1)).skel.grid.slotTime s = Q.params.ts s := by
    change (s : Time) * (4 * Q.run.1.ΔAC) = 4 * Q.run.1.ΔAC * s
    ring
  rw [htime] at hlo hhi
  have hbound : Q.params.ts s ≤ D.query + 4 * (Q.index : Time) * Q.params.Δ := by
    change Q.params.ts s ≤ D.query + (Q.index : Time) * (4 * Q.params.Δ) at hhi
    linarith only [hhi]
  have hsΔ : Q.params.ts s + Q.params.Δ ≤ Q.run.2.horizon := by
    linarith only [hbound, D.reserve, hb, hd]
  have hsb : Q.params.ts s ≤ Q.run.2.horizon := by linarith only [hsΔ, hd]
  have hready := hr 0 (by simp [Pattern.single])
  simp only [Nat.add_zero] at hready
  have hmem : runProposer S Q.run.2 Q.hn s ∈ Q.run.2.sel (.proposer s) := by
    simp only [runProposer_eq, dite_eq_left hready.1]
    exact Finset.min'_mem _ _
  obtain ⟨hR, hH⟩ := hready.2 _ hmem
  rw [htime] at hR hH
  have hkey : Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn s)) =
      runProposer S Q.run.2 Q.hn s := Q.run.2.key.symm_apply_apply _
  have hnode := ready_transport_at S Q.run.2 Q.hn Q.valid (hq0.trans hlo.le) hsb hR
  rw [hkey] at hnode
  have hheld : runProposer S Q.run.2 Q.hn s ∈ Q.keys (Q.params.ts s + Q.params.Δ) := by
    have hla : Q.run.2.point.lookAhead (((1 : Nat) : Time) * Q.run.2.point.env.ΔAC)
        (Q.params.ts s) = Q.params.ts s + Q.params.Δ := by
      change min (Q.params.ts s + ((1 : Nat) : Time) * Q.run.1.ΔAC) Q.run.2.horizon =
        Q.params.ts s + Q.run.1.ΔAC
      rw [Nat.cast_one, one_mul]
      exact min_eq_left hsΔ
    rw [hla] at hH
    have h := honest_ownKey_at S Q.run.2 hH hsΔ
    rwa [hkey] at h
  have hold : D.oldLabel < s := by
    exact_mod_cast (SA.ts_lt_iff Q.params).mp
      (lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans D.lower))) hlo)
  have hshort : Regimes.Growing.ReadyAt Q.trace Q.keys (Regimes.catchUp Q.params)
      (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) := by
    refine ⟨hnode.1, fun t ht hts => hnode.2 t ?_ hts⟩
    apply le_trans _ ht
    apply max_le_max_left
    have : Regimes.catchUp Q.params ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run := by
      simpa only [Regimes.catchUp] using D.duration_bound
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
  let O : HealthyRepairOpeningAt S A V Q D :=
    ⟨s, k, P, hlo, hbound, hold, hlabel, hP, proposal_accepted_at hrun hnc hpk hP, ht, hnode,
      hheld⟩
  exact ⟨O, healthy_receiver_repair_of_opening_at S A V Q hb D O (healthy_repair_catch_at S A V Q)⟩

end Consensus.Goldilocks.Obligations.Growing

end
