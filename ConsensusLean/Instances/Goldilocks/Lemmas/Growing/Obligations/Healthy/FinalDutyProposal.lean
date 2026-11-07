module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.FinalPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ProposerGap
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # A final query's proposer duty gives an actual proposal, under growing faults

`final_duty_proposal_run_at`, the growing form of `final_duty_proposal_run`
(`Obligations/FinalDutyProposal`, `ProposerGap.duty_proposal_run`): an honest-ready proposer duty
at a slot `s > 0` with `t_s ≤ horizon`, at the duty hold `Δ_AC` of the final recurrence, gives the
designated proposer's actual proposal at `t_s`, accepted by its proposer, as a growing
`HonestProposalRun`. The duty's look-ahead `min (t_s + Δ_AC) horizon` is exactly the proposer's
honesty through `t_s + hold` read by `honestKeysAt`, which clamps at the horizon. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The query's catch-up duration covers the protocol catch-up `18 Δp`. -/
theorem final_catchUp_le_cDur_at (Q : FinalQueryAt S A V) :
    Regimes.catchUp Q.params ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run :=
  catchUp_le_cDur S A V Q.run Q.hn

/-- **Duty to actual proposal** under growing faults. An honest-ready proposer duty at a slot
`s > 0` with `t_s ≤ horizon` and the duty hold `Δ_AC` gives the run proposer's actual proposal `P`
of slot `s` at a cut of time `t_s`, accepted by its proposer, ready there for the query's catch-up
duration, and a growing `HonestProposalRun`. -/
theorem final_duty_proposal_run_at (Q : FinalQueryAt S A V) {s : Nat} (hs : 0 < s)
    (hth : Q.params.ts s ≤ Q.run.2.horizon)
    (hduty : HonestReadyIn Q.run.2.point Q.run.2.key (fun s => Q.run.2.sel (.proposer s)) s
      ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((goldilocks S (Model.pubOf Q.run.1)).skel.grid.slotTime s) Q.run.2.point.env.ΔAC) :
    ∃ k P, Healing.Growing.HonestProposalRun Q.trace Q.keys (runProposer S Q.run.2 Q.hn) s P ∧
      Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn s) k P ∧
      Q.trace.AcceptAt (runProposer S Q.run.2 Q.hn s) k P ∧
      Q.trace.time k = Q.params.ts s ∧ P.slot = s ∧
      Regimes.Growing.ReadyAt Q.trace Q.keys ((Sys (goldilocks S) V).cDur (K S A) Q.run)
        (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) := by
  have htime : (goldilocks S (Model.pubOf Q.run.1)).skel.grid.slotTime s = Q.params.ts s := by
    change (s : Time) * (4 * Q.run.1.ΔAC) = 4 * Q.run.1.ΔAC * s
    ring
  have hmem : runProposer S Q.run.2 Q.hn s ∈ Q.run.2.sel (.proposer s) := by
    simp only [runProposer_eq, dite_eq_left hduty.1]
    exact Finset.min'_mem _ _
  obtain ⟨hR, hH⟩ := hduty.2 _ hmem
  rw [htime] at hR hH
  have h0 : (0 : Time) ≤ Q.params.ts s := by
    have := Q.params.toParams.hΔ
    simp only [SA.SAParams.ts]; positivity
  have hnode := ready_transport_at S Q.run.2 Q.hn Q.valid h0 hth hR
  have hkey : Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn s)) =
      runProposer S Q.run.2 Q.hn s := Q.run.2.key.symm_apply_apply _
  rw [hkey] at hnode
  have hhold : runProposer S Q.run.2 Q.hn s ∈
      Q.keys (Q.params.ts s + Regimes.Growing.hold Q.params) := by
    rw [mem_honestKeysAt_iff]
    change Q.run.2.key _ ∉ Q.run.2.faultyAt (min (Q.params.ts s + Q.run.1.ΔAC) Q.run.2.horizon)
    exact hH
  have hshort : Regimes.Growing.ReadyAt Q.trace Q.keys (Regimes.catchUp Q.params)
      (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) := by
    refine ⟨hnode.1, fun τ hlo hhi => hnode.2 τ ?_ hhi⟩
    refine le_trans (max_le_max_left 0 ?_) hlo
    linarith [final_catchUp_le_cDur_at S A V Q]
  have hrun := simTraceAt_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision
  obtain ⟨k, P, hP, ht⟩ := Regimes.Growing.ready_proposer_proposes_at hrun hnc hs hshort
  have hlabel : P.slot = s := by
    have := hP.2.2
    rw [ht, Q.params.slotTime_eq] at this
    have he : (P.slot : Time) = (s : Time) := by
      simp only [SA.SAParams.ts] at this
      exact mul_left_cancel₀ (mul_pos four_pos Q.params.toParams.hΔ).ne' this.symm
    exact_mod_cast he
  have hk : runProposer S Q.run.2 Q.hn s ∈ Q.keys (Q.trace.time k) := by
    rw [ht]; exact hnode.1
  exact ⟨k, P, Healing.Growing.honestProposalRun_of_proposesAt_at hrun hnc hhold rfl hP hlabel,
    hP, proposal_accepted_at hrun hnc hk hP, ht, hlabel, hnode⟩

end Consensus.Goldilocks.Obligations.Growing

end
