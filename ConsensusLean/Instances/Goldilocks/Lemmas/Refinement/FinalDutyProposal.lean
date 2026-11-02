module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.FinalWindowDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting

public section

/-! # Goldilocks Refinement: a final query's proposer duty gives an actual proposal (#136)

`final_duty_proposal_run`: in a final query, an honest-ready proposer duty at a slot `s > 0` whose
slot time is inside the horizon produces the designated proposer's actual proposal at `t_s`,
accepted by its proposer, as an `HonestProposalRun`. It is generic in `s`: the seed slot and
every window anchor use it, and it selects no offsets. Premises are the query's run fields
(`valid`, `noCollision`) and the duty itself; the query's catch-up duration covers the protocol
catch-up `18 Δp` through `accepted_catchUp_ge_sleepy`. No recurrence, reset, M1 or `accepted_heal`
value is used. The chain is the one of `healthy_bounded_repairing_opening` (HealedSafety):
`runProposer` membership, `ready_transport`, `Regimes.ready_proposer_proposes`,
`Compose.proposal_accepted`, `Healing.honestProposalRun_of_proposesAt`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The query's catch-up duration covers the protocol catch-up `18 Δp`. -/
theorem final_catchUp_le_cDur (Q : FinalQuery S A V) :
    Regimes.catchUp Q.params ≤ (Sys (family S) V).cDur (K S A) Q.run := by
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hc : (37 : Time) ≤ ((K S A).params.catchUp : Time) := by
    rw [acceptanceContract_params_eq]
    change (37 : Time) ≤ ((accepted_coefficients S A).catchUp : Nat)
    rw [accepted_coefficients_catchUp]
    exact_mod_cast accepted_catchUp_ge_sleepy S A
  change 18 * (Q.run.1.Δ + 1) ≤ ((K S A).params.catchUp : Time) * Q.run.1.Δ
  nlinarith

/-- **Duty to actual proposal.** An honest-ready proposer duty at a slot `s > 0` with
`t_s ≤ horizon` gives the run proposer's actual proposal `P` of slot `s` at a cut of time `t_s`,
accepted by its proposer, ready there for the query's catch-up duration, and an
`HonestProposalRun`. -/
theorem final_duty_proposal_run (Q : FinalQuery S A V) {s : Nat} (hs : 0 < s)
    (hth : Q.params.ts s ≤ Q.run.2.horizon)
    (hduty : HonestReadyIn Q.run.2.point Q.run.2.key (fun s => Q.run.2.sel (.proposer s)) s
      ((Sys (family S) V).cDur (K S A) Q.run)
      ((family S (Model.pubOf Q.run.1)).skel.grid.slotTime s)) :
    ∃ k P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P ∧
      Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn s) k P ∧
      Q.trace.AcceptAt (runProposer S Q.run.2 Q.hn s) k P ∧
      Q.trace.time k = Q.params.ts s ∧ P.slot = s ∧
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) ((Sys (family S) V).cDur (K S A) Q.run)
        (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) := by
  have htime : (family S (Model.pubOf Q.run.1)).skel.grid.slotTime s = Q.params.ts s := by
    change (s : Time) * (4 * (Q.run.1.Δ + 1)) = 4 * (Q.run.1.Δ + 1) * s
    ring
  have hmem : runProposer S Q.run.2 Q.hn s ∈ Q.run.2.sel (.proposer s) := by
    simp only [runProposer, dite_eq_left hduty.1]
    exact Finset.min'_mem _ _
  have hR := hduty.2 _ hmem
  rw [htime] at hR
  have h0 : (0 : Time) ≤ Q.params.ts s := by
    have := Q.params.toParams.hΔ
    simp only [SA.SAParams.ts]; positivity
  have hnode := ready_transport S Q.run.2 Q.hn Q.valid h0 hth hR
  rw [show Q.run.2.ownKey (Q.run.2.key (runProposer S Q.run.2 Q.hn s)) =
    runProposer S Q.run.2 Q.hn s from Q.run.2.key.symm_apply_apply _] at hnode
  have hshort : Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) (Regimes.catchUp Q.params)
      (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) := by
    refine ⟨hnode.1, fun t ht hts => hnode.2 t ?_ hts⟩
    apply le_trans _ ht
    apply max_le_max_left
    have := final_catchUp_le_cDur S A V Q
    linarith
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision
  obtain ⟨k, P, hP, ht⟩ := Regimes.ready_proposer_proposes hrun hnc hs hshort
  have hlabel : P.slot = s := by
    have := hP.2.2
    rw [ht, Q.params.slotTime_eq] at this
    have he : (P.slot : Time) = (s : Time) := by
      simp only [SA.SAParams.ts] at this
      nlinarith [Q.params.toParams.hΔ]
    exact_mod_cast he
  refine ⟨k, P, Healing.honestProposalRun_of_proposesAt hrun hnc hnode.1 rfl hP hlabel, hP,
    Compose.proposal_accepted hrun hnc hnode.1 hP, ht, hlabel, hnode⟩

end Consensus.Goldilocks.Refinement

end
