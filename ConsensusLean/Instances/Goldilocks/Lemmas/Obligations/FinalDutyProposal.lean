module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ProposerGap

public section

/-! # Goldilocks Obligations: a final query's proposer duty gives an actual proposal

`final_duty_proposal_run`: in a final query, an honest-ready proposer duty at a slot `s > 0` whose
slot time is inside the horizon produces the designated proposer's actual proposal at `t_s`,
accepted by its proposer, as an `HonestProposalRun`. It is generic in `s`: the seed slot and
every window anchor use it, and it selects no offsets. Premises are the query's run fields
(`valid`, `noCollision`) and the duty itself; the query's catch-up duration covers the protocol
catch-up `18 Δp` through `contract_catchUp_ge_sleepy`. No recurrence, reset, `Healing.M1` route or
`contract_heal` value is used. It is a thin instance of the run-level core `duty_proposal_run`
(`ProposerGap`).
The chain is the one of `healthy_bounded_repairing_opening` (HealedSafety):
`runProposer` membership, `ready_transport`, `Regimes.ready_proposer_proposes`,
`Compose.proposal_accepted`, `Healing.honestProposalRun_of_proposesAt`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The query's catch-up duration covers the protocol catch-up `18 Δp`. -/
theorem final_catchUp_le_cDur (Q : FinalQuery S A V) :
    Regimes.catchUp Q.params ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run :=
  catchUp_le_cDur S A V Q.run Q.hn

/-- **Duty to actual proposal.** An honest-ready proposer duty at a slot `s > 0` with
`t_s ≤ horizon` gives the run proposer's actual proposal `P` of slot `s` at a cut of time `t_s`,
accepted by its proposer, ready there for the query's catch-up duration, and an
`HonestProposalRun`. -/
theorem final_duty_proposal_run (Q : FinalQuery S A V) {s : Nat} {hold : Time} (hs : 0 < s)
    (hth : Q.params.ts s ≤ Q.run.2.horizon)
    (hduty : HonestReadyIn Q.run.2.point Q.run.2.key (fun s => Q.run.2.sel (.proposer s)) s
      ((Sys (goldilocks S) V).cDur (K S A) Q.run)
      ((goldilocks S (Model.pubOf Q.run.1)).skel.grid.slotTime s) hold) :
    ∃ k P, Healing.HonestProposalRun Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) s P ∧
      Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn s) k P ∧
      Q.trace.AcceptAt (runProposer S Q.run.2 Q.hn s) k P ∧
      Q.trace.time k = Q.params.ts s ∧ P.slot = s ∧
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2) ((Sys (goldilocks S) V).cDur (K S A) Q.run)
        (runProposer S Q.run.2 Q.hn s) (Q.params.ts s) :=
  duty_proposal_run S A V Q.run Q.hn Q.constant Q.valid Q.noCollision hs hth hduty

end Consensus.Goldilocks.Obligations

end
