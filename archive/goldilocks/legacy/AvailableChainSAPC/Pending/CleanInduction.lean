module
public import AvailableChainSAPC.Proofs.Clean

/-!
The round-17 proposal-choice obligation is discharged in round 18.
This historical interface remains outside the default targets. Its proof
below uses the unchanged Sleepy regime; the invariant argument is no
longer needed. The default theorem is `clean_proposal_choices_from_engine`.
The rejected free-path statement remains in `RejectedCleanInduction`
with its checked counterexample.
-/

@[expose] public section
namespace AvailableChain.SAPC.Pending
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Historical proposal-choice obligation, now proved below. -/
def CleanProposalChoicesObligation {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) : Prop :=
  E.Δ = p.Δ → ∀ rho t₀,
    SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀ →
    JointCleanInvariant p E rho rho.events.length →
    ∀ r, t₀ < proposalTime p r → HonestAwakeProposer E rho r →
      gateTime p r ≤ rho.horizon → ∃ b,
        HonestProposalAt E (sapcInterface p).toInterface rho r b ∧
        ∀ v ∈ rho.honest, (headData p rho r v).target = b

theorem cleanProposalChoicesObligation_from_engine
    {V : Type} [DecidableEq V] [Fintype V] (p : Params) (E : Env V) :
    CleanProposalChoicesObligation p E := by
  intro hΔ rho t₀ hs _
  exact clean_proposal_choices_from_engine p E rho hΔ t₀ hs

#print axioms cleanProposalChoicesObligation_from_engine

end AvailableChain.SAPC.Pending
end
