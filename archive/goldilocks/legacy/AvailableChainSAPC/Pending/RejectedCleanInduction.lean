module
public import AvailableChainSAPC.Proofs.CleanTicks -- shake: keep (re-export)
public import AvailableChainSAPC.Proofs.CleanInclusion -- shake: keep (re-export)

/-!
Rejected round-9 event obligations, retained only for the checked
round-10 counterexample. The active obligations are in `CleanInduction`. This module is
not imported by any default target. These are proposition definitions,
not axioms, placeholder proofs, or new contract premises.

Round 10: `CleanInductionCounterexample.cleanEventObligations_false`
refutes `CleanEventObligations` as written. Its universal path extension
fails at the first successful early save, even under Sleepy and the cap.
See `Tests/CleanInvariantCounterexample` and docs/SAPC-STATUS.md. These
definitions are retained unchanged to state the exact failed obligation.

Completed steps: initial state, freeze, ticks without a proposal or other
duty, every delivery kind under Sleepy, and proposal ticks under the cap. The local finite-state
gate proof is complete, but the whole joint gate step below is not.

An early tick for r+1 is also the gate tick for r. The obligations below
use the complete actual clock, not independent updates at the same time.
A release tick is the next HEAD tick. Emission itself has no state step.
-/

@[expose] public section
namespace AvailableChain.SAPC.Pending.Rejected
open AvailableChain.Generic AvailableChain.Statements.Generic

def JointEventStep {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (e : Event V (sapc p).Object) : Prop :=
  ∀ index, rho.events[index]? = some e → ∀ path,
    CleanPathFacts p E rho index path →
    ∃ nextPath, (∀ b, path b → nextPath b) ∧
      CleanPathFacts p E rho (index + 1) nextPath

/-- The run assumptions are exactly Sleepy. In particular there is no
cap, root-compatibility, transfer, or proposal-view assumption. -/
def CleanEventObligations {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) : Prop :=
  E.Δ = p.Δ → ∀ rho t₀,
    SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀ →
    -- Early save, with the preceding gate when r > 0.
    (∀ v r, JointEventStep p E rho (.tick v (earlyTime p r))) ∧
    -- HEAD, including same-time release. Frozen/carried PC selection.
    (∀ v r, JointEventStep p E rho (.tick v (voteTime p r))) ∧
    -- Gate, including the next early save at the same time.
    (∀ v r, JointEventStep p E rho (.tick v (gateTime p r))) ∧
    -- Proposal tick: authorize the live PC before choosing the parent.
    (∀ v r, JointEventStep p E rho (.tick v (proposalTime p r)))

/-- The missing proposal step must derive exact raw service from honest
proposal merge and the joint path. This is the premise consumed by
`clean_inclusion_of_joint_and_service`, not a weakened inclusion claim. -/
def CleanProposalServiceObligation {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) : Prop :=
  E.Δ = p.Δ → ∀ rho t₀,
    SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀ →
    ∀ path, CleanPathFacts p E rho rho.events.length path →
    ∀ r, t₀ < proposalTime p r → HonestAwakeProposer E rho r →
      gateTime p r ≤ rho.horizon → ∃ b,
        HonestProposalAt E (sapcInterface p).toInterface rho r b ∧
        ∀ v ∈ rho.honest,
          SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b

end AvailableChain.SAPC.Pending.Rejected
end
