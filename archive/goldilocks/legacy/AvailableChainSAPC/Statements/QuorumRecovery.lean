module
public import AvailableChainSAPC.Statements.Contract

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Recovery with an absolute awake quorum. The awake set may change at
any time. All delivery, recurrence, and horizon fields retain their
Draft 4.3 meaning. This is an additional SA-PC regime. -/
structure QuorumRecoveryRegime {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (G : Time) (E : Env V) (rho : Run V (sapc p)) : Prop where
  execution : ExecutionValid (sapc p) E rho
  rootInjective : RootInjective E (sapcInterface p).toInterface rho
  partialSynchrony : PartialSynchrony (sapc p) E rho
  faultBound : FaultBound (sapc p) (pcFaultCap p) rho
  quorumParticipation : ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
    pcQuorum p ≤ (awakeAt E rho.honest t).card
  recurrence : HonestProposerRecurrence E (sapcInterface p).toInterface rho
    E.t_GST (sapcConstants p G).proposerGap
  horizon : E.t_GST + (sapcConstants p G).recoveryBound ≤ rho.horizon

end AvailableChain.SAPC
end
