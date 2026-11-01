module
public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Replay -- shake: keep (WC checks)

public section

/-! WC J1; DC weak-continuation interface checkpoint.
These tests check source construction, finite replay, the first suffix batch,
and application of every discharged premise to a later-job interface.
The event-step proposition is a test parameter. No event-step proof is supplied. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationInterfaces

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC J1; DC source seed: no extra source or foundation hypothesis is required. -/
theorem sourceSeed (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hinput : HealingInput p c E source w ΔF) (hend : tstar p w < source.horizon) :
    BoundedHealingCut₂ p c E source w.u w.QStar (afterTicksIdx source (tstar p w)) ΔF ∧
      WCSeed p c E source w (afterTicksIdx source (tstar p w)) :=
  wc_heightSeed hS hinput hend

omit [Fintype V] in
/-- WC J1; DC finite replay: agreement and source validity transfer the complete seed. -/
theorem replaySeed (ha : AgreesThrough₂ p c E source E' rho ΔF)
    (hv : V2.D.ExecutionValid E source) (hs : WCSeed p c E source w iStar)
    (hend : SA.gateTime p.toParams w.u < source.horizon) : WCSeed p c E' rho w iStar :=
  wc_seedReplay ha hv hs hend

/-- WC J1; DC first batch: the weak participation rule includes u+1. -/
theorem firstBatch (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuationSleep₂ p c E source E' rho ΔF) (_hs : WCSeed p c E source w iStar)
    (hjoin : E.t_GST ≤ slotStartZ p (w.u : Int))
    (hcover : SA.voteTime p.toParams (w.u + 1) ≤ rho.horizon) :
    (Gen.V2.Duty.faulty rho).card <
      (joinedHonest p E' rho (SA.voteTime p.toParams (w.u + 1))).card :=
  wc_participation hS hc hjoin _ le_rfl hcover

/-- WC J1; DC discharge: all [L] ports match the proposed event-step interface. -/
theorem stepPorts (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hc : CleanContinuationSleep₂ p c E source E' rho ΔF) (_hs : WCSeed p c E source w iStar)
    (hjoin : E.t_GST ≤ slotStartZ p (w.u : Int))
    (step : WCStepStatement p c E' rho ΔF w iStar) :
    WCSeed p c E' rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
      WCInv p c E' rho w iStar i → ∀ e, rho.events[i]? = some e →
        WCInv p c E' rho w iStar (i + 1) :=
  wc_dischargeContinuation hS hc _hs hjoin step

omit [Fintype V] in
/-- WC J1; DC retrospective I2: the receipt index is strictly before the completed gate. -/
theorem retrospective {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hi : WCInv p c E' rho w iStar i) (hr : WCResult p c E' rho w iStar i j x s B) :
    ∀ y ∈ rho.honest, joinedAt p E' rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      ∃ k < j, WCHeadRead p c E' rho k y (s + 1) B :=
  hi.retrospective j x s B hr

#check WCFinalizedCrossingStatement
#check WCFinalizedOccurrenceStatement
#check WCLowFinalizedStatement
#check WCFinalityTargetEarlierStatement
#check WCSeededFrameStatement
#check WCSeededFrameLiveStatement
#check WCSeededFramePathStatement
#check WCInitStatement
#check WCStepDeliveryStatement
#check WCStepNoGateTickStatement
#check WCStepGateTickStatement
#check WCStepRestartStatement
#check WCSeededInductionStatement
#check WCRetrospectiveStatement
#check WCService4Statement
#check WCSeededSafetyStatement
#check WCFinalBelowStatement
#check WCProposalPivotStatement
#check WCProposalAdmissionStatement
#check WCExactProposalStatement
#check WCInclusion6Statement
#check WCCutPublicReadStatement
#check WCGrowthStatement
#check WCSourceOriginStatement
#check WCSourceLabelStatement

end AvailableChain.FGSA.Run.Tests.WeakContinuationInterfaces
end
