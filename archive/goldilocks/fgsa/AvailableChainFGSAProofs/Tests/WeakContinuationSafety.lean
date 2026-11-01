module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Induction
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Replay -- shake: keep (WC checks)
public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuation

public section

/-! WC plan §8 Job 2; DC reviewed propositions and complete continuation safety. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationSafety

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}
    {G ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- WC plan §8 Job 2; DC the source producers and replay supply all five continuation fields. -/
theorem continuationSafety (hS : StrongRecoverySearchPrefix₂ p c E source G ΔF)
    (hinput : HealingInput p c E source w ΔF) (hend : tstar p w < source.horizon)
    (hc : CleanContinuationSleep₂ p c E source E' rho ΔF)
    :
    SSafeFromCut₂ p c E' rho (afterTicksIdx source (tstar p w)) w.QStar ΔF := by
  obtain ⟨cut, hs⟩ := wc_heightSeed hS hinput hend
  have hs' := wc_seedReplay hc.agrees hS.base.valid hs cut.beforeEnd
  apply wc_dischargeContinuation hS hc hs (wc_sourceJoinCut hinput.wit)
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead
  exact wc_seededSafeFromCut hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs'

-- WC plan §8 Job 2; DC each reviewed proposition has a producer with no added premise.
example : WCFinalizedCrossingStatement := wc_finalizedCrossing
example : WCFinalizedOccurrenceStatement p c E rho := wc_finalizedOccurrence
example : WCLowFinalizedStatement p c E rho w iStar := wc_lowFinalized
example : WCSourceOriginStatement p c E rho := wc_sourceOrigin
example : WCSourceLabelStatement p c E rho := wc_sourceLabel
example : WCFinalityTargetEarlierStatement p c E rho := wc_finalityTargetEarlier
example : WCSeededFrameStatement p c E rho ΔF w iStar := wc_seededFrame
example : WCSeededFrameLiveStatement p c E rho ΔF w iStar := wc_seededFrameLive
example : WCSeededFramePathStatement p c E rho ΔF w iStar := wc_seededFramePath
example : WCInitStatement p c E rho ΔF w iStar := wc_init
example : WCStepDeliveryStatement p c E rho ΔF w iStar := wc_stepDelivery
example : WCStepNoGateTickStatement p c E rho ΔF w iStar := wc_stepNoGateTick
example : WCStepGateTickStatement p c E rho ΔF w iStar := wc_stepGateTick
example : WCStepRestartStatement p c E rho ΔF w iStar := wc_stepRestart
example : WCStepStatement p c E rho ΔF w iStar := wc_step
example : WCSeededInductionStatement p c E rho ΔF w iStar := wc_seededInduction
example : WCRetrospectiveStatement p c E rho ΔF w iStar := wc_retrospective
example : WCService4Statement p c E rho ΔF w iStar := wc_service4
example : WCSeededSafetyStatement p c E rho w iStar := wc_seededSafety
example : WCFinalBelowStatement p c E rho ΔF w iStar := wc_finalBelow

end AvailableChain.FGSA.Run.Tests.WeakContinuationSafety
end
