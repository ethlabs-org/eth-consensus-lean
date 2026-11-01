module
public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth -- shake: keep (axiom audit)

public import AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed -- shake: keep (seed axiom audit)

-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Assembly.ContinuationReplay -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Assembly.ContinuationService -- shake: keep

public section

open AvailableChain.FGSA.Run

#print axioms wcg_filtered_replay
#print axioms wcg_eventReplay
#print axioms wcg_beforeReplay
#print axioms wcg_tickEventReplay
#print axioms wcg_readReplay
#print axioms wcg_afterTicksReplay
#print axioms wcg_cut_storeReplay
#print axioms wcg_seed_state
#print axioms wcg_half_of_participation
#print axioms wcg_faultQ_of_half
#print axioms wcg_suffix_faultQ
#print axioms wcg_finalityBlock_of_scope
#print axioms wcg_scope_no_evidence
#print axioms wcg_lowFinalized_of_no_evidence
#print axioms wcg_lowFinalized
#print axioms wcg_init
#print axioms wcg_seededFrame
#print axioms wcg_seededFrameLive
#print axioms wcg_seededFramePath
#print axioms wcg_finalityTargetEarlier
#print axioms wcg_live_of_invariant_inclusion
#print axioms wcg_certifiedOrigin
#print axioms wcg_seedCertified
#print axioms wcg_retained_nonempty
#print axioms wcg_seedCarrier
#print axioms wcg_participation
#print axioms wcg_finalHistoryAt
#print axioms wcg_outputHistoryAt
#print axioms wcg_result_output_compatible
#print axioms wcg_gate_cut_iff
#print axioms wcg_finiteFacts
#print axioms wcg_finiteStep
#print axioms wcg_service4_prefix
#print axioms wcg_service4
#print axioms wcg_gateHeads
#print axioms wcg_gateFinalOrigin
#print axioms wcg_gateBatch
#print axioms wcg_gateResult
#print axioms wcg_reconcileBound
#print axioms wcg_outputStep
#print axioms wcg_retrospectiveFrame
#print axioms wcg_retrospectivePaths
#print axioms wcg_retrospective
#print axioms wcg_stepDelivery
#print axioms wcg_stepNoGateTick
#print axioms wcg_stepGateTick
#print axioms wcg_stepRestart
#print axioms wcg_step
#print axioms wcg_finalBelow
#print axioms wcg_seededInduction
#print axioms wcg_proposalPivot
#print axioms wcg_exactProposal
#print axioms wcg_proposalAdmission
#print axioms wcg_inclusion6
#print axioms wcg_inclusion6_result
#print axioms wcg_sourceParticipation
#print axioms wcg_inclusion6_proved
#print axioms wcg_seededLiveAt
#print axioms wcg_finiteSeed
#print axioms wcg_heightSeed
#print axioms wcg_sourceWitness
#print axioms wcg_outputReplay
#print axioms wcg_empty_outputs
#print axioms wcg_scopedRowOrigins
#print axioms wcg_dischargeL
#print axioms wcg_liveOfSeed
#print axioms wcg_tick_retained
#print axioms wcg_tick_before_cut
#print axioms wcg_time_before_cut
#print axioms wcg_tickSourceReplay
#print axioms wcg_preTickReplay
#print axioms wcg_tickReads
#print axioms wcg_tickPassed
#print axioms wcg_rowSourceReplay
#print axioms wcg_actionReads
#print axioms wcg_retainedSeed
#print axioms assembly_tickReplay_atWake
#print axioms assembly_joinedReplay
#print axioms assembly_wcg_dischargeL
#print axioms wcg_service4OfSeed
#print axioms wcg_service_outputs
#print axioms wcg_sourceJoinCut
#print axioms wcg_sourceWitness_joined
#print axioms wcg_heightSeed_of_finite
#print axioms wcg_retainedSeed_of_finite
end
