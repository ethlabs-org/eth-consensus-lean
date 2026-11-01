module
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Empty -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Live -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Dynamics -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Replay -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Counts -- shake: keep

























-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepReconcile -- shake: keep









public section

open AvailableChain.FGSA.Run

#print axioms AvailableChain.FGSA.Run.WCFinalizedOccurrence
#print axioms AvailableChain.FGSA.Run.WCReceiptOrigins
#print axioms AvailableChain.FGSA.Run.WCHeadRead
#print axioms AvailableChain.FGSA.Run.WCLeaseOrigin
#print axioms AvailableChain.FGSA.Run.WCTargetOrigin
#print axioms AvailableChain.FGSA.Run.WCFiniteFacts
#print axioms AvailableChain.FGSA.Run.WCSeed
#print axioms AvailableChain.FGSA.Run.WCResult
#print axioms AvailableChain.FGSA.Run.WCBelowHistory
#print axioms AvailableChain.FGSA.Run.WCInv
#print axioms AvailableChain.FGSA.Run.WCDutyInput
#print axioms AvailableChain.FGSA.Run.WCControllingRow
#print axioms AvailableChain.FGSA.Run.WCUsableHighSourcesBelow
#print axioms AvailableChain.FGSA.Run.WCFrameBelow
#print axioms AvailableChain.FGSA.Run.WCDutyView
#print axioms AvailableChain.FGSA.Run.WCFrameLiveBelow
#print axioms AvailableChain.FGSA.Run.WCFramePathBelow
#print axioms AvailableChain.FGSA.Run.WCProposalPivot
#print axioms AvailableChain.FGSA.Run.WCProposalAdmittedBeforeVote
#print axioms AvailableChain.FGSA.Run.WCFinalityTargetEarlier
#print axioms AvailableChain.FGSA.Run.WCInitStatement
#print axioms AvailableChain.FGSA.Run.WCStepDeliveryStatement
#print axioms AvailableChain.FGSA.Run.WCStepNoGateTickStatement
#print axioms AvailableChain.FGSA.Run.WCStepGateTickStatement
#print axioms AvailableChain.FGSA.Run.WCStepRestartStatement
#print axioms AvailableChain.FGSA.Run.WCStepStatement
#print axioms AvailableChain.FGSA.Run.WCSeededInductionStatement
#print axioms AvailableChain.FGSA.Run.WCService4Statement
#print axioms AvailableChain.FGSA.Run.WCSeededFrameStatement
#print axioms AvailableChain.FGSA.Run.WCFinalBelowStatement
#print axioms AvailableChain.FGSA.Run.WCProposalPivotStatement
#print axioms AvailableChain.FGSA.Run.WCProposalAdmissionStatement
#print axioms AvailableChain.FGSA.Run.WCExactProposalStatement
#print axioms AvailableChain.FGSA.Run.WCInclusion6Statement
#print axioms AvailableChain.FGSA.Run.WCRetrospectiveStatement
#print axioms AvailableChain.FGSA.Run.WCSeededFrameLiveStatement
#print axioms AvailableChain.FGSA.Run.WCSeededFramePathStatement
#print axioms AvailableChain.FGSA.Run.WCLowFinalizedStatement
#print axioms AvailableChain.FGSA.Run.WCFinalizedOccurrenceStatement
#print axioms AvailableChain.FGSA.Run.WCFinalityTargetEarlierStatement
#print axioms AvailableChain.FGSA.Run.WCFinalizedCrossingStatement
#print axioms AvailableChain.FGSA.Run.WCSeededSafetyStatement
#print axioms AvailableChain.FGSA.Run.WCCutPublicReadStatement
#print axioms AvailableChain.FGSA.Run.WCGrowthStatement
#print axioms AvailableChain.FGSA.Run.WCSourceOriginStatement
#print axioms AvailableChain.FGSA.Run.WCSourceLabelStatement
#print axioms AvailableChain.FGSA.Run.wc_gate_enabled_of_result
#print axioms AvailableChain.FGSA.Run.wc_enabledGate_awakeClosed
#print axioms AvailableChain.FGSA.Run.wc_enabledGate_restartFreeTime
#print axioms AvailableChain.FGSA.Run.wc_enabledGate_of_joinedAt
#print axioms AvailableChain.FGSA.Run.WCResult.enabled
#print axioms AvailableChain.FGSA.Run.wc_gate_raw_enabled
#print axioms AvailableChain.FGSA.Run.wc_gate_pre_joined
#print axioms AvailableChain.FGSA.Run.wc_gate_suppressed
#print axioms AvailableChain.FGSA.Run.wc_joined_gate_witness
#print axioms AvailableChain.FGSA.Run.wc_joined_participation_split
#print axioms AvailableChain.FGSA.Run.wc_enabledGate_service_epoch
#print axioms AvailableChain.FGSA.Run.wc_gate_cut_iff
#print axioms AvailableChain.FGSA.Run.wc_currentEpoch_result
#print axioms AvailableChain.FGSA.Run.wc_joined_retrospective_witness
#print axioms AvailableChain.FGSA.Run.wc_receipt_anchor_deadline
#print axioms AvailableChain.FGSA.Run.wc_receipt_anchor_late
#print axioms AvailableChain.FGSA.Run.wc_eventsReplay
#print axioms AvailableChain.FGSA.Run.wc_eventReplay
#print axioms AvailableChain.FGSA.Run.wc_prefixReplay
#print axioms AvailableChain.FGSA.Run.wc_tickReplay
#print axioms AvailableChain.FGSA.Run.wc_emitsReplay
#print axioms AvailableChain.FGSA.Run.wc_storeReplay
#print axioms AvailableChain.FGSA.Run.wc_cutReplay
#print axioms AvailableChain.FGSA.Run.wc_tickIdxReplay
#print axioms AvailableChain.FGSA.Run.wc_preTickReplay
#print axioms AvailableChain.FGSA.Run.wc_postClockReplay
#print axioms AvailableChain.FGSA.Run.wc_headReplay
#print axioms AvailableChain.FGSA.Run.wc_sourceReplay
#print axioms AvailableChain.FGSA.Run.wc_rowReplay
#print axioms AvailableChain.FGSA.Run.wc_acceptsReplay
#print axioms AvailableChain.FGSA.Run.wc_stepReplay
#print axioms AvailableChain.FGSA.Run.wc_dutyReplay
#print axioms AvailableChain.FGSA.Run.wc_gateInReplay
#print axioms AvailableChain.FGSA.Run.wc_gateReplay
#print axioms AvailableChain.FGSA.Run.wc_fastReplay
#print axioms AvailableChain.FGSA.Run.wc_gateAtReplay
#print axioms AvailableChain.FGSA.Run.wc_passedReplay
#print axioms AvailableChain.FGSA.Run.wc_headAtReplay
#print axioms AvailableChain.FGSA.Run.wc_seedReplay
#print axioms AvailableChain.FGSA.Run.wc_readReplay
#print axioms AvailableChain.FGSA.Run.wc_beforeReplay
#print axioms AvailableChain.FGSA.Run.wc_timeIdxReplay
#print axioms AvailableChain.FGSA.Run.wc_afterTicksReplay
#print axioms AvailableChain.FGSA.Run.wc_init
#print axioms AvailableChain.FGSA.Run.WCGInitStatement
#print axioms AvailableChain.FGSA.Run.WCGStepDeliveryStatement
#print axioms AvailableChain.FGSA.Run.WCGStepNoGateTickStatement
#print axioms AvailableChain.FGSA.Run.WCGStepGateTickStatement
#print axioms AvailableChain.FGSA.Run.WCGStepRestartStatement
#print axioms AvailableChain.FGSA.Run.WCGStepStatement
#print axioms AvailableChain.FGSA.Run.WCGSeededInductionStatement
#print axioms AvailableChain.FGSA.Run.WCGService4Statement
#print axioms AvailableChain.FGSA.Run.WCGSeededFrameStatement
#print axioms AvailableChain.FGSA.Run.WCGFinalBelowStatement
#print axioms AvailableChain.FGSA.Run.WCGProposalPivotStatement
#print axioms AvailableChain.FGSA.Run.WCGProposalAdmissionStatement
#print axioms AvailableChain.FGSA.Run.WCGExactProposalStatement
#print axioms AvailableChain.FGSA.Run.WCGInclusion6Statement
#print axioms AvailableChain.FGSA.Run.WCGRetrospectiveStatement
#print axioms AvailableChain.FGSA.Run.WCGSeededFrameLiveStatement
#print axioms AvailableChain.FGSA.Run.WCGSeededFramePathStatement
#print axioms AvailableChain.FGSA.Run.WCGLowFinalizedStatement
#print axioms AvailableChain.FGSA.Run.wcg_half_of_participation
#print axioms AvailableChain.FGSA.Run.wcg_half_of_joined_participation
#print axioms AvailableChain.FGSA.Run.wcg_faultQ_of_half
#print axioms AvailableChain.FGSA.Run.wcg_suffix_faultQ
#print axioms AvailableChain.FGSA.Run.wcg_tick_retained
#print axioms AvailableChain.FGSA.Run.wcg_filtered_replay
#print axioms AvailableChain.FGSA.Run.wcg_readReplay
#print axioms AvailableChain.FGSA.Run.wcg_afterTicksReplay
#print axioms AvailableChain.FGSA.Run.wcg_init

#print axioms AvailableChain.FGSA.Run.wcg_gate_enabled_of_result
#print axioms AvailableChain.FGSA.Run.wcg_gate_pre_joined

#print axioms AvailableChain.FGSA.Run.wc_seededFrame
#print axioms AvailableChain.FGSA.Run.wc_seededFrameLive
#print axioms AvailableChain.FGSA.Run.wc_seededFramePath
#print axioms AvailableChain.FGSA.Run.wc_gateHeads
#print axioms AvailableChain.FGSA.Run.wc_gateFinalOrigin
#print axioms AvailableChain.FGSA.Run.wcg_seededFrame
#print axioms AvailableChain.FGSA.Run.wcg_seededFrameLive
#print axioms AvailableChain.FGSA.Run.wcg_seededFramePath
#print axioms AvailableChain.FGSA.Run.wcg_eventReplay
#print axioms AvailableChain.FGSA.Run.wcg_beforeReplay
#print axioms AvailableChain.FGSA.Run.wcg_tickEventReplay
#print axioms AvailableChain.FGSA.Run.wcg_tickSourceReplay
#print axioms AvailableChain.FGSA.Run.wcg_confirmedReaderSourceReplay
#print axioms AvailableChain.FGSA.Run.wcg_outputReplay
#print axioms AvailableChain.FGSA.Run.wcg_empty_outputs
#print axioms AvailableChain.FGSA.Run.wcg_gate_path_coverage
#print axioms AvailableChain.FGSA.Run.wcg_transfer_path_coverage
#print axioms AvailableChain.FGSA.Run.wcg_head_handlers
#print axioms AvailableChain.FGSA.Run.wcg_gate_restart_bound
#print axioms AvailableChain.FGSA.Run.wcg_gate_read_epoch
#print axioms AvailableChain.FGSA.Run.wcg_gate_head_receipt
#print axioms AvailableChain.FGSA.Run.wcg_vote_restart_bound
#print axioms AvailableChain.FGSA.Run.wcg_vote_read_epoch
#print axioms AvailableChain.FGSA.Run.wc_gate_path_coverage
#print axioms AvailableChain.FGSA.Run.wc_transfer_path_coverage
#print axioms AvailableChain.FGSA.Run.wc_head_handlers
#print axioms AvailableChain.FGSA.Run.wc_gate_restart_bound
#print axioms AvailableChain.FGSA.Run.wc_gate_read_epoch
#print axioms AvailableChain.FGSA.Run.wc_gate_head_receipt
#print axioms AvailableChain.FGSA.Run.wc_vote_restart_bound
#print axioms AvailableChain.FGSA.Run.wc_vote_read_epoch
#print axioms AvailableChain.FGSA.Run.wcg_finalHistoryAt
#print axioms AvailableChain.FGSA.Run.wcg_outputHistoryAt
#print axioms AvailableChain.FGSA.Run.wcg_result_output_compatible
#print axioms AvailableChain.FGSA.Run.wcg_output_mono_of_inv
#print axioms AvailableChain.FGSA.Run.wcg_seededSafety
#print axioms AvailableChain.FGSA.Run.wcg_gateHeads
#print axioms AvailableChain.FGSA.Run.wcg_gateFinalOrigin
#print axioms AvailableChain.FGSA.Run.wcg_gateBatch
#print axioms AvailableChain.FGSA.Run.wcg_gateResult
#print axioms AvailableChain.FGSA.Run.wcg_gate_result_served
#print axioms AvailableChain.FGSA.Run.wcg_gate_result_outputs
#print axioms AvailableChain.FGSA.Run.wcg_service_result_outputs
#print axioms AvailableChain.FGSA.Run.wcg_service4_prefix
#print axioms AvailableChain.FGSA.Run.wcg_retrospectiveFrame
#print axioms AvailableChain.FGSA.Run.wcg_retrospectivePaths
#print axioms AvailableChain.FGSA.Run.wc_finalHistoryAt
#print axioms AvailableChain.FGSA.Run.wc_outputHistoryAt
#print axioms AvailableChain.FGSA.Run.wc_result_output_compatible
#print axioms AvailableChain.FGSA.Run.wc_output_mono_of_inv
#print axioms AvailableChain.FGSA.Run.wc_seededSafety
#print axioms AvailableChain.FGSA.Run.wc_gate_result_served
#print axioms AvailableChain.FGSA.Run.wc_gate_result_outputs
#print axioms AvailableChain.FGSA.Run.wc_service_result_outputs
#print axioms AvailableChain.FGSA.Run.wc_service4_prefix
#print axioms AvailableChain.FGSA.Run.wc_gateBatch
#print axioms AvailableChain.FGSA.Run.wc_gateResult
#print axioms AvailableChain.FGSA.Run.wc_retrospectiveFrame
#print axioms AvailableChain.FGSA.Run.wc_retrospectivePaths
#print axioms AvailableChain.FGSA.Run.wc_event_before_prefixTime
#print axioms AvailableChain.FGSA.Run.wc_confirmedReader_early_gate
#print axioms AvailableChain.FGSA.Run.wcg_gate_raw_enabled
#print axioms AvailableChain.FGSA.Run.wcg_gate_cut_iff
#print axioms AvailableChain.FGSA.Run.wcg_event_before_prefixTime
#print axioms AvailableChain.FGSA.Run.wcg_confirmedReader_early_gate
#print axioms AvailableChain.FGSA.Run.wcg_result_enabled
#print axioms AvailableChain.FGSA.Run.wcg_enabledGate_of_joinedAt
#print axioms AvailableChain.FGSA.Run.wcg_joined_gate_witness
#print axioms AvailableChain.FGSA.Run.wcg_cut_storeReplay
#print axioms AvailableChain.FGSA.Run.wcg_seed_state
#print axioms AvailableChain.FGSA.Run.wcg_tick_before_cut
#print axioms AvailableChain.FGSA.Run.wcg_time_before_cut
#print axioms AvailableChain.FGSA.Run.wcg_preTickReplay
#print axioms AvailableChain.FGSA.Run.wcg_tickReads
#print axioms AvailableChain.FGSA.Run.wcg_tickPassed
#print axioms AvailableChain.FGSA.Run.wcg_rowSourceReplay
#print axioms AvailableChain.FGSA.Run.wcg_actionReads

#print axioms AvailableChain.FGSA.Run.wc_receiptOrigins

#print axioms AvailableChain.FGSA.Run.wcg_receiptOrigins

#print axioms AvailableChain.FGSA.Run.wc_finiteStep

#print axioms AvailableChain.FGSA.Run.wc_reconcileBound

#print axioms AvailableChain.FGSA.Run.wc_outputStep

#print axioms AvailableChain.FGSA.Run.wc_finalBelow

#print axioms AvailableChain.FGSA.Run.wcg_finiteStep

#print axioms AvailableChain.FGSA.Run.wcg_finiteFacts

#print axioms AvailableChain.FGSA.Run.wc_stepRestart

#print axioms AvailableChain.FGSA.Run.wcg_stepRestart

#print axioms AvailableChain.FGSA.Run.wc_historyMax

#print axioms AvailableChain.FGSA.Run.wc_gateLabel_beforeVote

#print axioms AvailableChain.FGSA.Run.wc_cut_le_laterTick

#print axioms AvailableChain.FGSA.Run.wc_highSource_beforeVote

#print axioms AvailableChain.FGSA.Run.wc_history_previousHeads

#print axioms AvailableChain.FGSA.Run.wcg_outputStep

#print axioms AvailableChain.FGSA.Run.wcg_reconcileBound

#print axioms AvailableChain.FGSA.Run.wcg_finalBelow

#print axioms AvailableChain.FGSA.Run.wc_relay_head_epoch
#print axioms AvailableChain.FGSA.Run.wc_relay_head_history
#print axioms AvailableChain.FGSA.Run.wc_relay_head_handlers
#print axioms AvailableChain.FGSA.Run.wc_relay_gate_restart_bound
#print axioms AvailableChain.FGSA.Run.wc_relay_vote_restart_bound
#print axioms AvailableChain.FGSA.Run.wc_relay_head_receiver_service
#print axioms AvailableChain.FGSA.Run.wc_relay_head_relay_scope
#print axioms AvailableChain.FGSA.Run.wc_relay_headVotes_provenance
#print axioms AvailableChain.FGSA.Run.wc_relay_head_receipt_at_read
#print axioms AvailableChain.FGSA.Run.wc_relay_vote_proposal_tick
#print axioms AvailableChain.FGSA.Run.wc_relay_support_accepted
#print axioms AvailableChain.FGSA.Run.wc_relay_transfer_head_scope
#print axioms AvailableChain.FGSA.Run.wc_relay_gate_read_epoch
#print axioms AvailableChain.FGSA.Run.wc_relay_headVotes_backward
#print axioms AvailableChain.FGSA.Run.wcg_relay_head_epoch
#print axioms AvailableChain.FGSA.Run.wcg_relay_head_history
#print axioms AvailableChain.FGSA.Run.wcg_relay_head_handlers
#print axioms AvailableChain.FGSA.Run.wcg_relay_gate_restart_bound
#print axioms AvailableChain.FGSA.Run.wcg_relay_vote_restart_bound
#print axioms AvailableChain.FGSA.Run.wcg_relay_head_receiver_service
#print axioms AvailableChain.FGSA.Run.wcg_relay_head_relay_scope
#print axioms AvailableChain.FGSA.Run.wcg_relay_headVotes_provenance
#print axioms AvailableChain.FGSA.Run.wcg_relay_head_receipt_at_read
#print axioms AvailableChain.FGSA.Run.wcg_relay_vote_proposal_tick
#print axioms AvailableChain.FGSA.Run.wcg_relay_support_accepted
#print axioms AvailableChain.FGSA.Run.wcg_relay_transfer_head_scope
#print axioms AvailableChain.FGSA.Run.wcg_relay_gate_read_epoch
#print axioms AvailableChain.FGSA.Run.wcg_relay_headVotes_backward
#print axioms AvailableChain.FGSA.Run.wc_stepDelivery
#print axioms AvailableChain.FGSA.Run.wc_stepNoGateTick
#print axioms AvailableChain.FGSA.Run.wc_stepGateTick
#print axioms AvailableChain.FGSA.Run.wc_seededInduction
#print axioms AvailableChain.FGSA.Run.wc_seededSafeFromCut
#print axioms AvailableChain.FGSA.Run.wcg_stepDelivery
#print axioms AvailableChain.FGSA.Run.wcg_stepNoGateTick
#print axioms AvailableChain.FGSA.Run.wcg_stepGateTick
#print axioms AvailableChain.FGSA.Run.wcg_seededInduction

#print axioms AvailableChain.FGSA.Run.wc_tick_joinedAt
#print axioms AvailableChain.FGSA.Run.wc_duty_joinedAt
#print axioms AvailableChain.FGSA.Run.wc_duty_receiver
#print axioms AvailableChain.FGSA.Run.wc_duty_path_coverage
#print axioms AvailableChain.FGSA.Run.wc_duty_head_path
#print axioms AvailableChain.FGSA.Run.wc_joined_rest_bound
#print axioms AvailableChain.FGSA.Run.wc_proposalInput
#print axioms AvailableChain.FGSA.Run.wc_headInput
#print axioms AvailableChain.FGSA.Run.wc_headRead_stamped
#print axioms AvailableChain.FGSA.Run.wc_headRead_laterPath
#print axioms AvailableChain.FGSA.Run.wc_frameMember
#print axioms AvailableChain.FGSA.Run.wc_proposalPath_of_previous
#print axioms AvailableChain.FGSA.Run.wc_headPath_of_previous
#print axioms AvailableChain.FGSA.Run.wc_history_beforeVote
#print axioms AvailableChain.FGSA.Run.wc_clock_offProposalHead
#print axioms AvailableChain.FGSA.Run.wc_comparisonInputs
#print axioms AvailableChain.FGSA.Run.wc_proposer_prior_of_F_prefix
#print axioms AvailableChain.FGSA.Run.wc_reader_scores
#print axioms AvailableChain.FGSA.Run.wc_previousReceipts
#print axioms AvailableChain.FGSA.Run.wc_proposalCounts
#print axioms AvailableChain.FGSA.Run.wc_headCounts
#print axioms AvailableChain.FGSA.Run.wc_treeFrameAncestry
#print axioms AvailableChain.FGSA.Run.wc_proposalPivot
#print axioms AvailableChain.FGSA.Run.wc_head_source_path
#print axioms AvailableChain.FGSA.Run.wc_relay_head_emission_scope

#print axioms AvailableChain.FGSA.Run.wc_local_proposal_service
#print axioms AvailableChain.FGSA.Run.wc_accepted_target_service
#print axioms AvailableChain.FGSA.Run.wc_retained_score_scope
#print axioms AvailableChain.FGSA.Run.wc_emitted_proposal_service
#print axioms AvailableChain.FGSA.Run.wc_retainedReads
#print axioms AvailableChain.FGSA.Run.wc_exactProposal
#print axioms AvailableChain.FGSA.Run.wc_proposalAdmission

#print axioms AvailableChain.FGSA.Run.wc_gate_active_heads

#print axioms AvailableChain.FGSA.Run.wc_exact_gate_raw

#print axioms AvailableChain.FGSA.Run.wc_confirmedReader_public_gate

#print axioms AvailableChain.FGSA.Run.wc_cachedSafety

#print axioms AvailableChain.FGSA.Run.wc_prior_below_proposal

#print axioms AvailableChain.FGSA.Run.wc_proposal_gates

#print axioms AvailableChain.FGSA.Run.wc_suffix_mono

#print axioms AvailableChain.FGSA.Run.wc_inclusion6_result

#print axioms AvailableChain.FGSA.Run.wcg_cachedSafety

#print axioms AvailableChain.FGSA.Run.WCCachedSafety

#print axioms AvailableChain.FGSA.Run.WCInclusion6ResultStatement

#print axioms AvailableChain.FGSA.Run.wc_cut_publicRead

#print axioms AvailableChain.FGSA.Run.wc_growth_of_safety_inclusion

#print axioms AvailableChain.FGSA.Run.wc_checkpoint

#print axioms AvailableChain.FGSA.Run.wc_seededLiveAt

#print axioms AvailableChain.FGSA.Run.wcg_readAt_clamp

#print axioms AvailableChain.FGSA.Run.wcg_empty_outputReplay

#print axioms AvailableChain.FGSA.Run.wcg_cut_read_time

#print axioms AvailableChain.FGSA.Run.wcg_empty_outputDomain

#print axioms AvailableChain.FGSA.Run.wcg_proposalSourceReplay

#print axioms AvailableChain.FGSA.Run.wcg_empty_inclusion

#print axioms AvailableChain.FGSA.Run.wcg_growthOfOutputs

#print axioms AvailableChain.FGSA.Run.wcg_localPrefixReplay

#print axioms AvailableChain.FGSA.Run.wcg_empty_stateMap

#print axioms AvailableChain.FGSA.Run.wcg_empty_stateMap_timed

#print axioms AvailableChain.FGSA.Run.wcg_cut_before_prefix_event

#print axioms AvailableChain.FGSA.Run.wcg_empty_readerReplay

#print axioms AvailableChain.FGSA.Run.wcg_empty_stateSafety

#print axioms AvailableChain.FGSA.Run.wcg_empty_live_of_finalBelow

#print axioms AvailableChain.FGSA.Run.wcg_empty_finalBelow

#print axioms AvailableChain.FGSA.Run.fgsa_target_service_genesis
