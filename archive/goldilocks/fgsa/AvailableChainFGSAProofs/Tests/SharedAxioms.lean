module
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyStore -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyScope -- shake: keep (#print axioms)

public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp -- shake: keep (audit)

public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Channels -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Compose -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Count -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.ExactHead -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Gate -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.GridSchedule -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.HeadAfterSettlement -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.HeadCover -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.HeadGeometry -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Healed -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.HealingFixture -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.HonestQuorum -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.KeepExact -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.OpeningAfterGate -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.OpeningSource -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowth -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.ProposalRead -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Reads -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.ReceiptFacts -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Recurrence -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Relay -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Release -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumers -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersH6S -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersL2 -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersQ -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedPersist -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedReflect -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedScores -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedWalk -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedWalkStore -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Roots -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RowAuth -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.RowReads -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.SameLabel -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.ScoreRun -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.SelfDelivery -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.WindowTerminal -- shake: keep (audit)

public import AvailableChainFGSAProofs.Proofs.Shared.HeadAdmit -- shake: keep (audit)

public section

#print axioms AvailableChain.FGSA.Run.fgsa_trigger_nonneg
#print axioms AvailableChain.FGSA.Run.fgsa_awakeOn_before_tick_noRestart
#print axioms AvailableChain.FGSA.Run.fgsa_joinedNow_noRestart
#print axioms AvailableChain.FGSA.Run.fgsa_gate_saved_guarded
#print axioms AvailableChain.FGSA.Run.fgsa_store_durable
#print axioms AvailableChain.FGSA.Run.fgsa_store_cumulative_on
#print axioms AvailableChain.FGSA.Run.fgsa_catchUp_before_freeze
#print axioms AvailableChain.FGSA.Run.fgsa_gate_joined_of_joinedEnv
#print axioms AvailableChain.FGSA.Run.fgsa_gate_joined_of_enabled
#print axioms AvailableChain.FGSA.Run.fgsa_enabledGate_noRestart
#print axioms AvailableChain.FGSA.Run.fgsa_store_cumulative
#print axioms AvailableChain.FGSA.Run.fgsaSafetyReads
#print axioms AvailableChain.FGSA.Run.fgsaSafetyReads_def
#print axioms AvailableChain.FGSA.Run.fgsaSafetyWireLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyClientLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyUnitLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyStoreLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyOrderLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyScopeLaws
#print axioms AvailableChain.FGSA.Run.fgsa_safetyScopedRoots

#print axioms AvailableChain.FGSA.Run.fgsaSafetyRestartLaws

#print axioms AvailableChain.FGSA.Run.fgsa_restore_finality_fields

#print axioms AvailableChain.FGSA.Run.fgsa_grid_carrier_timeW
#print axioms AvailableChain.FGSA.Run.fgsa_grid_kernel_deadlineW
#print axioms AvailableChain.FGSA.Run.F4_W_implies_FE_W
#print axioms AvailableChain.FGSA.Run.kappaF_ceiling
#print axioms AvailableChain.FGSA.Run.kappaF_ge_two
#print axioms AvailableChain.FGSA.Run.kappaF_eq_two_iff
#print axioms AvailableChain.FGSA.Run.betaF_eq_eight_delta
#print axioms AvailableChain.FGSA.Run.epsF_eq_zero
#print axioms AvailableChain.FGSA.Run.carrierTimeW_eq_carrierTime2
#print axioms AvailableChain.FGSA.Run.kernelDeadlineW_eq_kernelDeadline
#print axioms AvailableChain.FGSA.Run.W_W_eq_W_F
#print axioms AvailableChain.FGSA.Run.betaF_bounds
#print axioms AvailableChain.FGSA.Run.betaF_le_period
#print axioms AvailableChain.FGSA.Run.epsF_nonneg
#print axioms AvailableChain.FGSA.Run.epsF_bounds
#print axioms AvailableChain.FGSA.Run.actionTime_periodW
#print axioms AvailableChain.FGSA.Run.action_delivery_boundsW
#print axioms AvailableChain.FGSA.Run.kernel_before_next_actionW
#print axioms AvailableChain.FGSA.Run.E_gF_eq
#print axioms AvailableChain.FGSA.Run.B_cF_eq
#print axioms AvailableChain.FGSA.Run.E_jF_bounds
#print axioms AvailableChain.FGSA.Run.BF_bounds
#print axioms AvailableChain.FGSA.Run.B_HF_bounds
#print axioms AvailableChain.FGSA.Run.B_HF_eq_B_H
#print axioms AvailableChain.FGSA.Run.B_bestF_le_healing
#print axioms AvailableChain.FGSA.Run.BF_max
#print axioms AvailableChain.FGSA.Run.resetF_healing_eq
#print axioms AvailableChain.FGSA.Run.B_HF_numeric_351
#print axioms AvailableChain.FGSA.Run.B_HF_numeric_295
#print axioms AvailableChain.FGSA.Run.B_HF_numeric_343
#print axioms AvailableChain.FGSA.Run.ancestorClosed_preceq
#print axioms AvailableChain.FGSA.Run.ancestorClosed_compatible
#print axioms AvailableChain.FGSA.Run.srcFrame_genesis_preceq
#print axioms AvailableChain.FGSA.Run.srcFrame_genesis_compatible
#print axioms AvailableChain.FGSA.Run.fgSource_eq_jointSource
#print axioms AvailableChain.FGSA.Run.propose_head
#print axioms AvailableChain.FGSA.Run.frameR_congr_fg
#print axioms AvailableChain.FGSA.Run.domainR_congr_fg
#print axioms AvailableChain.FGSA.Run.fgsa_domainR_eq_filtered
#print axioms AvailableChain.FGSA.Run.fgsa_domainR_eq_storeFrame_of_top_retained
#print axioms AvailableChain.FGSA.Run.eligible_lo_live
#print axioms AvailableChain.FGSA.Run.jointSelections_record_irrel
#print axioms AvailableChain.FGSA.Run.frame_postClock
#print axioms AvailableChain.FGSA.Run.rowSigner_iff_holder
#print axioms AvailableChain.FGSA.Run.honestRow_auth
#print axioms AvailableChain.FGSA.Run.emit_lt_handles
#print axioms AvailableChain.FGSA.Run.fgsa_cpPrefix_of_srcFrame
#print axioms AvailableChain.FGSA.Run.cpPrefix_of_srcFrame
#print axioms AvailableChain.FGSA.Run.fgsa_cpCompat_of_srcFrame
#print axioms AvailableChain.FGSA.Run.cpCompat_of_srcFrame
#print axioms AvailableChain.FGSA.Run.fgsa_cpCompat_of_scopedFrame
#print axioms AvailableChain.FGSA.Run.cpCompat_of_scopedFrame
#print axioms AvailableChain.FGSA.Run.pendingFold_consume_W
#print axioms AvailableChain.FGSA.Run.covered_parent_W
#print axioms AvailableChain.FGSA.Run.finalityBatch_covered_W
#print axioms AvailableChain.FGSA.Run.finalizePending_of_acceptBefore_W
#print axioms AvailableChain.FGSA.Run.muOf_spec
#print axioms AvailableChain.FGSA.Run.H0.time_unique
#print axioms AvailableChain.FGSA.Run.H0.tstar_eq
#print axioms AvailableChain.FGSA.Run.HealAC.tsMono
#print axioms AvailableChain.FGSA.Run.HealAC.tExact
#print axioms AvailableChain.FGSA.Run.fgsa_honest_head_eq_of_stored
#print axioms AvailableChain.FGSA.Run.fgsa_active_support_of_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_active_path_of_coverage
#print axioms AvailableChain.FGSA.Run.fgsa_stored_honest_head_awake
#print axioms AvailableChain.FGSA.Run.fgsa_late_rest_bound
#print axioms AvailableChain.FGSA.Run.fgsa_gate_batch_premises
#print axioms AvailableChain.FGSA.Run.fgsa_gate_zero_of_receipts
#print axioms AvailableChain.FGSA.Run.fgsa_headVote_best_ancestry_of_cover
#print axioms AvailableChain.FGSA.Run.fgsa_headVote_exact_of_covered_parent
#print axioms AvailableChain.FGSA.Run.exactHead_of_proposal_on_run
#print axioms AvailableChain.FGSA.Run.exactService_head_of_proposal
#print axioms AvailableChain.FGSA.Run.exactService_emitted_head
#print axioms AvailableChain.FGSA.Run.exactService_gate_receipts_of_head
#print axioms AvailableChain.FGSA.Run.exactService_gate_raw_of_head
#print axioms AvailableChain.FGSA.Run.exactService_fastWrite_of_gateService
#print axioms AvailableChain.FGSA.Run.exactService_opening_of_gateService
#print axioms AvailableChain.FGSA.Run.exactService_gate_at_of_head
#print axioms AvailableChain.FGSA.Run.exactService_gate_of_head
#print axioms AvailableChain.FGSA.Run.exactService_of_head_and_gate
#print axioms AvailableChain.FGSA.Run.exactService_participation_of_card
#print axioms AvailableChain.FGSA.Run.fgsa_gate_of_coveringBatch
#print axioms AvailableChain.FGSA.Run.fgsa_S_eq_of_exact
#print axioms AvailableChain.FGSA.Run.openingSource_extends_served
#print axioms AvailableChain.FGSA.Run.openingSource_eq_of_no_strict_extension
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_stamps
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_block_stamp_lt
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_block_to_tick
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt
#print axioms AvailableChain.FGSA.Run.fgsa_grid_sa_proposalTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_engine_proposalTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gridco_proposalTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_sa_voteTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_engine_voteTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gridco_voteTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_sa_releaseTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_engine_releaseTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gridco_releaseTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_sa_earlyTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_engine_earlyTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gridco_earlyTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_sa_freezeTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_engine_freezeTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gridco_freezeTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_sa_gateTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_engine_gateTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gridco_gateTime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_sa_lifetime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_engine_lifetime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gridco_lifetime
#print axioms AvailableChain.FGSA.Run.fgsa_grid_period
#print axioms AvailableChain.FGSA.Run.fgsa_grid_lease
#print axioms AvailableChain.FGSA.Run.fgsa_grid_opening
#print axioms AvailableChain.FGSA.Run.fgsa_grid_action_time
#print axioms AvailableChain.FGSA.Run.fgsa_grid_action_gate
#print axioms AvailableChain.FGSA.Run.fgsa_grid_proposal_duty
#print axioms AvailableChain.FGSA.Run.fgsa_grid_head_duty
#print axioms AvailableChain.FGSA.Run.fgsa_grid_action_duty
#print axioms AvailableChain.FGSA.Run.fgsa_grid_run_head_duty
#print axioms AvailableChain.FGSA.Run.fgsa_grid_run_action_duty
#print axioms AvailableChain.FGSA.Run.fgsa_grid_round_period
#print axioms AvailableChain.FGSA.Run.fgsa_grid_carrier_time2
#print axioms AvailableChain.FGSA.Run.fgsa_grid_kernel_deadline
#print axioms AvailableChain.FGSA.Run.fgsa_grid_kernel_before_next_action
#print axioms AvailableChain.FGSA.Run.fgsa_grid_vote_before_action
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gate_after_carrier2
#print axioms AvailableChain.FGSA.Run.fgsa_grid_action_delivery_bounds
#print axioms AvailableChain.FGSA.Run.fgsa_grid_gate_action_order
#print axioms AvailableChain.FGSA.Run.fgsa_firstHead_after
#print axioms AvailableChain.FGSA.Run.fgsa_firstHead_after_bound
#print axioms AvailableChain.FGSA.Run.batch_head_covers
#print axioms AvailableChain.FGSA.Run.fgsa_headReachesLo
#print axioms AvailableChain.FGSA.Run.healed_same_time
#print axioms AvailableChain.FGSA.Run.healed_mono_start
#print axioms AvailableChain.FGSA.Run.healing_held_block_receipt
#print axioms AvailableChain.FGSA.Run.kmid_honestSeats_mem
#print axioms AvailableChain.FGSA.Run.kmid_honest_quorum
#print axioms AvailableChain.FGSA.Run.kept_or_conflict
#print axioms AvailableChain.FGSA.Run.kept_or_cause
#print axioms AvailableChain.FGSA.Run.fgsa_domain_anchorClosed_mono
#print axioms AvailableChain.FGSA.Run.exactHead_of_pivot_ancestry
#print axioms AvailableChain.FGSA.Run.exactHead_of_pivot
#print axioms AvailableChain.FGSA.Run.fgsa_firstOpening_after_gate
#print axioms AvailableChain.FGSA.Run.openingSource_candidate_of_gateService
#print axioms AvailableChain.FGSA.Run.openingSource_domain_of_kept_or_cause
#print axioms AvailableChain.FGSA.Run.openingSource_firstOpening
#print axioms AvailableChain.FGSA.Run.openingSource_exact_of_gateService
#print axioms AvailableChain.FGSA.Run.openingSource_firstOpening_exact
#print axioms AvailableChain.FGSA.Run.jointGrowthAt_of_inclusion
#print axioms AvailableChain.FGSA.Run.fgsa_timeIdx_now_le
#print axioms AvailableChain.FGSA.Run.fgsa_output_noFuture_of_slot
#print axioms AvailableChain.FGSA.Run.fgsa_proposal_emission_exists_of_awake_slot
#print axioms AvailableChain.FGSA.Run.fgsa_honestProposal_exists_of_awake_slot
#print axioms AvailableChain.FGSA.Run.fgsa_outputAt_eq_S_at
#print axioms AvailableChain.FGSA.Run.fgsa_healSuffix_timeIdx
#print axioms AvailableChain.FGSA.Run.fgsa_healed_output_mono
#print axioms AvailableChain.FGSA.Run.proposal_read_named
#print axioms AvailableChain.FGSA.Run.afterTicks_eq_stateBefore
#print axioms AvailableChain.FGSA.Run.afterTicks_node
#print axioms AvailableChain.FGSA.Run.afterTicks_eq_tick_preTick
#print axioms AvailableChain.FGSA.Run.preIdx_le_afterTicksIdx
#print axioms AvailableChain.FGSA.Run.afterTicksIdx_mono
#print axioms AvailableChain.FGSA.Run.fgsa_tickIdx_of_event
#print axioms AvailableChain.FGSA.Run.gateResult_eq_saved
#print axioms AvailableChain.FGSA.Run.fgsa_gate_raw_of_nonempty
#print axioms AvailableChain.FGSA.Run.isGateTime_iff
#print axioms AvailableChain.FGSA.Run.gateResultAt_eq_gateResult
#print axioms AvailableChain.FGSA.Run.vHead_eq_headAtIdx
#print axioms AvailableChain.FGSA.Run.actionSourceFG_eq_round
#print axioms AvailableChain.FGSA.Run.acceptsFinalBefore_of_idx
#print axioms AvailableChain.FGSA.Run.acceptsFinalBefore_mono_deadline
#print axioms AvailableChain.FGSA.Run.acceptsFinalBefore_mono_ancestor
#print axioms AvailableChain.FGSA.Run.stable_afterTicks
#print axioms AvailableChain.FGSA.Run.receipt_finality
#print axioms AvailableChain.FGSA.Run.receipt_parent_path
#print axioms AvailableChain.FGSA.Run.receipt_height_hj
#print axioms AvailableChain.FGSA.Run.receipt_height_genesis
#print axioms AvailableChain.FGSA.Run.receipt_actionTime_strictMono
#print axioms AvailableChain.FGSA.Run.fgsa_gamma_bounds
#print axioms AvailableChain.FGSA.Run.fgsa_gamma_aligned
#print axioms AvailableChain.FGSA.Run.fgsa_gamma_eq_of_dvd
#print axioms AvailableChain.FGSA.Run.fgsa_gamma_idem
#print axioms AvailableChain.FGSA.Run.fgsa_strongW_recF
#print axioms AvailableChain.FGSA.Run.fgsa_lit_recF
#print axioms AvailableChain.FGSA.Run.fgsa_recPat_restricted
#print axioms AvailableChain.FGSA.Run.fgsa_recPatAt_restricted
#print axioms AvailableChain.FGSA.Run.fgsa_restricted_of_unrestricted
#print axioms AvailableChain.FGSA.Run.fgsa_horizon_mono
#print axioms AvailableChain.FGSA.Run.fgsa_B_max
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_seat_clean_late
#print axioms AvailableChain.FGSA.Run.fgsa_headSupport_subset_headVotes
#print axioms AvailableChain.FGSA.Run.fgsa_headVotes_provenance
#print axioms AvailableChain.FGSA.Run.fgsa_vote_accepted_before_head_read
#print axioms AvailableChain.FGSA.Run.fgsa_headVotes_backward_relay
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_vote_forward
#print axioms AvailableChain.FGSA.Run.fgsa_voteSupports_of_path
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_forward_relay
#print axioms AvailableChain.FGSA.Run.fgsa_releaseCount_antitone
#print axioms AvailableChain.FGSA.Run.fgsa_release_store
#print axioms AvailableChain.FGSA.Run.fgsa_release_bound
#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H6
#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H17
#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H6S
#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_L2
#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_L4R
#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_HG1
#print axioms AvailableChain.FGSA.Run.fgsa_headRead_block_slots
#print axioms AvailableChain.FGSA.Run.fgsa_headRead_child_slot
#print axioms AvailableChain.FGSA.Run.fgsa_exactHeadGeometry_of_retained_endpoint
#print axioms AvailableChain.FGSA.Run.fgsa_headVote_covers_parent_of_retained_geometry
#print axioms AvailableChain.FGSA.Run.fgsa_retainedEndpoint_geometry_on_run
#print axioms AvailableChain.FGSA.Run.fgsa_retainedExactHead_geometry_on_run
#print axioms AvailableChain.FGSA.Run.fgsa_retained_source_stop
#print axioms AvailableChain.FGSA.Run.exactService_head_of_retained_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_domainR_eq_treeStoreFrameView
#print axioms AvailableChain.FGSA.Run.fgsa_domainR_eq_storeFrameView_of_top_retained
#print axioms AvailableChain.FGSA.Run.fgsa_walk_domain_of_witness_tree_view
#print axioms AvailableChain.FGSA.Run.fgsa_walk_domain_of_witness_view_of_top_retained
#print axioms AvailableChain.FGSA.Run.fgsa_score_geometry_of_retained_cuts
#print axioms AvailableChain.FGSA.Run.fgsa_retained_path_mem
#print axioms AvailableChain.FGSA.Run.fgsa_retained_proposal_mem
#print axioms AvailableChain.FGSA.Run.fgsa_retained_persists_of_path
#print axioms AvailableChain.FGSA.Run.fgsa_retained_proposal_mem_on_run
#print axioms AvailableChain.FGSA.Run.fgsa_retained_path_persists_on_run
#print axioms AvailableChain.FGSA.Run.fgsa_retainedWalk_geometry_on_run
#print axioms AvailableChain.FGSA.Run.retainedBand_def
#print axioms AvailableChain.FGSA.Run.ReflectedDomainWitness_def
#print axioms AvailableChain.FGSA.Run.fgsa_tree_domain_witness_of_mem
#print axioms AvailableChain.FGSA.Run.fgsa_domain_witness_of_mem_of_top_retained
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_full_domain_view
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_path_domain_view
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_eligible_iff_view
#print axioms AvailableChain.FGSA.Run.fgsa_eligible_eq_of_retainedBand_score
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_reflected_old_child
#print axioms AvailableChain.FGSA.Run.fgsa_retained_old_child_reflects_on_run
#print axioms AvailableChain.FGSA.Run.fgsa_eligible_eq_of_same_floor
#print axioms AvailableChain.FGSA.Run.fgsa_eligible_eq_of_parent_height
#print axioms AvailableChain.FGSA.Run.fgsa_score_geometry_of_domains
#print axioms AvailableChain.FGSA.Run.fgsa_score_geometry_of_tree_domains
#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_candidates_on_run
#print axioms AvailableChain.FGSA.Run.fgsa_retained_scores_of_candidates
#print axioms AvailableChain.FGSA.Run.fgsa_retained_prefix_of_trunk_or_support
#print axioms AvailableChain.FGSA.Run.fgsa_walk_domain_of_witness
#print axioms AvailableChain.FGSA.fgsa_ordinary_parent_of_live_prefix_of_top_retained
#print axioms AvailableChain.FGSA.fgsa_ordinary_parent_of_live_cover_of_top_retained
#print axioms AvailableChain.FGSA.fgsa_ordinary_parent_of_live_prefix_filtered
#print axioms AvailableChain.FGSA.fgsa_ordinary_parent_of_live_cover_filtered
#print axioms AvailableChain.FGSA.fgsa_band_eq_of_same_floor
#print axioms AvailableChain.FGSA.fgsa_eligible_eq_of_band_score
#print axioms AvailableChain.FGSA.fgsa_eligible_eq_of_no_band_score
#print axioms AvailableChain.FGSA.Run.rootScope_store
#print axioms AvailableChain.FGSA.Run.rootScope_ancestor
#print axioms AvailableChain.FGSA.Run.rootScope_eq
#print axioms AvailableChain.FGSA.Run.rootScope_source
#print axioms AvailableChain.FGSA.Run.certified_preceq
#print axioms AvailableChain.FGSA.Run.rootScope_entry
#print axioms AvailableChain.FGSA.Run.rootScope_justified
#print axioms AvailableChain.FGSA.Run.rootScope_finalized
#print axioms AvailableChain.FGSA.Run.srcFrameAbove_scoped
#print axioms AvailableChain.FGSA.Run.rootScope_result
#print axioms AvailableChain.FGSA.Run.rootScope_belowLabel
#print axioms AvailableChain.FGSA.Run.row_auth_of_toRow
#print axioms AvailableChain.FGSA.Run.rowService_carrier_read
#print axioms AvailableChain.FGSA.Run.rowService_chain_occurrence
#print axioms AvailableChain.FGSA.Run.batch_proposal_read
#print axioms AvailableChain.FGSA.Run.heldBefore_at_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_sameLabel
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_proposal_pools
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_stored_proposal_eq
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_metadata_retained
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_carried_raw_subset
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_raw_subset
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_proposalsAt_eq
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_frozen_vote_relay
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_raw_extra
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_block_forward
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_block_backward
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_support_forward
#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_support_backward
#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_run
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_frozen_block
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_full_domain
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_path_domain_filtered
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_path_domain_of_top_retained
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_eligible_iff
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_proposal_parent
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_current_block_eq
#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_reflected_block
#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_run
#print axioms AvailableChain.FGSA.Run.Base₂.snoc_ownRow
#print axioms AvailableChain.FGSA.Run.Base₂.cutAt
#print axioms AvailableChain.FGSA.Run.Base₂.ownRow_run
#print axioms AvailableChain.FGSA.Run.Base₂.ownRow_run_exists
#print axioms AvailableChain.FGSA.Run.Base₂.snoc_ownRow_other
#print axioms AvailableChain.FGSA.Run.fgsa_terminalRetentionW

end

#print axioms AvailableChain.FGSA.Run.fgsa_historySafeAt_of_emitted_head
#print axioms AvailableChain.FGSA.Run.fgsa_head_receipt_on
#print axioms AvailableChain.FGSA.Run.fgsa_release_bound_restart

#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_stamps_on

#print axioms AvailableChain.FGSA.Run.fgsa_head_stamp_before_read

#print axioms AvailableChain.FGSA.Run.fgsa_proposal_receipt_on

#print axioms AvailableChain.FGSA.Run.ReceiverService.processed

#print axioms AvailableChain.FGSA.Run.ReceiverService.proposal

#print axioms AvailableChain.FGSA.Run.FreshHeadService.receipt

#print axioms AvailableChain.FGSA.Run.fgsa_head_joined_of_joinedAt

#print axioms AvailableChain.FGSA.Run.fgsa_target_receipt_on

#print axioms AvailableChain.FGSA.Run.fgsa_block_stamp_before_read

#print axioms AvailableChain.FGSA.Run.fgsa_awake_of_joinedAt

#print axioms AvailableChain.FGSA.Run.fgsa_restartTime_ge

#print axioms AvailableChain.FGSA.Run.fgsa_joinedAt_of_emitted_head

#print axioms AvailableChain.FGSA.Run.fgsa_receiptCoverage_on

#print axioms AvailableChain.FGSA.Run.fgsa_active_path_of_coverage_on

#print axioms AvailableChain.FGSA.Run.fgsa_stored_honest_head_joined

#print axioms AvailableChain.FGSA.Run.fgsa_late_rest_bound_joined

#print axioms AvailableChain.FGSA.Run.fgsa_gate_batch_premises_joined

#print axioms AvailableChain.FGSA.Run.exactService_emitted_head_joined

#print axioms AvailableChain.FGSA.Run.exactService_gate_receipts_of_head_on

#print axioms AvailableChain.FGSA.Run.exactService_gate_raw_of_head_on

#print axioms AvailableChain.FGSA.Run.exactService_gate_at_of_head_on

#print axioms AvailableChain.FGSA.Run.exactService_gate_of_head_on

#print axioms AvailableChain.FGSA.Run.exactService_of_head_and_gate_on

#print axioms AvailableChain.FGSA.Run.exactService_participation_of_card_joined

#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_block_stamp_lt_on

#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_on

#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_block_to_tick_on

#print axioms AvailableChain.FGSA.Run.inclusion_stampVote_of_prefix

#print axioms AvailableChain.FGSA.Run.inclusion_stampBlock_of_prefix

#print axioms AvailableChain.FGSA.Run.inclusion_stamps_kept

#print axioms AvailableChain.FGSA.Run.inclusion_stamps_kept_on

#print axioms AvailableChain.FGSA.Run.inclusion_head_receipt_early_on

#print axioms AvailableChain.FGSA.Run.inclusion_head_receipt_early

#print axioms AvailableChain.FGSA.Run.inclusion_no_equivocation

#print axioms AvailableChain.FGSA.Run.inclusion_joined_head_seats

#print axioms AvailableChain.FGSA.Run.inclusion_head_seats

#print axioms AvailableChain.FGSA.Run.inclusion_rest_bound

#print axioms AvailableChain.FGSA.Run.fgsa_action_walk_batch

#print axioms AvailableChain.FGSA.Run.fgsa_action_walk_batch_legacy

#print axioms AvailableChain.FGSA.Run.fgsa_retained_proposal_mem_on_run_epoch

#print axioms AvailableChain.FGSA.Run.fgsa_sameLabel_on

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_metadata_retained_restart

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_raw_subset_restart

#print axioms AvailableChain.FGSA.Run.fgsa_votes_cumulative_on

#print axioms AvailableChain.FGSA.Run.exactService_of_head_clean_on
#print axioms AvailableChain.FGSA.Run.exactService_of_head_recovery_on

#print axioms AvailableChain.FGSA.Run.fgsa_target_service_genesis
#print axioms AvailableChain.FGSA.Run.fgsa_target_service_of_proposal

#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_run_on

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_block_backward_on

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_block_forward_on

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_frozen_vote_relay_on

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_raw_extra_on

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_support_backward_on

#print axioms AvailableChain.FGSA.Run.fgsa_scoreRun_support_forward_on

#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_run_on

#print axioms AvailableChain.FGSA.Run.fgsa_target_receipt_at_tick_on

#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_reflected_block_on

#print axioms AvailableChain.FGSA.Run.exactHead_of_proposal_on_run_on

#print axioms AvailableChain.FGSA.Run.exactService_head_of_proposal_on

#print axioms AvailableChain.FGSA.Run.exactService_head_of_proposal_clean_on

#print axioms AvailableChain.FGSA.Run.exactService_head_of_proposal_recovery_on

#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_clean_on

#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_recovery_on

#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_clean_of_retained_proposal_on

#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_recovery_of_retained_proposal_on

#print axioms AvailableChain.FGSA.Run.fgsa_sameLabel_serviceScope

#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_candidates_on_run_on

#print axioms AvailableChain.FGSA.Run.fgsa_retained_old_child_reflects_on_run_on

#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_reflected_old_child_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedWalk_geometry_on_run_on

#print axioms AvailableChain.FGSA.Run.fgsa_retained_path_persists_on_run_on

#print axioms AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedExactHead_geometry_on_run_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H17_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H6_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H6S_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_HG1_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_L4R_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_L2_on

#print axioms AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_clean_on

#print axioms AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_recovery_on

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H17_joined

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H6_joined

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_H6S_joined

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_HG1_joined

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_L4R_joined

#print axioms AvailableChain.FGSA.Run.fgsa_retainedReads_L2_joined

#print axioms AvailableChain.FGSA.Run.fgsa_vote_accepted_before_local

#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_forward_relay_on

#print axioms AvailableChain.FGSA.Run.fgsa_cleanSupport_vote_forward_on

#print axioms AvailableChain.FGSA.Run.fgsa_headVotes_backward_relay_on

#print axioms AvailableChain.FGSA.Run.fgsa_headVotes_provenance_on

#print axioms AvailableChain.FGSA.Run.fgsa_vote_accepted_before_head_read_on

#print axioms AvailableChain.FGSA.Run.fgsa_walkRun_frozen_block_on

#print axioms AvailableChain.FGSA.Run.healing_held_block_receipt_on

#print axioms AvailableChain.FGSA.Run.fgsa_receiptCoverage_anchor_on
#print axioms AvailableChain.FGSA.Run.fgsa_active_path_of_coverage_anchor_on

#print axioms AvailableChain.FGSA.Run.Recovery₂.joinedAt_of_slotStart_le
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.of_legacy
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.legacy_delivery
#print axioms AvailableChain.FGSA.Run.Recovery₂.of_legacy
#print axioms AvailableChain.FGSA.Run.Recovery₂Aligned.gamma_eq
#print axioms AvailableChain.FGSA.Run.recovery₂_roundUp
#print axioms AvailableChain.FGSA.Run.Recovery₂.toRecoveryCore
#print axioms AvailableChain.FGSA.Run.card_eq_n_of_linked
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.toCleanCut
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.faultQ_of_pos
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.faultQ
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.batch
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.batchAt
#print axioms AvailableChain.FGSA.Run.Recovery₂.faultX_count_rec
#print axioms AvailableChain.FGSA.Run.Recovery₂.faultQ
#print axioms AvailableChain.FGSA.Run.Recovery₂.batch
#print axioms AvailableChain.FGSA.Run.fgsa_clean_delivery_iff
#print axioms AvailableChain.FGSA.Run.fgsa_seed_reachable
#print axioms AvailableChain.FGSA.Run.fgsa_seed_accepted
#print axioms AvailableChain.FGSA.Run.Outage₂.pos
#print axioms AvailableChain.FGSA.Run.Outage₂.toCleanCut
#print axioms AvailableChain.FGSA.Run.Outage₂.faultQ
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_clean
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_recovery
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_clean_legacy
#print axioms AvailableChain.FGSA.Run.fgsa_gateReceipt_recovery_legacy
#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_clean_of_retained_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_score_eq_on_recovery_of_retained_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_clean
#print axioms AvailableChain.FGSA.Run.fgsa_ghost_transfer_sfx_on_recovery
#print axioms AvailableChain.FGSA.Run.exactService_head_of_proposal_clean
#print axioms AvailableChain.FGSA.Run.exactService_head_of_proposal_recovery
#print axioms AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_clean
#print axioms AvailableChain.FGSA.Run.exactService_head_of_retained_proposal_recovery
#print axioms AvailableChain.FGSA.Run.exactService_of_head_clean
#print axioms AvailableChain.FGSA.Run.exactService_of_head_recovery
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.snoc_ownRow
#print axioms AvailableChain.FGSA.Run.Recovery₂.snoc_ownRow
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.cutAt
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.ownRow_run
#print axioms AvailableChain.FGSA.Run.Recovery₂.cutAt
#print axioms AvailableChain.FGSA.Run.Recovery₂.ownRow_run
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.cutAt_le
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂.ownRow_run_le
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.ownRow_run
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂.ownRow_run_le
#print axioms AvailableChain.FGSA.Run.Clean₂.ownRow_run
#print axioms AvailableChain.FGSA.Run.Outage₂.ownRow_run
#print axioms AvailableChain.FGSA.Run.Outage₂.ownRow_run_mid

#print axioms AvailableChain.FGSA.Run.fgsa_historySafeAt_of_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_proposal_handlers_at_anchor
#print axioms AvailableChain.FGSA.Run.fgsa_enabledGate_awakeClosed
#print axioms AvailableChain.FGSA.Run.fgsa_enabledGate_anchor_epoch
#print axioms AvailableChain.FGSA.Run.fgsa_gate_path_anchor_service
#print axioms AvailableChain.FGSA.Run.fgsa_transfer_path_anchor_service
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorStatement
#print axioms AvailableChain.FGSA.Run.fgsa_receiptCoverage_anchor
#print axioms AvailableChain.FGSA.Run.fgsa_active_path_of_coverage_anchor
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.within
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.service
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.slotWindow
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.handlers
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.compat
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.deadline
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.pathCoverage
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageAnchorPremises.proposalPaths

#print axioms AvailableChain.FGSA.Run.fgsa_proposal_acceptance_facts
