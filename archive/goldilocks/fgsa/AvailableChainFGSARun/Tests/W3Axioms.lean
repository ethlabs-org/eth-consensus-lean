module
public import AvailableChainFGSARun.Proofs.SelfDelivery -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.HeadHistory -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.ProposalHistory -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.ReadyAcceptance -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.NamedDelivery -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.NamedHistory -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.AC -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.Join -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.RowHistory -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.AncestorDeadlines -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.Spec.Simulation -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.EmissionWellFormed -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.ClientTrace -- shake: keep (#print axioms)

public import AvailableChainFGSARun.Proofs.ReceiptCoverageReady -- shake: keep (#print axioms)

public section

#print axioms AvailableChain.FGSA.Run.fgsa_fgAction_unjoined_source_none
#print axioms AvailableChain.FGSA.Run.fgsa_clock_restartTime
#print axioms AvailableChain.FGSA.Run.fgsa_process_restartTime
#print axioms AvailableChain.FGSA.Run.fgsa_restartTime_bound
#print axioms AvailableChain.FGSA.Run.fgsa_joinedNow_of_joinedEnv
#print axioms AvailableChain.FGSA.Run.fgsa_joinedNow_of_caughtUp
#print axioms AvailableChain.FGSA.Run.fgsa_joinedNow_of_awakeClosed
#print axioms AvailableChain.FGSA.Run.rowPool_provenance
#print axioms AvailableChain.FGSA.Run.fgsa_emitted_row_no_prior_processed
#print axioms AvailableChain.FGSA.ancestorDeadlines_acRestart
#print axioms AvailableChain.FGSA.ancestorDeadlines_gateStep
#print axioms AvailableChain.FGSA.Run.ancestorDeadlines_restore
#print axioms AvailableChain.FGSA.Run.ownRecord_fold_run
#print axioms AvailableChain.FGSA.Run.fgsa_emits_head
#print axioms AvailableChain.FGSA.Run.fgsa_emits_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_emitOnceUnder
#print axioms AvailableChain.FGSA.Run.decode_honest
#print axioms AvailableChain.FGSA.Run.fgsa_emissionRowsValid
#print axioms AvailableChain.FGSA.Run.honest_emit_wellFormed
#print axioms AvailableChain.FGSA.Run.fgsa_tick_rows_of_seats
#print axioms AvailableChain.FGSA.Run.fgsaHooks
#print axioms AvailableChain.FGSA.Spec.spec_restart_durable_retained
#print axioms AvailableChain.FGSA.Spec.spec_restart_clock_retained
#print axioms AvailableChain.FGSA.Spec.spec_prune_restart_mem
#print axioms AvailableChain.FGSA.Spec.spec_prune_schedule
#print axioms AvailableChain.FGSA.Spec.spec_prune_sleep
#print axioms AvailableChain.FGSA.Spec.spec_prune_execution_valid
#print axioms AvailableChain.FGSA.Spec.spec_revised_target_execution
#print axioms AvailableChain.FGSA.Spec.spec_restart_retained_block_trace
#print axioms AvailableChain.FGSA.Spec.spec_restart_execution_valid

#print axioms AvailableChain.FGSA.Run.fgsa_clockPre_gateView
#print axioms AvailableChain.FGSA.Run.fgsaAC_gate_write
#print axioms AvailableChain.FGSA.Run.fgsaAC_output_step
#print axioms AvailableChain.FGSA.Run.fgsaAC_laws
#print axioms AvailableChain.FGSA.Run.fgsaAC_slot_gate_reads

#print axioms AvailableChain.FGSA.Run.fgsaTimelyClock_clock
#print axioms AvailableChain.FGSA.Run.fgsa_awake_before_noRestart
#print axioms AvailableChain.FGSA.Run.fgsa_historySafeAt_noRestart
#print axioms AvailableChain.FGSA.Run.fgsa_processed_by_deadline_ready
#print axioms AvailableChain.FGSA.Run.fgsa_accepted_by_deadline_of_parentStored
#print axioms AvailableChain.FGSA.Run.fgsa_replay_vote_stamp_time
#print axioms AvailableChain.FGSA.Run.fgsa_vote_stamp_source_or_restart
#print axioms AvailableChain.FGSA.Run.fgsa_block_stamp_source_or_restart
#print axioms AvailableChain.FGSA.Run.fgsa_block_accepted_origin
#print axioms AvailableChain.FGSA.Run.fgsa_vote_stamp_source
#print axioms AvailableChain.FGSA.Run.fgsa_block_stamp_source
#print axioms AvailableChain.FGSA.Run.fgsa_replayed_head_delivery_origin
#print axioms AvailableChain.FGSA.Run.fgsa_emitted_head_no_prior_processed
#print axioms AvailableChain.FGSA.Run.fgsa_emitted_proposal_no_prior_processed
#print axioms AvailableChain.FGSA.Run.proposal_trigger_in_scope
#print axioms AvailableChain.FGSA.Run.proposal_trigger_in_root_scope
#print axioms AvailableChain.FGSA.Run.namedScope_stored_proposal
#print axioms AvailableChain.FGSA.Run.stored_named_body_delivery
#print axioms AvailableChain.FGSA.Run.stored_named_body_ancestor
#print axioms AvailableChain.FGSA.Run.namedProposalInRun_genesis_or_delivered
#print axioms AvailableChain.FGSA.Run.namedProposalInRun_origin
#print axioms AvailableChain.FGSA.Run.namedStored_eq
#print axioms AvailableChain.FGSA.Run.fgsa_clockOf_nonneg
#print axioms AvailableChain.FGSA.Run.fgsa_vote_accepted_before
#print axioms AvailableChain.FGSA.Run.fgsa_block_accepted_before
#print axioms AvailableChain.FGSA.Run.fgsa_head_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_proposal_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_honest_head_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_head_cap_sources
#print axioms AvailableChain.FGSA.Run.executionValid_cut
#print axioms AvailableChain.FGSA.Run.healthyPrefixDeliveryBy_of_le
#print axioms AvailableChain.FGSA.Run.partialSynchronyBy_snoc_selfDelivery
#print axioms AvailableChain.FGSA.Run.healthyPrefixDeliveryBy_snoc_selfDelivery
#print axioms AvailableChain.FGSA.Run.partialSynchronyBy_cut
#print axioms AvailableChain.FGSA.Run.healthyPrefixDeliveryBy_cut

end

#print axioms AvailableChain.FGSA.Run.NamedProposalReceiptScope
#print axioms AvailableChain.FGSA.Run.NamedReceiptRootCollisionFree
#print axioms AvailableChain.FGSA.Run.namedReceiptScope_of_namedScope
#print axioms AvailableChain.FGSA.Run.namedReceiptScope_emitted
#print axioms AvailableChain.FGSA.Run.namedReceiptScope_ancestor
#print axioms AvailableChain.FGSA.Run.NamedReceiptRootCollisionFree.toNamedRootCollisionFree
#print axioms AvailableChain.FGSA.Run.proposal_trigger_in_receipt_scope
#print axioms AvailableChain.FGSA.Run.proposal_processed_in_scope
#print axioms AvailableChain.FGSA.Run.emitted_proposal_history_in_scope
#print axioms AvailableChain.FGSA.Run.proposal_trigger_service_in_scope
#print axioms AvailableChain.FGSA.Run.fgsa_receiptCoverage_ready
