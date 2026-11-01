module
public import AvailableChainFGSAProofs.Proofs.Healing.Attempt -- shake: keep (#print axioms targets)


-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.HealingInputExport -- shake: keep

public section

/-! Strict audit of the selected recovery services and bounded consumers. -/

#print axioms AvailableChain.FGSA.Run.healing_selected_carriers_recovery
#print axioms AvailableChain.FGSA.Run.healing_head_witness_receipts_recovery
#print axioms AvailableChain.FGSA.Run.healing_self_proposal_service
#print axioms AvailableChain.FGSA.Run.repair_lease_cover_two_at
#print axioms AvailableChain.FGSA.Run.repair_lease_cover_one_at
#print axioms AvailableChain.FGSA.Run.frontier_gate_scope_of_cover
#print axioms AvailableChain.FGSA.Run.frontier_gate_fast_count
#print axioms AvailableChain.FGSA.Run.frontier_retained_reader_floor
#print axioms AvailableChain.FGSA.Run.frontier_service
#print axioms AvailableChain.FGSA.Run.healing_retained_cone_reader_floor
#print axioms AvailableChain.FGSA.Run.healing_frontierSearch_recovery
#print axioms AvailableChain.FGSA.Run.healing_resetTransferCore_recovery
#print axioms AvailableChain.FGSA.Run.healing_postReset_coneStep
#print axioms AvailableChain.FGSA.Run.healing_postReset_openingDomainStep₂
#print axioms AvailableChain.FGSA.Run.healing_postReset_serviceStep₂
#print axioms AvailableChain.FGSA.Run.healing_frontier_service_scopes_recovery
#print axioms AvailableChain.FGSA.Run.healing_repair_service_scopes_recovery
#print axioms AvailableChain.FGSA.Run.healing_opening_service_scopes_recovery
#print axioms AvailableChain.FGSA.Run.healing_proposal_service_at_recovery_anchor
#print axioms AvailableChain.FGSA.Run.healing_target_receipt_at_event
#print axioms AvailableChain.FGSA.Run.healing_witness_receipt_at_event
#print axioms AvailableChain.FGSA.Run.healing_phase_witness_receipts_recovery
#print axioms AvailableChain.FGSA.Run.healing_phase_block_receipt_recovery
#print axioms AvailableChain.FGSA.Run.healing_evidence_spread_recovery
#print axioms AvailableChain.FGSA.Run.healing_rPhase_recovery

#print axioms AvailableChain.FGSA.Run.healing_progressAttempt
#print axioms AvailableChain.FGSA.Run.healing_frontierSearch

#print axioms AvailableChain.FGSA.Run.healing_healTContract_reset
#print axioms AvailableChain.FGSA.Run.healing_healRContract_reset
#print axioms AvailableChain.FGSA.Run.healing_postReset_h6GateService
#print axioms AvailableChain.FGSA.Run.postReset_h2Prime_reset
#print axioms AvailableChain.FGSA.Run.postReset_tHigh_reset

end

-- Round 9: bounded lease/raw successors and the returned input producers.
#print axioms AvailableChain.FGSA.Run.healing_source_before_receipt_at_recovery
#print axioms AvailableChain.FGSA.Run.postReset_moving_head_cut
#print axioms AvailableChain.FGSA.Run.postReset_moving_domain
#print axioms AvailableChain.FGSA.Run.postReset_written_ready
#print axioms AvailableChain.FGSA.Run.postReset_written_sync
#print axioms AvailableChain.FGSA.Run.postReset_written_window
#print axioms AvailableChain.FGSA.Run.healing_first_transfer_written
#print axioms AvailableChain.FGSA.Run.postReset_written_source_compatible
#print axioms AvailableChain.FGSA.Run.postReset_written_domain
#print axioms AvailableChain.FGSA.Run.postReset_written_first_head
#print axioms AvailableChain.FGSA.Run.postReset_written_first_head_label
#print axioms AvailableChain.FGSA.Run.postReset_written_heads_at_write_cut
#print axioms AvailableChain.FGSA.Run.postReset_written_later_result
#print axioms AvailableChain.FGSA.Run.postReset_leaseSafe_results_succ
#print axioms AvailableChain.FGSA.Run.postReset_moving_lease_compat
#print axioms AvailableChain.FGSA.Run.postReset_written_next_head
#print axioms AvailableChain.FGSA.Run.postReset_written_moving_parent
#print axioms AvailableChain.FGSA.Run.postReset_written_heads_succ
#print axioms AvailableChain.FGSA.Run.postReset_written_proposals_succ
#print axioms AvailableChain.FGSA.Run.postReset_written_finality_compatible
#print axioms AvailableChain.FGSA.Run.postReset_written_gate_lease_compat
#print axioms AvailableChain.FGSA.Run.postReset_written_outputs_succ
#print axioms AvailableChain.FGSA.Run.postReset_leaseSafe_succ
#print axioms AvailableChain.FGSA.Run.postReset_raw_first_head_above
#print axioms AvailableChain.FGSA.Run.postReset_raw_first_head
#print axioms AvailableChain.FGSA.Run.postReset_raw_first_head_label
#print axioms AvailableChain.FGSA.Run.postReset_raw_heads_at_gate_cut
#print axioms AvailableChain.FGSA.Run.postReset_raw_at_gate_cut
#print axioms AvailableChain.FGSA.Run.postReset_raw_moving_domain
#print axioms AvailableChain.FGSA.Run.postReset_resetLease_succ_all
#print axioms AvailableChain.FGSA.Run.postReset_raw_heads_succ_above
#print axioms AvailableChain.FGSA.Run.postReset_raw_proposals_succ_above
#print axioms AvailableChain.FGSA.Run.postReset_raw_finality_compatible_above
#print axioms AvailableChain.FGSA.Run.postReset_raw_gate_lease_compat
#print axioms AvailableChain.FGSA.Run.postReset_raw_outputs_succ_above
#print axioms AvailableChain.FGSA.Run.postReset_raw_heads_succ
#print axioms AvailableChain.FGSA.Run.postReset_raw_proposals_succ
#print axioms AvailableChain.FGSA.Run.postReset_raw_outputs_succ
#print axioms AvailableChain.FGSA.Run.postReset_rawTransfer_succ
#print axioms AvailableChain.FGSA.Run.postReset_resetLease_succ'
#print axioms AvailableChain.FGSA.Run.healing_release_rows_expiry
#print axioms AvailableChain.FGSA.Run.healing_proposal_receipt_recovery
#print axioms AvailableChain.FGSA.Run.healing_postReset_confirmed_reader
#print axioms AvailableChain.FGSA.Run.healing_postReset_joint_recovery
#print axioms AvailableChain.FGSA.Run.healing_postReset_inv_recovery
#print axioms AvailableChain.FGSA.Run.healing_h0_extension_recovery
#print axioms AvailableChain.FGSA.Run.healing_localInput_recovery
#print axioms AvailableChain.FGSA.Run.healing_fullInput_recovery

#print axioms AvailableChain.FGSA.Run.healing_output_moving_suffix_at
