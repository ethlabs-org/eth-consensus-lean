module
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryService -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.ResetCut -- shake: keep

public section

#print axioms AvailableChain.FGSA.Run.healing_scope_enabled_gate
#print axioms AvailableChain.FGSA.Run.healing_scope_restart_bound
#print axioms AvailableChain.FGSA.Run.healing_recovery_restart_cutoff
#print axioms AvailableChain.FGSA.Run.healing_recovery_joinedNow
#print axioms AvailableChain.FGSA.Run.healing_recovery_gate_reader
#print axioms AvailableChain.FGSA.Run.healing_recovery_restartFree
#print axioms AvailableChain.FGSA.Run.healing_recovery_action_epoch
#print axioms AvailableChain.FGSA.Run.healing_recovery_action_stamps
#print axioms AvailableChain.FGSA.Run.healing_scope_durable
#print axioms AvailableChain.FGSA.Run.healing_recovery_finality
#print axioms AvailableChain.FGSA.Run.healing_scope_stamps
#print axioms AvailableChain.FGSA.Run.healing_recovery_frame_prefixes
#print axioms AvailableChain.FGSA.Run.healing_recovery_action_frame
#print axioms AvailableChain.FGSA.Run.healing_accepted_proposal_service
#print axioms AvailableChain.FGSA.Run.healing_accepted_target_service
#print axioms AvailableChain.FGSA.Run.healing_emitted_proposal_service
#print axioms AvailableChain.FGSA.Run.healing_emitted_head_service
#print axioms AvailableChain.FGSA.Run.reset_period_lower
#print axioms AvailableChain.FGSA.Run.reset_action_exists
#print axioms AvailableChain.FGSA.Run.reset_rG_after
#print axioms AvailableChain.FGSA.Run.reset_rG_first
#print axioms AvailableChain.FGSA.Run.reset_cut
#print axioms AvailableChain.FGSA.Run.reset_first_action_upper
#print axioms AvailableChain.FGSA.Run.reset_cut_lower
#print axioms AvailableChain.FGSA.Run.reset_cut_upper
#print axioms AvailableChain.FGSA.Run.reset_frontier
#print axioms AvailableChain.FGSA.Run.reset_inclusive_frontier
#print axioms AvailableChain.FGSA.Run.reset_inclusive_start_iff
#print axioms AvailableChain.FGSA.Run.reset_row_cap
#print axioms AvailableChain.FGSA.Run.reset_old_row_before_cut
#print axioms AvailableChain.FGSA.Run.reset_old_height_sup_le
#print axioms AvailableChain.FGSA.Run.reset_mu_le_iff

end

#print axioms AvailableChain.FGSA.Run.WitnessReceiptScope.atRead

#print axioms AvailableChain.FGSA.Run.WitnessHeldScope.atRead

#print axioms AvailableChain.FGSA.Run.HeadWitnessReceiptScope.witness

#print axioms AvailableChain.FGSA.Run.PhaseWitnessReceiptScope.frontier

#print axioms AvailableChain.FGSA.Run.PhaseWitnessReceiptScope.top

#print axioms AvailableChain.FGSA.Run.PhaseWitnessReceiptScope.contest

#print axioms AvailableChain.FGSA.Run.healing_proposal_gap
#print axioms AvailableChain.FGSA.Run.healing_proposal_phase_reader_floor
#print axioms AvailableChain.FGSA.Run.healing_settled_frame_ready

#print axioms AvailableChain.FGSA.Run.healing_capped_witness_reader_floor
