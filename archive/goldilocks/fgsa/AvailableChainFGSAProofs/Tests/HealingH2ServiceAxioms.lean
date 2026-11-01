module






-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchFull -- shake: keep

public section

#print axioms AvailableChain.FGSA.Run.opening_heads_cover
#print axioms AvailableChain.FGSA.Run.opening_gate_guard
#print axioms AvailableChain.FGSA.Run.opening_gateService_of_cover
#print axioms AvailableChain.FGSA.Run.opening_postClock_of_tick
#print axioms AvailableChain.FGSA.Run.opening_domain_clock
#print axioms AvailableChain.FGSA.Run.opening_proposal_band
#print axioms AvailableChain.FGSA.Run.opening_domain_of_band
#print axioms AvailableChain.FGSA.Run.later_opening_service
#print axioms AvailableChain.FGSA.Run.later_opening_gateService_domain
#print axioms AvailableChain.FGSA.Run.opening_transfer
#print axioms AvailableChain.FGSA.Run.opening_timeIdx_mono
#print axioms AvailableChain.FGSA.Run.opening_phase_restrict
#print axioms AvailableChain.FGSA.Run.opening_source_body
#print axioms AvailableChain.FGSA.Run.later_opening_source_extends
#print axioms AvailableChain.FGSA.Run.next_opening_body_service
#print axioms AvailableChain.FGSA.Run.later_opening_covered
#print axioms AvailableChain.FGSA.Run.opening_first_time_bound
#print axioms AvailableChain.FGSA.Run.opening_entry_one
#print axioms AvailableChain.FGSA.Run.opening_height_one
#print axioms AvailableChain.FGSA.Run.common_first_opening_labels
#print axioms AvailableChain.FGSA.Run.common_first_time_bound
#print axioms AvailableChain.FGSA.Run.common_source_tick
#print axioms AvailableChain.FGSA.Run.common_source_height_le
#print axioms AvailableChain.FGSA.Run.common_source_below_raw
#print axioms AvailableChain.FGSA.Run.common_sources_compatible
#print axioms AvailableChain.FGSA.Run.common_entry_of_plateau
#print axioms AvailableChain.FGSA.Run.common_low_or_high
#print axioms AvailableChain.FGSA.Run.common_sources_extend_and_cap
#print axioms AvailableChain.FGSA.Run.common_entry_at_high
#print axioms AvailableChain.FGSA.Run.common_next_sources_extend_and_cap
#print axioms AvailableChain.FGSA.Run.common_next_entry
#print axioms AvailableChain.FGSA.Run.common_entry_at_low
#print axioms AvailableChain.FGSA.Run.common_opening_covered
#print axioms AvailableChain.FGSA.Run.common_sameLabel_scope
#print axioms AvailableChain.FGSA.Run.healing_tCommon
#print axioms AvailableChain.FGSA.Run.common_height_one
#print axioms AvailableChain.FGSA.Run.frontierOpeningServed_intro
#print axioms AvailableChain.FGSA.Run.frontier_open_indices
#print axioms AvailableChain.FGSA.Run.frontier_open_domain
#print axioms AvailableChain.FGSA.Run.frontier_open_plateau
#print axioms AvailableChain.FGSA.Run.frontier_open_of_served
#print axioms AvailableChain.FGSA.Run.frontier_open_q_eq
#print axioms AvailableChain.FGSA.Run.frontier_open_later
#print axioms AvailableChain.FGSA.Run.frontier_open_time
#print axioms AvailableChain.FGSA.Run.frontier_openings
#print axioms AvailableChain.FGSA.Run.frontierSeedQualification_iff
#print axioms AvailableChain.FGSA.Run.tfSeed_two_from_tRepair
#print axioms AvailableChain.FGSA.Run.tfSeed_one_from_tRepair
#print axioms AvailableChain.FGSA.Run.tfSeed_later
#print axioms AvailableChain.FGSA.Run.frontier_seed_vote_cutoff
#print axioms AvailableChain.FGSA.Run.tfSeed_qSucc_lease_cover
#print axioms AvailableChain.FGSA.Run.frontier_seed_qSucc_input
#print axioms AvailableChain.FGSA.Run.frontier_seed_qSucc_head
#print axioms AvailableChain.FGSA.Run.frontier_repair_gate_scope
#print axioms AvailableChain.FGSA.Run.frontier_gate_guard_of_receipts
#print axioms AvailableChain.FGSA.Run.frontier_gate_geometry
#print axioms AvailableChain.FGSA.Run.frontier_proposals_cover
#print axioms AvailableChain.FGSA.Run.frontier_output_cover
#print axioms AvailableChain.FGSA.Run.frontier_gate_guard_of_cover
#print axioms AvailableChain.FGSA.Run.frontier_opening_gateService_of_cover
#print axioms AvailableChain.FGSA.Run.frontier_exactService_of_heads
#print axioms AvailableChain.FGSA.Run.frontier_seed_qSucc_exactService
#print axioms AvailableChain.FGSA.Run.frontier_later_head
#print axioms AvailableChain.FGSA.Run.frontier_later_exactService
#print axioms AvailableChain.FGSA.Run.frontier_service_core
#print axioms AvailableChain.FGSA.Run.frontier_service
#print axioms AvailableChain.FGSA.Run.repair_honest_proposal
#print axioms AvailableChain.FGSA.Run.repair_grid_Γ
#print axioms AvailableChain.FGSA.Run.repair_lt_Γ
#print axioms AvailableChain.FGSA.Run.repair_exact_service
#print axioms AvailableChain.FGSA.Run.repair_after_of_cover
#print axioms AvailableChain.FGSA.Run.repair_two_lease
#print axioms AvailableChain.FGSA.Run.repair_synchronous
#print axioms AvailableChain.FGSA.Run.healing_tRepair
#print axioms AvailableChain.FGSA.Run.healing_rise_one_of_frontier
#print axioms AvailableChain.FGSA.Run.healing_rise_one_frontier
#print axioms AvailableChain.FGSA.Run.healing_rise_one_phase
#print axioms AvailableChain.FGSA.Run.healing_rise_one_split
#print axioms AvailableChain.FGSA.Run.healing_rise_one_entry
#print axioms AvailableChain.FGSA.Run.healing_rise_one_gate_copy
#print axioms AvailableChain.FGSA.Run.healing_rise_one_height
#print axioms AvailableChain.FGSA.Run.healing_rise_one_rows_received
#print axioms AvailableChain.FGSA.Run.frontierSearch_event_time_le
#print axioms AvailableChain.FGSA.Run.frontierSearch_first_effective_split
#print axioms AvailableChain.FGSA.Run.frontierSearch_classify_stop
#print axioms AvailableChain.FGSA.Run.frontierSearch_first_rise
#print axioms AvailableChain.FGSA.Run.frontierSearch_first_row
#print axioms AvailableChain.FGSA.Run.frontierSearch_first_row_unique
#print axioms AvailableChain.FGSA.Run.frontierSearch_skipped_row
#print axioms AvailableChain.FGSA.Run.frontierSearch_phase_step_of_crossing
#print axioms AvailableChain.FGSA.Run.frontierSearch_strict_cap_or_rise
#print axioms AvailableChain.FGSA.Run.frontierSearch_timeIdx_le_idxBefore
#print axioms AvailableChain.FGSA.Run.frontierSearch_rise_mono
#print axioms AvailableChain.FGSA.Run.frontierSearch_rise_of_receipt
#print axioms AvailableChain.FGSA.Run.healing_frontierTail_row
#print axioms AvailableChain.FGSA.Run.frontierHG2aResult_iff
#print axioms AvailableChain.FGSA.Run.frontierSearch_hg2a_bound
#print axioms AvailableChain.FGSA.Run.frontierSearch_hg2a_gate_cost
#print axioms AvailableChain.FGSA.Run.frontierSearch_hg2a_gap
#print axioms AvailableChain.FGSA.Run.frontier_hg2a_receipt
#print axioms AvailableChain.FGSA.Run.healing_frontierTail_rise_of_seed
#print axioms AvailableChain.FGSA.Run.healing_frontierTail_rise
#print axioms AvailableChain.FGSA.Run.healing_frontierTail

#print axioms AvailableChain.FGSA.Run.frontierSearch_timeIdx_mono

#print axioms AvailableChain.FGSA.Run.frontierSearch_phase_cut

#print axioms AvailableChain.FGSA.Run.frontierSearch_repair_seed

#print axioms AvailableChain.FGSA.Run.frontierSearch_seed_after

#print axioms AvailableChain.FGSA.Run.frontierSearch_proposal_heights

#print axioms AvailableChain.FGSA.Run.frontierSearch_seed_repair

#print axioms AvailableChain.FGSA.Run.frontierSearch_save_seed

#print axioms AvailableChain.FGSA.Run.frontier_hg3_contest

#print axioms AvailableChain.FGSA.Run.frontierSearch_period_bound

#print axioms AvailableChain.FGSA.Run.frontierSearch_gap_phase

#print axioms AvailableChain.FGSA.Run.frontier_hg3_gap

#print axioms AvailableChain.FGSA.Run.frontierSearch_initial_J_age

#print axioms AvailableChain.FGSA.Run.frontier_hg3_topJ

#print axioms AvailableChain.FGSA.Run.frontierSearch_repair_start

#print axioms AvailableChain.FGSA.Run.frontierSearch_allowance_nonneg

#print axioms AvailableChain.FGSA.Run.frontierSearch_rise_rebase

#print axioms AvailableChain.FGSA.Run.frontierSearch_rise_of_stop

#print axioms AvailableChain.FGSA.Run.frontierSearch_remaining_eq

#print axioms AvailableChain.FGSA.Run.frontierSearch_phase_tail

#print axioms AvailableChain.FGSA.Run.frontierSearch_task_bounds

#print axioms AvailableChain.FGSA.Run.frontierSearch_rise_task

#print axioms AvailableChain.FGSA.Run.frontierSearch_row_of_rise

#print axioms AvailableChain.FGSA.Run.frontierSearch_row_task

#print axioms AvailableChain.FGSA.Run.frontierSearch_cut_start

#print axioms AvailableChain.FGSA.Run.frontierSearch_event_time_mono

#print axioms AvailableChain.FGSA.Run.frontierSearch_phase_exists

#print axioms AvailableChain.FGSA.Run.healing_frontierSearch

end

#print axioms AvailableChain.FGSA.Run.frontier_seed_readers
#print axioms AvailableChain.FGSA.Run.FrontierReadScope.first
