module
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOneAdvance -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRaw -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLease -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetHigh -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossUnanimous -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchAge -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Healing.LiveDC -- shake: keep (#print axioms targets)
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRead -- shake: keep





-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.AttemptSettle -- shake: keep

-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseBoot -- shake: keep


-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAge -- shake: keep
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionTerminal -- shake: keep






-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6S -- shake: keep








-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.RepairGate -- shake: keep

-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierRead -- shake: keep

set_option linter.privateModule false

#print axioms AvailableChain.FGSA.Run.healing_row_delivery
#print axioms AvailableChain.FGSA.Run.healing_receipt_before_tick
#print axioms AvailableChain.FGSA.Run.healing_action_period
#print axioms AvailableChain.FGSA.Run.healing_delivery_clock
#print axioms AvailableChain.FGSA.Run.healing_justification_timed
#print axioms AvailableChain.FGSA.Run.healing_finality_source_clock
#print axioms AvailableChain.FGSA.Run.healing_justified_source_clock
#print axioms AvailableChain.FGSA.Run.healing_proposal_full_witness
#print axioms AvailableChain.FGSA.Run.healing_full_witness
#print axioms AvailableChain.FGSA.Run.healing_proposer_floor
#print axioms AvailableChain.FGSA.Run.healing_tGeom
#print axioms AvailableChain.FGSA.Run.healing_retained_path
#print axioms AvailableChain.FGSA.Run.healing_carried_path
#print axioms AvailableChain.FGSA.Run.healing_frozen_path
#print axioms AvailableChain.FGSA.Run.healing_witness_relay
#print axioms AvailableChain.FGSA.Run.healing_witness_relay_phase
#print axioms AvailableChain.FGSA.Run.healing_source_slot
#print axioms AvailableChain.FGSA.Run.healing_full_witness_all
#print axioms AvailableChain.FGSA.Run.frontierSearch_age_service
#print axioms AvailableChain.FGSA.Run.healing_liveDCFromWindows
#print axioms AvailableChain.FGSA.Run.healing_phase_idx_le_time
#print axioms AvailableChain.FGSA.Run.healing_phase_block_receipt
#print axioms AvailableChain.FGSA.Run.healing_evidence_spread
#print axioms AvailableChain.FGSA.Run.healing_phase_rows_spread
#print axioms AvailableChain.FGSA.Run.healing_phase_idxBefore_mono
#print axioms AvailableChain.FGSA.Run.healing_phase_lt_timeIdx
#print axioms AvailableChain.FGSA.Run.healing_frontier_mono
#print axioms AvailableChain.FGSA.Run.healing_phase_held_receipt
#print axioms AvailableChain.FGSA.Run.PostResetConeAt_def
#print axioms AvailableChain.FGSA.Run.postResetRetainedCone_iff_at
#print axioms AvailableChain.FGSA.Run.postResetRetainedCone_iff
#print axioms AvailableChain.FGSA.Run.postReset_source_label_le_sub_two
#print axioms AvailableChain.FGSA.Run.postReset_release_before_proposal
#print axioms AvailableChain.FGSA.Run.postReset_proposal_horizon
#print axioms AvailableChain.FGSA.Run.postReset_head_horizon
#print axioms AvailableChain.FGSA.Run.postReset_synchronous_window
#print axioms AvailableChain.FGSA.Run.postResetRetainedCone_of_horizon_lt
#print axioms AvailableChain.FGSA.Run.healing_postReset_retainedReads_at
#print axioms AvailableChain.FGSA.Run.healing_postReset_retainedReads
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap_remainder
#print axioms AvailableChain.FGSA.Run.healing_promotion_held_mono
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_deadline
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_deadline_strict
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_receipt
#print axioms AvailableChain.FGSA.Run.healing_promotion_row_receipt_strict
#print axioms AvailableChain.FGSA.Run.healing_promotion_maturity
#print axioms AvailableChain.FGSA.Run.healing_promotion_maturity_of_action
#print axioms AvailableChain.FGSA.Run.healing_promotion_age_gap
#print axioms AvailableChain.FGSA.Run.healing_promotion_proposal_read
#print axioms AvailableChain.FGSA.Run.healing_promotion_carrier
#print axioms AvailableChain.FGSA.Run.healing_promotion_slot_proposal
#print axioms AvailableChain.FGSA.Run.healing_promotion_gap_proposal
#print axioms AvailableChain.FGSA.Run.healing_promotion_same_rows
#print axioms AvailableChain.FGSA.Run.healing_settled_frame_strict
#print axioms AvailableChain.FGSA.Run.healing_support_idxBefore_le
#print axioms AvailableChain.FGSA.Run.healing_witness_relay_settled
#print axioms AvailableChain.FGSA.Run.healing_head_witness_relay
#print axioms AvailableChain.FGSA.Run.healing_support_gate_late
#print axioms AvailableChain.FGSA.Run.healing_support_vote_backward
#print axioms AvailableChain.FGSA.Run.healing_support_prefreeze_path
#print axioms AvailableChain.FGSA.Run.healing_support_target_path
#print axioms AvailableChain.FGSA.Run.healing_support_release_rows
#print axioms AvailableChain.FGSA.Run.healing_saved_origin
#print axioms AvailableChain.FGSA.Run.healing_clockPre_live
#print axioms AvailableChain.FGSA.Run.healing_support_vote_tick
#print axioms AvailableChain.FGSA.Run.healing_support_honest_emits
#print axioms AvailableChain.FGSA.Run.healing_support_key_cases
#print axioms AvailableChain.FGSA.Run.healing_support_gate_reads
#print axioms AvailableChain.FGSA.Run.healing_support_fastWrite
#print axioms AvailableChain.FGSA.Run.healing_support_phaseBody_of_write
#print axioms AvailableChain.FGSA.Run.healing_last_write_support
#print axioms AvailableChain.FGSA.Run.healing_support_deadline_le_vote
#print axioms AvailableChain.FGSA.Run.healing_support_vote_before_proposal
#print axioms AvailableChain.FGSA.Run.healing_last_write_two_lease
#print axioms AvailableChain.FGSA.Run.healing_last_write_one_lease
#print axioms AvailableChain.FGSA.Run.HealingInputOfH0Statement_def
#print axioms AvailableChain.FGSA.Run.healing_resetF_budget_eq
#print axioms AvailableChain.FGSA.Run.healing_resetFull_horizon
#print axioms AvailableChain.FGSA.Run.healing_time_strict_of_reset
#print axioms AvailableChain.FGSA.Run.healing_hTime_of

#print axioms AvailableChain.FGSA.Run.healing_phase_top_persist_all
#print axioms AvailableChain.FGSA.Run.healing_phase_contest_persist_of_crossing_all
#print axioms AvailableChain.FGSA.Run.healing_phase_order_of_crossing_all
#print axioms AvailableChain.FGSA.Run.healing_frontier_mono_all
#print axioms AvailableChain.FGSA.Run.healing_phase_window_all
#print axioms AvailableChain.FGSA.Run.healing_settle_start_on
#print axioms AvailableChain.FGSA.Run.healing_promotion_quiet_window
#print axioms AvailableChain.FGSA.Run.healing_phase_extend_of_no_effective
#print axioms AvailableChain.FGSA.Run.healing_recovery_restart_bound
#print axioms AvailableChain.FGSA.Run.healing_recovery_epoch
#print axioms AvailableChain.FGSA.Run.healing_recovery_durable
#print axioms AvailableChain.FGSA.Run.healing_recovery_stamps
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined
#print axioms AvailableChain.FGSA.Run.healing_recovery_receiverService
#print axioms AvailableChain.FGSA.Run.repair_head_exact
#print axioms AvailableChain.FGSA.Run.frontier_relay
#print axioms AvailableChain.FGSA.Run.frontier_head_relay

#print axioms AvailableChain.FGSA.Run.healing_recovery_frame_metadata

#print axioms AvailableChain.FGSA.Run.healing_recovery_readyTrigger

#print axioms AvailableChain.FGSA.Run.healing_settle_start
#print axioms AvailableChain.FGSA.Run.healing_settle_event
#print axioms AvailableChain.FGSA.Run.healing_rPhase
#print axioms AvailableChain.FGSA.Run.healing_attempt_settle_start
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_raise_other_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_contest_settle
#print axioms AvailableChain.FGSA.Run.healing_attempt_firstRow_other_settle

#print axioms AvailableChain.FGSA.Run.frontier_F_below_all
#print axioms AvailableChain.FGSA.Run.frontier_F_below
#print axioms AvailableChain.FGSA.Run.healing_promotion_first_receipt
#print axioms AvailableChain.FGSA.Run.healing_promotion_first_receipt_of_frontierCap
#print axioms AvailableChain.FGSA.Run.healing_promotion_block_held_mono
#print axioms AvailableChain.FGSA.Run.promotion_age_advance_of_source
#print axioms AvailableChain.FGSA.Run.healing_promotion_advance
#print axioms AvailableChain.FGSA.Run.boot_not_effective_one

#print axioms AvailableChain.FGSA.Run.healing_recovery_joinedHonest
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined_counts
#print axioms AvailableChain.FGSA.Run.repair_exact_service_on
#print axioms AvailableChain.FGSA.Run.healing_postReset_retainedReads_at_on

#print axioms AvailableChain.FGSA.Run.healing_recovery_gate_scope
#print axioms AvailableChain.FGSA.Run.healing_head_witness_relay_on
#print axioms AvailableChain.FGSA.Run.healing_support_prefreeze_path_on
#print axioms AvailableChain.FGSA.Run.healing_support_gate_cover
#print axioms AvailableChain.FGSA.Run.healing_support_emitted_head

#print axioms AvailableChain.FGSA.Run.healing_phase_top_persist
#print axioms AvailableChain.FGSA.Run.healing_phase_contest_persist_of_crossing
#print axioms AvailableChain.FGSA.Run.healing_phase_order_of_crossing

#print axioms AvailableChain.FGSA.Run.healing_promotion_age_receipt
#print axioms AvailableChain.FGSA.Run.healing_promotion_age_service
#print axioms AvailableChain.FGSA.Run.healing_renewedPromotion
#print axioms AvailableChain.FGSA.Run.healing_renewedPromotion_terminal

#print axioms AvailableChain.FGSA.Run.healing_frozen_path_on
#print axioms AvailableChain.FGSA.Run.healing_support_raw_backward_on
#print axioms AvailableChain.FGSA.Run.healing_support_target_path_on
#print axioms AvailableChain.FGSA.Run.healing_transfer_proposal_service
#print axioms AvailableChain.FGSA.Run.healing_support_honest_head
#print axioms AvailableChain.FGSA.Run.healing_support_release_compat
#print axioms AvailableChain.FGSA.Run.healing_first_transfer_core
#print axioms AvailableChain.FGSA.Run.healing_first_transfer_fast

#print axioms AvailableChain.FGSA.Run.healing_support_read_window
#print axioms AvailableChain.FGSA.Run.healing_support_vote_kept_on
#print axioms AvailableChain.FGSA.Run.healing_support_honest_batch_seat
#print axioms AvailableChain.FGSA.Run.healing_support_head_frame
#print axioms AvailableChain.FGSA.Run.healing_next_transfer_core
#print axioms AvailableChain.FGSA.Run.healing_heads_transfer
#print axioms AvailableChain.FGSA.Run.healing_fast_heads_transfer

#print axioms AvailableChain.FGSA.Run.FastSupportScope.cut_mono
#print axioms AvailableChain.FGSA.Run.healing_lease_clock_nongate
#print axioms AvailableChain.FGSA.Run.healing_lease_persist
#print axioms AvailableChain.FGSA.Run.healing_fast_source
#print axioms AvailableChain.FGSA.Run.healing_fast_lease_at
#print axioms AvailableChain.FGSA.Run.healing_fast_lease
#print axioms AvailableChain.FGSA.Run.healing_fast_heads
#print axioms AvailableChain.FGSA.Run.healing_support_frame_at
#print axioms AvailableChain.FGSA.Run.healing_output_gate_step
#print axioms AvailableChain.FGSA.Run.healing_output_cover
#print axioms AvailableChain.FGSA.Run.healing_fast_output
#print axioms AvailableChain.FGSA.Run.healing_proposal_batch_seat
#print axioms AvailableChain.FGSA.Run.healing_proposal_core
#print axioms AvailableChain.FGSA.Run.healing_proposals_cover
#print axioms AvailableChain.FGSA.Run.healing_fast_proposals

#print axioms AvailableChain.FGSA.Run.healing_saved_origin_on
#print axioms AvailableChain.FGSA.Run.SlowSupportScope.cut_mono
#print axioms AvailableChain.FGSA.Run.healing_clock_nongate
#print axioms AvailableChain.FGSA.Run.healing_slow_window
#print axioms AvailableChain.FGSA.Run.healing_slow_majority
#print axioms AvailableChain.FGSA.Run.healing_support_honest_late
#print axioms AvailableChain.FGSA.Run.healing_slow_honest_seat
#print axioms AvailableChain.FGSA.Run.healing_slow_lease_window
#print axioms AvailableChain.FGSA.Run.healing_slow_lease_at
#print axioms AvailableChain.FGSA.Run.healing_slow_lease
#print axioms AvailableChain.FGSA.Run.healing_slow_first_transfer
#print axioms AvailableChain.FGSA.Run.healing_slow_heads
#print axioms AvailableChain.FGSA.Run.healing_slow_proposals
#print axioms AvailableChain.FGSA.Run.healing_slow_output
#print axioms AvailableChain.FGSA.Run.healing_phase_transfers
#print axioms AvailableChain.FGSA.Run.healing_tPerm_at
#print axioms AvailableChain.FGSA.Run.frontier_head_relay_on
#print axioms AvailableChain.FGSA.Run.frontier_head_batch_seat
#print axioms AvailableChain.FGSA.Run.frontier_next_transfer_core
#print axioms AvailableChain.FGSA.Run.frontier_first_transfer_core
#print axioms AvailableChain.FGSA.Run.frontier_first_transfer_fast
#print axioms AvailableChain.FGSA.Run.frontier_first_transfer_slow
#print axioms AvailableChain.FGSA.Run.frontier_heads_transfer
#print axioms AvailableChain.FGSA.Run.frontier_Q_heads
#print axioms AvailableChain.FGSA.Run.frontier_fast_heads
#print axioms AvailableChain.FGSA.Run.frontier_slow_heads

#print axioms AvailableChain.FGSA.Run.frontier_proposal_batch_seat

#print axioms AvailableChain.FGSA.Run.frontier_prior_support

#print axioms AvailableChain.FGSA.Run.frontier_target_scores

#print axioms AvailableChain.FGSA.Run.repair_liveRoot_cases

#print axioms AvailableChain.FGSA.Run.repair_F_preceq_Z

#print axioms AvailableChain.FGSA.Run.repair_prior_support

#print axioms AvailableChain.FGSA.Run.repair_controls_clock

#print axioms AvailableChain.FGSA.Run.repair_liveRoot_witness

#print axioms AvailableChain.FGSA.Run.repair_fullTree_nonempty

#print axioms AvailableChain.FGSA.Run.repair_idx_lt

#print axioms AvailableChain.FGSA.Run.repair_h6_frame

#print axioms AvailableChain.FGSA.Run.repair_read_row

#print axioms AvailableChain.FGSA.Run.repair_h6_input

#print axioms AvailableChain.FGSA.Run.repair_proposal_emission

#print axioms AvailableChain.FGSA.Run.repair_head_exact_legacy

#print axioms AvailableChain.FGSA.Run.repair_slot_lt_of_time

#print axioms AvailableChain.FGSA.Run.repair_lease_cover_of_split

#print axioms AvailableChain.FGSA.Run.repair_lease_cover_two

#print axioms AvailableChain.FGSA.Run.repair_head_after_two

#print axioms AvailableChain.FGSA.Run.retainedH6Input_on_repaired_reads

#print axioms AvailableChain.FGSA.Run.repair_head_two

#print axioms AvailableChain.FGSA.Run.repair_h6c_window

#print axioms AvailableChain.FGSA.Run.repair_head_after_one

#print axioms AvailableChain.FGSA.Run.repair_lease_cover_one

#print axioms AvailableChain.FGSA.Run.retainedH6Input_on_synchronous_reads

#print axioms AvailableChain.FGSA.Run.repair_head_one

#print axioms AvailableChain.FGSA.Run.healing_source_label_bound

#print axioms AvailableChain.FGSA.Run.healing_source_relay_deadline

#print axioms AvailableChain.FGSA.Run.healing_source_row_label

#print axioms AvailableChain.FGSA.Run.healing_tf_retention

#print axioms AvailableChain.FGSA.Run.healing_tf_retention_on

#print axioms AvailableChain.FGSA.Run.healing_source_path_retained

#print axioms AvailableChain.FGSA.Run.healing_source_path_retained_on

#print axioms AvailableChain.FGSA.Run.healing_source_supporter_head

#print axioms AvailableChain.FGSA.Run.healing_source_body_relay

#print axioms AvailableChain.FGSA.Run.healing_source_body_stamps

#print axioms AvailableChain.FGSA.Run.healing_source_old_body

#print axioms AvailableChain.FGSA.Run.healing_recoveryStart_ge

#print axioms AvailableChain.FGSA.Run.healing_tDel

#print axioms AvailableChain.FGSA.Run.healing_tDelReset_core

#print axioms AvailableChain.FGSA.Run.healing_tDelReset

#print axioms AvailableChain.FGSA.Run.SrcN_def

#print axioms AvailableChain.FGSA.Run.HighSrcN_def

#print axioms AvailableChain.FGSA.Run.Lost_def

#print axioms AvailableChain.FGSA.Run.healing_srcN_of_source

#print axioms AvailableChain.FGSA.Run.healing_headAtIdx_tick

#print axioms AvailableChain.FGSA.Run.healing_idx_lt_of_time_lt

#print axioms AvailableChain.FGSA.Run.healing_source_decode

#print axioms AvailableChain.FGSA.Run.healing_high_source_sync

#print axioms AvailableChain.FGSA.Run.healing_high_source_labelSync

#print axioms AvailableChain.FGSA.Run.healing_loss_same

#print axioms AvailableChain.FGSA.Run.healing_source_supporter

#print axioms AvailableChain.FGSA.Run.healing_loss_of_supporter

#print axioms AvailableChain.FGSA.Run.healing_loss_support

#print axioms AvailableChain.FGSA.Run.healing_first_transfer_domain

#print axioms AvailableChain.FGSA.Run.healing_block_receipt_sync

#print axioms AvailableChain.FGSA.Run.healing_block_path_sync

#print axioms AvailableChain.FGSA.Run.healing_block_stamp_le_now

#print axioms AvailableChain.FGSA.Run.healing_batch_seat_sync

#print axioms AvailableChain.FGSA.Run.healing_next_transfer_domain

#print axioms AvailableChain.FGSA.Run.healing_loss_lease_late

#print axioms AvailableChain.FGSA.Run.repair_stored_slot_le

#print axioms AvailableChain.FGSA.Run.repair_stored_slot_lt

#print axioms AvailableChain.FGSA.Run.repair_source_mem

#print axioms AvailableChain.FGSA.Run.repair_finality_slot

#print axioms AvailableChain.FGSA.Run.repair_proposal_slot

#print axioms AvailableChain.FGSA.Run.repair_gate_finality_le

#print axioms AvailableChain.FGSA.Run.repair_gate_receipt

#print axioms AvailableChain.FGSA.Run.repair_gate_fast_count

#print axioms AvailableChain.FGSA.Run.repair_gate_guard

#print axioms AvailableChain.FGSA.Run.repair_output_bound

#print axioms AvailableChain.FGSA.Run.repair_gate_old_output

#print axioms AvailableChain.FGSA.Run.repair_gate_opening

#print axioms AvailableChain.FGSA.Run.repair_gate_geometry

#print axioms AvailableChain.FGSA.Run.FrontierReadScope.cut_mono

#print axioms AvailableChain.FGSA.Run.frontier_seed_leases

#print axioms AvailableChain.FGSA.Run.frontier_lease_cover

#print axioms AvailableChain.FGSA.Run.frontier_pivot_held

#print axioms AvailableChain.FGSA.Run.retainedHG1Input_through

#print axioms AvailableChain.FGSA.Run.retainedHG1Input_before_first_rise

#print axioms AvailableChain.FGSA.Run.frontier_cap_before_on

#print axioms AvailableChain.FGSA.Run.healing_domain_filter_F

#print axioms AvailableChain.FGSA.Run.healing_head_covers_root

#print axioms AvailableChain.FGSA.Run.healing_loss_late_source

#print axioms AvailableChain.FGSA.Run.healing_loss_single_cause

#print axioms AvailableChain.FGSA.Run.healing_loss_cause_of_view

#print axioms AvailableChain.FGSA.Run.healing_noLoss_heads

#print axioms AvailableChain.FGSA.Run.healing_loss_F_below

#print axioms AvailableChain.FGSA.Run.healing_source_receipt

#print axioms AvailableChain.FGSA.Run.healing_loss_domain

#print axioms AvailableChain.FGSA.Run.healing_loss_cause

#print axioms AvailableChain.FGSA.Run.healing_high_source_compat

#print axioms AvailableChain.FGSA.Run.healing_high_source_compat_reset

#print axioms AvailableChain.FGSA.Run.healing_unanimous_release_compat

#print axioms AvailableChain.FGSA.Run.healing_unanimous_next_transfer_kept

#print axioms AvailableChain.FGSA.Run.healing_delivery_clock_on

#print axioms AvailableChain.FGSA.Run.healing_finality_source_clock_on

#print axioms AvailableChain.FGSA.Run.healing_justified_source_clock_on

#print axioms AvailableChain.FGSA.Run.postReset_high_compatible_all

#print axioms AvailableChain.FGSA.Run.postReset_high_compatible_succ

#print axioms AvailableChain.FGSA.Run.postReset_reset_compatible_all

#print axioms AvailableChain.FGSA.Run.postReset_reset_compatible_succ

#print axioms AvailableChain.FGSA.Run.postReset_descent_kept

#print axioms AvailableChain.FGSA.Run.postReset_descent_kept_of_compat

#print axioms AvailableChain.FGSA.Run.postReset_general_kept_of_compat

#print axioms AvailableChain.FGSA.Run.postReset_rKeep_body_of_compat

#print axioms AvailableChain.FGSA.Run.postReset_rKeep_body_reset

#print axioms AvailableChain.FGSA.Run.postReset_selected_label_above

#print axioms AvailableChain.FGSA.Run.postReset_selected_label

#print axioms AvailableChain.FGSA.Run.SelectedBefore_def

#print axioms AvailableChain.FGSA.Run.selectedBefore_of_sourceBefore

#print axioms AvailableChain.FGSA.Run.postReset_selected_reset_compatible

#print axioms AvailableChain.FGSA.Run.postReset_general_kept

#print axioms AvailableChain.FGSA.Run.postReset_receiver_compatible

#print axioms AvailableChain.FGSA.Run.postReset_tDel

#print axioms AvailableChain.FGSA.Run.postReset_keep_height

#print axioms AvailableChain.FGSA.Run.postReset_keep_contest

#print axioms AvailableChain.FGSA.Run.postReset_keep_floor

#print axioms AvailableChain.FGSA.Run.postReset_keep_roots

#print axioms AvailableChain.FGSA.Run.postReset_keep_witness

#print axioms AvailableChain.FGSA.Run.postReset_keep_body

#print axioms AvailableChain.FGSA.Run.postReset_protected_kept_succ

#print axioms AvailableChain.FGSA.Run.postReset_rKeep_body

#print axioms AvailableChain.FGSA.Run.postReset_leaseSafe_antecedent_of_lastWrite

#print axioms AvailableChain.FGSA.Run.postReset_fProv_all

#print axioms AvailableChain.FGSA.Run.postReset_rFProv_reset

#print axioms AvailableChain.FGSA.Run.postReset_h5RawTransfer_body

#print axioms AvailableChain.FGSA.Run.healing_gate_result_supporter

#print axioms AvailableChain.FGSA.Run.postReset_delivery_no_obligation

#print axioms AvailableChain.FGSA.Run.postReset_resetLease_preserve

#print axioms AvailableChain.FGSA.Run.postReset_resetLease_base

#print axioms AvailableChain.FGSA.Run.healing_first_transfer_raw_domain

#print axioms AvailableChain.FGSA.Run.postReset_slow_window_sync

#print axioms AvailableChain.FGSA.Run.postReset_raw_reset_compatible

#print axioms AvailableChain.FGSA.Run.postReset_noRewrite

#print axioms AvailableChain.FGSA.Run.healing_output_moving_suffix

#print axioms AvailableChain.FGSA.Run.postReset_resetLease_at_reset

#print axioms AvailableChain.FGSA.Run.postReset_resetLease_succ

#print axioms AvailableChain.FGSA.Run.postReset_raw_release_compatible

#print axioms AvailableChain.FGSA.Run.postReset_raw_moving_lease_compat

#print axioms AvailableChain.FGSA.Run.healing_proposal_moving_domain

#print axioms AvailableChain.FGSA.Run.healing_proposal_moving_parent

#print axioms AvailableChain.FGSA.Run.postReset_resetLease_zero

#print axioms AvailableChain.FGSA.Run.postReset_rawTransfer_before_reset

#print axioms AvailableChain.FGSA.Run.postReset_resetLease_step

#print axioms AvailableChain.FGSA.Run.healing_low_finality_after_reset

#print axioms AvailableChain.FGSA.Run.healing_low_finality_after_reset_on

#print axioms AvailableChain.FGSA.Run.healing_low_finality_at_reset_reset

#print axioms AvailableChain.FGSA.Run.healing_resetTransferCore

#print axioms AvailableChain.FGSA.Run.healing_tDelReset_of_reset

#print axioms AvailableChain.FGSA.Run.healing_rise_one_advance

-- Round 4: actual joins and selected per-receiver carrier receipts.
#print axioms AvailableChain.FGSA.Run.healing_head_carrier_receipt
#print axioms AvailableChain.FGSA.Run.healing_gate_enabled_of_joined
#print axioms AvailableChain.FGSA.Run.healing_gate_enabled_of_result
#print axioms AvailableChain.FGSA.Run.healing_recovery_later_gate
#print axioms AvailableChain.FGSA.Run.healingJoinedSeats_mem
#print axioms AvailableChain.FGSA.Run.FastSupportScope.firstOn
#print axioms AvailableChain.FGSA.Run.healing_support_gate_scope_of_cut
#print axioms AvailableChain.FGSA.Run.healing_head_carrier_demand_phase
#print axioms AvailableChain.FGSA.Run.healing_support_gate_scope_of_batch
#print axioms AvailableChain.FGSA.Run.healing_support_gate_geometry

-- Round 6: late batch windows and services at actual joined readers.
#print axioms AvailableChain.FGSA.Run.HealingWindow
#print axioms AvailableChain.FGSA.Run.StrongHealingWindow
#print axioms AvailableChain.FGSA.Run.StrongHealingWindow.window
#print axioms AvailableChain.FGSA.Run.HealingWindow.cut_mono
#print axioms AvailableChain.FGSA.Run.HealingWindow.sync
#print axioms AvailableChain.FGSA.Run.HealingWindow.prior
#print axioms AvailableChain.FGSA.Run.HealingWindow.after
#print axioms AvailableChain.FGSA.Run.healing_window_of_cut
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined_window
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined_next
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined_vote_next
#print axioms AvailableChain.FGSA.Run.healing_recovery_next_vote_joined_of_cut
#print axioms AvailableChain.FGSA.Run.healing_recovery_joined_proposal_next
#print axioms AvailableChain.FGSA.Run.healingJoinedSeats_card
#print axioms AvailableChain.FGSA.Run.healing_recovery_seat_counts
#print axioms AvailableChain.FGSA.Run.healing_recovery_seat_rivals
#print axioms AvailableChain.FGSA.Run.healing_high_source_recoveryStart
#print axioms AvailableChain.FGSA.Run.healing_window_of_recoveryStart
#print axioms AvailableChain.FGSA.Run.healing_high_source_window
#print axioms AvailableChain.FGSA.Run.HealingJoinedTick
#print axioms AvailableChain.FGSA.Run.HealingCarriersAt
#print axioms AvailableChain.FGSA.Run.healing_joined_tick_of_guard
#print axioms AvailableChain.FGSA.Run.healing_joined_tick_of_window
#print axioms AvailableChain.FGSA.Run.healing_carriers_window_at
#print axioms AvailableChain.FGSA.Run.healing_carriers_cut_at
#print axioms AvailableChain.FGSA.Run.FirstTransferScope.carriersOn
#print axioms AvailableChain.FGSA.Run.healing_support_honest_head_joined
#print axioms AvailableChain.FGSA.Run.healing_recovery_gate_enabled
#print axioms AvailableChain.FGSA.Run.healing_gate_cut_of_batch_cut
#print axioms AvailableChain.FGSA.Run.RepairHeadServices.target
#print axioms AvailableChain.FGSA.Run.healing_promotion_same_rows_on
#print axioms AvailableChain.FGSA.Run.healing_promotion_advance_on
#print axioms AvailableChain.FGSA.Run.healing_recovery_same_label
