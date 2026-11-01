module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationJoint -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Shared.Claims
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationFrame
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationGate
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationReceipt

public section

namespace AvailableChain.FGSA.Run.Tests.OutageContinuationAxioms

-- Typed audit targets retain the imported proof dependencies in the compiled test.

theorem audit_outageV_iff_vote_bound :
    type_of% (@AvailableChain.FGSA.Run.outageV_iff_vote_bound) :=
  @AvailableChain.FGSA.Run.outageV_iff_vote_bound
#print axioms audit_outageV_iff_vote_bound
theorem audit_outageV_iff_restored_label :
    type_of% (@AvailableChain.FGSA.Run.outageV_iff_restored_label) :=
  @AvailableChain.FGSA.Run.outageV_iff_restored_label
#print axioms audit_outageV_iff_restored_label
theorem audit_outageV_vote_before_expiry :
    type_of% (@AvailableChain.FGSA.Run.outageV_vote_before_expiry) :=
  @AvailableChain.FGSA.Run.outageV_vote_before_expiry
#print axioms audit_outageV_vote_before_expiry
theorem audit_outageV_old_gate_before_expiry :
    type_of% (@AvailableChain.FGSA.Run.outageV_old_gate_before_expiry) :=
  @AvailableChain.FGSA.Run.outageV_old_gate_before_expiry
#print axioms audit_outageV_old_gate_before_expiry
theorem audit_outageV_boundary :
    type_of% (@AvailableChain.FGSA.Run.outageV_boundary) :=
  @AvailableChain.FGSA.Run.outageV_boundary
#print axioms audit_outageV_boundary
theorem audit_outageV_arming_prem :
    type_of% (@AvailableChain.FGSA.Run.outageV_arming_prem) :=
  @AvailableChain.FGSA.Run.outageV_arming_prem
#print axioms audit_outageV_arming_prem
theorem audit_outageV_source_relay_before_freeze :
    type_of% (@AvailableChain.FGSA.Run.outageV_source_relay_before_freeze) :=
  @AvailableChain.FGSA.Run.outageV_source_relay_before_freeze
#print axioms audit_outageV_source_relay_before_freeze
theorem audit_outageV_regression_relay_bound :
    type_of% (@AvailableChain.FGSA.Run.outageV_regression_relay_bound) :=
  @AvailableChain.FGSA.Run.outageV_regression_relay_bound
#print axioms audit_outageV_regression_relay_bound
theorem audit_outage_early_event_state :
    type_of% (@AvailableChain.FGSA.Run.outage_early_event_state) :=
  @AvailableChain.FGSA.Run.outage_early_event_state
#print axioms audit_outage_early_event_state
theorem audit_outageV_contest_top :
    type_of% (@AvailableChain.FGSA.Run.outageV_contest_top) :=
  @AvailableChain.FGSA.Run.outageV_contest_top
#print axioms audit_outageV_contest_top
theorem audit_outageV_contested_filter :
    type_of% (@AvailableChain.FGSA.Run.outageV_contested_filter) :=
  @AvailableChain.FGSA.Run.outageV_contested_filter
#print axioms audit_outageV_contested_filter
theorem audit_outageV_entry_above :
    type_of% (@AvailableChain.FGSA.Run.outageV_entry_above) :=
  @AvailableChain.FGSA.Run.outageV_entry_above
#print axioms audit_outageV_entry_above
theorem audit_outageV_taller_carrier :
    type_of% (@AvailableChain.FGSA.Run.outageV_taller_carrier) :=
  @AvailableChain.FGSA.Run.outageV_taller_carrier
#print axioms audit_outageV_taller_carrier
theorem audit_outageV_received_height :
    type_of% (@AvailableChain.FGSA.Run.outageV_received_height) :=
  @AvailableChain.FGSA.Run.outageV_received_height
#print axioms audit_outageV_received_height
theorem audit_outageV_contested_frame_from_rows :
    type_of% (@AvailableChain.FGSA.Run.outageV_contested_frame_from_rows) :=
  @AvailableChain.FGSA.Run.outageV_contested_frame_from_rows
#print axioms audit_outageV_contested_frame_from_rows
theorem audit_outageV_partition_rejects :
    type_of% (@AvailableChain.FGSA.Run.outageV_partition_rejects) :=
  @AvailableChain.FGSA.Run.outageV_partition_rejects
#print axioms audit_outageV_partition_rejects
theorem audit_outageV_result_majority :
    type_of% (@AvailableChain.FGSA.Run.outageV_result_majority) :=
  @AvailableChain.FGSA.Run.outageV_result_majority
#print axioms audit_outageV_result_majority
theorem audit_outageV_gate_compatible :
    type_of% (@AvailableChain.FGSA.Run.outageV_gate_compatible) :=
  @AvailableChain.FGSA.Run.outageV_gate_compatible
#print axioms audit_outageV_gate_compatible
theorem audit_outageV_write_and_normalize :
    type_of% (@AvailableChain.FGSA.Run.outageV_write_and_normalize) :=
  @AvailableChain.FGSA.Run.outageV_write_and_normalize
#print axioms audit_outageV_write_and_normalize

theorem audit_outage_armed_induction_scoped :
    type_of% (@AvailableChain.FGSA.Run.outage_armed_induction_scoped) :=
  @AvailableChain.FGSA.Run.outage_armed_induction_scoped
#print axioms audit_outage_armed_induction_scoped
theorem audit_outageV_marker_frame :
    type_of% (@AvailableChain.FGSA.Run.outageV_marker_frame) :=
  @AvailableChain.FGSA.Run.outageV_marker_frame
#print axioms audit_outageV_marker_frame

theorem audit_outageV_first_restored_exists :
    type_of% (@AvailableChain.FGSA.Run.outageV_first_restored_exists) :=
  @AvailableChain.FGSA.Run.outageV_first_restored_exists
#print axioms audit_outageV_first_restored_exists
theorem audit_outageV_contest_carrier :
    type_of% (@AvailableChain.FGSA.Run.outageV_contest_carrier) :=
  @AvailableChain.FGSA.Run.outageV_contest_carrier
#print axioms audit_outageV_contest_carrier
theorem audit_outageV_gate_of_compatible_batch :
    type_of% (@AvailableChain.FGSA.Run.outageV_gate_of_compatible_batch) :=
  @AvailableChain.FGSA.Run.outageV_gate_of_compatible_batch
#print axioms audit_outageV_gate_of_compatible_batch

theorem audit_outage_source_held_at_action :
    type_of% (@AvailableChain.FGSA.Run.outage_source_held_at_action) :=
  @AvailableChain.FGSA.Run.outage_source_held_at_action
#print axioms audit_outage_source_held_at_action
theorem audit_outage_frozen_selected_ancestor :
    type_of% (@AvailableChain.FGSA.Run.outage_frozen_selected_ancestor) :=
  @AvailableChain.FGSA.Run.outage_frozen_selected_ancestor
#print axioms audit_outage_frozen_selected_ancestor
theorem audit_outageV_active_path_of_coverage :
    type_of% (@AvailableChain.FGSA.Run.outageV_active_path_of_coverage) :=
  @AvailableChain.FGSA.Run.outageV_active_path_of_coverage
#print axioms audit_outageV_active_path_of_coverage

theorem audit_outageV_head_covers_of_witnesses :
    type_of% (@AvailableChain.FGSA.Run.outageV_head_covers_of_witnesses) :=
  @AvailableChain.FGSA.Run.outageV_head_covers_of_witnesses
#print axioms audit_outageV_head_covers_of_witnesses

theorem audit_outageV_liveRoot_compatible :
    type_of% (@AvailableChain.FGSA.Run.outageV_liveRoot_compatible) :=
  @AvailableChain.FGSA.Run.outageV_liveRoot_compatible
#print axioms audit_outageV_liveRoot_compatible

theorem audit_outageV_headInTree_compatible :
    type_of% (@AvailableChain.FGSA.Run.outageV_headInTree_compatible) :=
  @AvailableChain.FGSA.Run.outageV_headInTree_compatible
#print axioms audit_outageV_headInTree_compatible

theorem audit_outageV_head_of_filter :
    type_of% (@AvailableChain.FGSA.Run.outageV_head_of_filter) :=
  @AvailableChain.FGSA.Run.outageV_head_of_filter
#print axioms audit_outageV_head_of_filter

theorem audit_outageV_contested_head :
    type_of% (@AvailableChain.FGSA.Run.outageV_contested_head) :=
  @AvailableChain.FGSA.Run.outageV_contested_head
#print axioms audit_outageV_contested_head

theorem audit_outageV_marker_head :
    type_of% (@AvailableChain.FGSA.Run.outageV_marker_head) :=
  @AvailableChain.FGSA.Run.outageV_marker_head
#print axioms audit_outageV_marker_head

theorem audit_outageV_head_from_rows :
    type_of% (@AvailableChain.FGSA.Run.outageV_head_from_rows) :=
  @AvailableChain.FGSA.Run.outageV_head_from_rows
#print axioms audit_outageV_head_from_rows

theorem audit_outageV_head_covers_from_batch :
    type_of% (@AvailableChain.FGSA.Run.outageV_head_covers_from_batch) :=
  @AvailableChain.FGSA.Run.outageV_head_covers_from_batch
#print axioms audit_outageV_head_covers_from_batch

theorem audit_outageV_exact_carrier_receipt :
    type_of% (@AvailableChain.FGSA.Run.outageV_exact_carrier_receipt) :=
  @AvailableChain.FGSA.Run.outageV_exact_carrier_receipt
#print axioms audit_outageV_exact_carrier_receipt

theorem audit_outage_later_marker_receipt :
    type_of% (@AvailableChain.FGSA.Run.outage_later_marker_receipt) :=
  @AvailableChain.FGSA.Run.outage_later_marker_receipt
#print axioms audit_outage_later_marker_receipt

theorem audit_outageV_short_horizon :
    type_of% (@AvailableChain.FGSA.Run.outageV_short_horizon) :=
  @AvailableChain.FGSA.Run.outageV_short_horizon
#print axioms audit_outageV_short_horizon

theorem audit_outageV_gate_through_relay :
    type_of% (@AvailableChain.FGSA.Run.outageV_gate_through_relay) :=
  @AvailableChain.FGSA.Run.outageV_gate_through_relay
#print axioms audit_outageV_gate_through_relay

theorem audit_outageV_source_gate_cutoff :
    type_of% (@AvailableChain.FGSA.Run.outageV_source_gate_cutoff) :=
  @AvailableChain.FGSA.Run.outageV_source_gate_cutoff
#print axioms audit_outageV_source_gate_cutoff

theorem audit_outage_source_gate_before_early :
    type_of% (@AvailableChain.FGSA.Run.outage_source_gate_before_early) :=
  @AvailableChain.FGSA.Run.outage_source_gate_before_early
#print axioms audit_outage_source_gate_before_early

theorem audit_outage_pending_gate_cert_receipt :
    type_of% (@AvailableChain.FGSA.Run.outage_pending_gate_cert_receipt) :=
  @AvailableChain.FGSA.Run.outage_pending_gate_cert_receipt
#print axioms audit_outage_pending_gate_cert_receipt

theorem audit_outage_crossing_source_at_read :
    type_of% (@AvailableChain.FGSA.Run.outage_crossing_source_at_read) :=
  @AvailableChain.FGSA.Run.outage_crossing_source_at_read
#print axioms audit_outage_crossing_source_at_read

theorem audit_outage_uncontested_frozen_path :
    type_of% (@AvailableChain.FGSA.Run.outage_uncontested_frozen_path) :=
  @AvailableChain.FGSA.Run.outage_uncontested_frozen_path
#print axioms audit_outage_uncontested_frozen_path

theorem audit_outage_prior_good_receipts :
    type_of% (@AvailableChain.FGSA.Run.outage_prior_good_receipts) :=
  @AvailableChain.FGSA.Run.outage_prior_good_receipts
#print axioms audit_outage_prior_good_receipts

theorem audit_outageV_gate_of_receipts :
    type_of% (@AvailableChain.FGSA.Run.outageV_gate_of_receipts) :=
  @AvailableChain.FGSA.Run.outageV_gate_of_receipts
#print axioms audit_outageV_gate_of_receipts

theorem audit_outageV_gateStep_covers :
    type_of% (@AvailableChain.FGSA.Run.outageV_gateStep_covers) :=
  @AvailableChain.FGSA.Run.outageV_gateStep_covers
#print axioms audit_outageV_gateStep_covers

theorem audit_outageV_fastSet_compatible :
    type_of% (@AvailableChain.FGSA.Run.outageV_fastSet_compatible) :=
  @AvailableChain.FGSA.Run.outageV_fastSet_compatible
#print axioms audit_outageV_fastSet_compatible

theorem audit_outageV_live_locks :
    type_of% (@AvailableChain.FGSA.Run.outageV_live_locks) :=
  @AvailableChain.FGSA.Run.outageV_live_locks
#print axioms audit_outageV_live_locks

theorem audit_outageV_source_compatible :
    type_of% (@AvailableChain.FGSA.Run.outageV_source_compatible) :=
  @AvailableChain.FGSA.Run.outageV_source_compatible
#print axioms audit_outageV_source_compatible

theorem audit_outageV_result_extends :
    type_of% (@AvailableChain.FGSA.Run.outageV_result_extends) :=
  @AvailableChain.FGSA.Run.outageV_result_extends
#print axioms audit_outageV_result_extends

theorem audit_outageV_restored_gate :
    type_of% (@AvailableChain.FGSA.Run.outageV_restored_gate) :=
  @AvailableChain.FGSA.Run.outageV_restored_gate
#print axioms audit_outageV_restored_gate

theorem audit_outage_continuation_inclusive_read :
    type_of% (@AvailableChain.FGSA.Run.outage_continuation_inclusive_read) :=
  @AvailableChain.FGSA.Run.outage_continuation_inclusive_read
#print axioms audit_outage_continuation_inclusive_read

theorem audit_outage_prior_covering_source :
    type_of% (@AvailableChain.FGSA.Run.outage_prior_covering_source) :=
  @AvailableChain.FGSA.Run.outage_prior_covering_source
#print axioms audit_outage_prior_covering_source

theorem audit_outage_first_regression_retained_frame :
    type_of% (@AvailableChain.FGSA.Run.outage_first_regression_retained_frame) :=
  @AvailableChain.FGSA.Run.outage_first_regression_retained_frame
#print axioms audit_outage_first_regression_retained_frame

theorem audit_outage_contested_head_of_names :
    type_of% (@AvailableChain.FGSA.Run.outage_contested_head_of_names) :=
  @AvailableChain.FGSA.Run.outage_contested_head_of_names
#print axioms audit_outage_contested_head_of_names

theorem audit_outage_continuation_event_state :
    type_of% (@AvailableChain.FGSA.Run.outage_continuation_event_state) :=
  @AvailableChain.FGSA.Run.outage_continuation_event_state
#print axioms audit_outage_continuation_event_state

theorem audit_outage_first_regression_marker :
    type_of% (@AvailableChain.FGSA.Run.outage_first_regression_marker) :=
  @AvailableChain.FGSA.Run.outage_first_regression_marker
#print axioms audit_outage_first_regression_marker

theorem audit_outage_regression_continuation :
    type_of% (@AvailableChain.FGSA.Run.outage_regression_continuation) :=
  @AvailableChain.FGSA.Run.outage_regression_continuation
#print axioms audit_outage_regression_continuation

theorem audit_outage_marker_head_on_scoped_prefix :
    type_of% (@AvailableChain.FGSA.Run.outage_marker_head_on_scoped_prefix) :=
  @AvailableChain.FGSA.Run.outage_marker_head_on_scoped_prefix
#print axioms audit_outage_marker_head_on_scoped_prefix

theorem audit_outage_scoped_head_root :
    type_of% (@AvailableChain.FGSA.Run.outage_scoped_head_root) :=
  @AvailableChain.FGSA.Run.outage_scoped_head_root
#print axioms audit_outage_scoped_head_root

theorem audit_outage_early_scoped_head :
    type_of% (@AvailableChain.FGSA.Run.outage_early_scoped_head) :=
  @AvailableChain.FGSA.Run.outage_early_scoped_head
#print axioms audit_outage_early_scoped_head

theorem audit_outage_continuation_scoped_heads :
    type_of% (@AvailableChain.FGSA.Run.outage_continuation_scoped_heads) :=
  @AvailableChain.FGSA.Run.outage_continuation_scoped_heads
#print axioms audit_outage_continuation_scoped_heads

theorem audit_outage_good_head_through_restored :
    type_of% (@AvailableChain.FGSA.Run.outage_good_head_through_restored) :=
  @AvailableChain.FGSA.Run.outage_good_head_through_restored
#print axioms audit_outage_good_head_through_restored

theorem audit_outage_continuation_public_reads :
    type_of% (@AvailableChain.FGSA.Run.outage_continuation_public_reads) :=
  @AvailableChain.FGSA.Run.outage_continuation_public_reads
#print axioms audit_outage_continuation_public_reads

theorem audit_outage_continuation_scoped_body :
    type_of% (@AvailableChain.FGSA.Run.outage_continuation_scoped_body) :=
  @AvailableChain.FGSA.Run.outage_continuation_scoped_body
#print axioms audit_outage_continuation_scoped_body

theorem audit_outageContinuation_supplier_boundary :
    type_of% (@AvailableChain.FGSA.Run.outage_continuation_scoped_body) :=
  @AvailableChain.FGSA.Run.outage_continuation_scoped_body
#print axioms audit_outageContinuation_supplier_boundary

theorem audit_outageContinuation_of_body :
    type_of% (@AvailableChain.FGSA.Run.outageContinuation_of_body) :=
  @AvailableChain.FGSA.Run.outageContinuation_of_body
#print axioms audit_outageContinuation_of_body

theorem audit_outageContinuation_claim_of :
    type_of% (@AvailableChain.FGSA.Run.outage_continuation_scoped_body) :=
  @AvailableChain.FGSA.Run.outage_continuation_scoped_body
#print axioms audit_outageContinuation_claim_of

end AvailableChain.FGSA.Run.Tests.OutageContinuationAxioms
end
