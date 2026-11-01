#!/usr/bin/env bash
# FGSA run-library checks (plan docs/plans/2026-09-29-fgsa-composition-t7-t1.md
# §3.1, T7.1), adapted from scripts/check-fgsa.sh: build (--wfail), root
# imports, native evaluation outside comments, the direct-import allowlist with
# its layer rules, the v1/v2 name-clash rule (no plain `open AvailableChain.V2`),
# the axiom check (with build coverage, the compiled allowlist, the
# import-closure check and the used-constant check), the lease-instance check,
# and the negative controls of these checks.
# The store check forbids the run and interface names (its Q1/Q5 boundary);
# this library is the run layer, so it has no such grep. It keeps the G13
# fixes of the store check: import headers are parsed after comment removal,
# the parser fails closed, the axiom script checks the allowlist again on the
# compiled import data, and source files come from `find -L` with
# `-iname '*.lean'` (symbolic links followed, extension in any case).
# Run: bash scripts/check-fgsa-run.sh. Exit 0 when every check passes.
# JOBS bounds this script's pool (default Mac 3, Linux 6; env wins).
# GATE_SLOTS caps shared controls and heavy steps (Mac 3, Linux 4; env wins).
# JOBS alone does not set machine concurrency.
# --no-negative or NEG=0 keeps all positive checks without negative controls.
# SOURCE_ONLY=1 runs the static checks and exits before compiled checks or controls.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
source scripts/import-policy.sh
if [ "${SOURCE_ONLY:-0}" != 1 ]; then
  gate_options "$@"
  for f in scripts/CheckFGSARunAxioms.lean scripts/CheckFGSARunLease.lean \
      scripts/AvailableChainCheckSupport/GeneratedOwner.lean \
      scripts/fgsa-controls/AdvG.lean scripts/fgsa-controls/AdvLib.lean; do
    [ -f "$f" ] || { echo "MISSING CHECK SCRIPT: $f"; exit 2; }
  done
fi
# The declarations that the axiom script must find and check (fail closed: a
# scan that misses the library fails). Each task adds its main outputs.
AX_OPTS=(--expect
  AvailableChain.FGSA.Run.fgsaTimelyClock_clock
  AvailableChain.FGSA.Run.fgsa_awake_before_noRestart
  AvailableChain.FGSA.Run.fgsa_historySafeAt_noRestart
  AvailableChain.FGSA.Run.fgsa_processed_by_deadline_ready
  AvailableChain.FGSA.Run.fgsa_accepted_by_deadline_of_parentStored
  AvailableChain.FGSA.Run.fgsa_replay_vote_stamp_time
  AvailableChain.FGSA.Run.fgsa_vote_stamp_source_or_restart
  AvailableChain.FGSA.Run.fgsa_block_stamp_source_or_restart
  AvailableChain.FGSA.Run.fgsa_block_accepted_origin
  AvailableChain.FGSA.Run.fgsa_vote_stamp_source
  AvailableChain.FGSA.Run.fgsa_block_stamp_source
  AvailableChain.FGSA.Run.fgsa_replayed_head_delivery_origin
  AvailableChain.FGSA.Run.fgsa_emitted_head_no_prior_processed
  AvailableChain.FGSA.Run.fgsa_emitted_proposal_no_prior_processed

  AvailableChain.FGSA.Run.fgsa_fgAction_unjoined_source_none
  AvailableChain.FGSA.Run.fgsa_clock_restartTime
  AvailableChain.FGSA.Run.fgsa_process_restartTime
  AvailableChain.FGSA.Run.fgsa_restartTime_bound
  AvailableChain.FGSA.Run.fgsa_joinedNow_of_joinedEnv
  AvailableChain.FGSA.Run.fgsa_joinedNow_of_caughtUp
  AvailableChain.FGSA.Run.fgsa_joinedNow_of_awakeClosed
  AvailableChain.FGSA.Run.fgsa_emitted_row_no_prior_processed
  AvailableChain.FGSA.ancestorDeadlines_acRestart
  AvailableChain.FGSA.Spec.spec_prune_restart_mem
  AvailableChain.FGSA.Spec.spec_prune_sleep
  # ROOT-DIGEST-2 W2 producers.
  AvailableChain.FGSA.Run.process_namedBodies_subset
  AvailableChain.FGSA.Run.stored_block_eq_of_root_eq
  AvailableChain.FGSA.Run.headTargetAtEmission_stored
  AvailableChain.FGSA.Run.headTargetAtEmission_scope
  AvailableChain.FGSA.Run.resolvedHead_root
  AvailableChain.FGSA.Run.headTargetAtEmission_receiver_eq
  AvailableChain.FGSA.Run.headTargetAtEmission_at_tick
  AvailableChain.FGSA.Run.headTargetAtEmission_of_stored
  AvailableChain.FGSA.Run.stored_eq_headVote
  AvailableChain.FGSA.Run.namedScope_stored_proposal
  AvailableChain.FGSA.Run.stored_named_body_delivery
  AvailableChain.FGSA.Run.stored_named_body_ancestor
  AvailableChain.FGSA.Run.namedProposalInRun_genesis_or_delivered
  AvailableChain.FGSA.Run.namedProposalInRun_origin
  AvailableChain.FGSA.Run.namedStored_eq
  AvailableChain.FGSA.RootLease.root_write_unique_keys
  AvailableChain.FGSA.RootLease.root_write_protectsUntil
  AvailableChain.FGSA.RootLease.root_expire_protectsUntil
  AvailableChain.FGSA.RootLease.root_release_protectsUntil
  AvailableChain.FGSA.Run.findByRoot_subtree
  AvailableChain.FGSA.Run.goldfishScoreOn_subtree
  AvailableChain.FGSA.Run.clockPre_headDomain
  AvailableChain.FGSA.Run.actView_score
  AvailableChain.FGSA.Run.actView_resolve_of_mem
  AvailableChain.FGSA.Run.resolvedTarget_root
  AvailableChain.FGSA.Run.resolvedTarget_of_mem
  AvailableChain.FGSA.Run.base_resolve_target
  AvailableChain.FGSA.Run.actView_resolve_target
  AvailableChain.FGSA.Run.clock_stored_block_eq
  AvailableChain.FGSA.Run.prefixSupport_body
  AvailableChain.FGSA.Run.confirmation_support_body
  AvailableChain.FGSA.Run.resolvedHead_target
  AvailableChain.FGSA.Run.resolvedHead_of_lookup
  AvailableChain.FGSA.Run.cleanSupport_domain_score
  AvailableChain.FGSA.Run.actView_target_of_resolvedHead
  AvailableChain.FGSA.Run.resolvedTarget_mem
  AvailableChain.FGSA.Run.actView_support_in_domain
  # ROOT-DIGEST-2: signed W1 named-scope public names.
  AvailableChain.FGSA.Run.DirectNamedProposalInRun
  AvailableChain.FGSA.Run.HeadTargetAtEmission
  AvailableChain.FGSA.Run.NamedProposalInRun
  AvailableChain.FGSA.Run.contentAgree_of_namedScope
  AvailableChain.FGSA.Run.emitted_payload_parent_base_stored
  AvailableChain.FGSA.Run.headTargetAtEmission_exists
  AvailableChain.FGSA.Run.headTargetAtEmission_unique
  AvailableChain.FGSA.Run.namedAncestor_eq
  AvailableChain.FGSA.Run.namedOrigin_reachable
  AvailableChain.FGSA.Run.namedProposal_eq
  AvailableChain.FGSA.Run.namedScope_ancestor
  AvailableChain.FGSA.Run.namedScope_collision
  AvailableChain.FGSA.Run.namedScope_compatible_iff
  AvailableChain.FGSA.Run.namedScope_delivered
  AvailableChain.FGSA.Run.namedScope_erase_injective
  AvailableChain.FGSA.Run.namedScope_held
  AvailableChain.FGSA.Run.namedScope_preceq_iff
  AvailableChain.FGSA.Run.proposal_trigger_in_root_scope
  # ROOT-DIGEST W3b: contract and origin producer inventory.
  AvailableChain.FGSA.Run.contentOk_withApp
  AvailableChain.FGSA.Run.emitted_payload_parent_stored
  AvailableChain.FGSA.Run.emitted_proposal_parent_stored
  AvailableChain.FGSA.Run.emitted_proposal_slot_root
  AvailableChain.FGSA.Run.proposal_handle_in_scope
  AvailableChain.FGSA.Run.proposal_handlesS_direct
  AvailableChain.FGSA.Run.proposal_trigger_in_scope
  AvailableChain.FGSA.Run.rootBlockInRun_ancestor
  AvailableChain.FGSA.Run.rootBlockInRun_delivered
  AvailableChain.FGSA.Run.rootBlockInRun_eq
  AvailableChain.FGSA.Run.rootBlockInRun_genesis_or_delivered
  AvailableChain.FGSA.Run.rootBlockInRun_held
  AvailableChain.FGSA.Run.rootBlockInRun_origin
  AvailableChain.FGSA.Run.rootBlockInRun_stored
  AvailableChain.FGSA.Run.rootBlockInRun_stored_proposal
  AvailableChain.FGSA.Run.rootInjectiveOn_run
  AvailableChain.FGSA.Run.rowsOk_withApp_proposalBlock
  AvailableChain.FGSA.Run.storeStepRoots_run
  AvailableChain.FGSA.Run.stored_body_ancestor
  AvailableChain.FGSA.Run.stored_body_delivery
  AvailableChain.FGSA.Run.stored_content_eq
  AvailableChain.FGSA.Run.stored_fg_body_delivery
  AvailableChain.FGSA.Run.withApp_zero_proposalBlock
  AvailableChain.FGSA.Run.DirectRootBlockInRun
  AvailableChain.FGSA.Run.RootBlockInRun
  AvailableChain.FGSA.Run.NamedRootCollisionFree
  AvailableChain.FGSA.Run.NamedRootCollisionFree.mk
  AvailableChain.FGSA.Run.NamedRootCollisionFree.root_injective
  Run.stored_rows_r3W Run.stored_chain_rowsValidW Run.exact_row_exclusion_checkedW Run.exact_row_exclusionW
  Run.isRowObject Run.isRowObject_def Run.fgsaDelay Run.fgsaDelay_def
  Run.fgsaDelay_row Run.fgsaDelay_nonrow Run.fgsaDelay_self Run.EmissionRowsValid Run.decode Run.HonestEmissionWellFormed
  Run.HonestProposalDecodes Run.fgsa_emissionRowsValid Run.fgsa_propose_parent_lt
  Run.honest_emit_wellFormed Run.decode_honest Run.fgsa Run.fgsaFamilies Run.fgsaIso Run.toWireEquiv Run.duties_spec
  Run.ReceiptCoveragePremises Run.ReceiptCoverageSleepPremises
  Run.ReceiptCoverageSleepStatement Run.ReceiptCoverageSleepStatement_def
  Run.fgsa_receiptCoverage_ready
  Run.duties_nodup Run.withApp_zero Run.rowsOk_withApp Run.recordOwn_attest
  Run.attest_signer_irrel Run.ofRow_injective Run.ofHead_injective Run.ofRow_auth
  Run.processedS_ofRow Run.excludesS_ofRow Run.handlesS_ofRow_iff Run.excludesS_inert
  Run.excludes_inert Run.excludes_inert_epoch Run.excludesFixed_inert_epoch
  Run.epoch_of_restartFree Run.excludes_stable_epoch Run.excludesFixed_stable_epoch
  Run.restore_st Run.restore_rec Run.clock_rec Run.process_rec Run.recordOwn_st
  Run.process_base_now Run.clock_vn Run.process_votes_subset Run.excludesS_process
  Run.fgsa_dutiesInjectiveAt Run.fgsa_emitOnceUnder
  Run.fgsa_head_singleDuty Run.fgsa_prop_singleDuty Run.invalidForParent_mono
  Run.invalidForParent_clock Run.admitBlock_of_invalidForParent Run.invalidForParent_no_carried
  Run.propose_rowsValid Run.fgsa_accepted_rowsValid Run.fgsa_trigger_rowsValid
  Run.fgsa_trigger_invalid_false Run.Epoch.weaken Run.decode_eq_vote
  Run.decode_eq_block Run.rowWire_decode
  Run.fgsaInterface Run.fgsaOutputs Run.finalizedOut Run.proposalTime_fgsa
  Run.propLabel_injective Run.fgsaClock Run.fgsa_monoAlong_preceq_F
  Run.fgsa_hrestore_retained Run.fgsa_hrestore_field_retained
  Run.fgsaRestoreTimeLaw Run.fgsa_restore_now Run.fgsa_restore_restartTime
  Run.fgsa_restore_record Run.fgsa_restore_fg Run.fgsa_restore_rowPool
  Run.fgsa_restore_proposals Run.fgsa_restore_namedBodies Run.fgsa_restore_blocks
  Run.fgsa_restore_obligations Run.fgsa_restore_stableRecord
  Run.fgsa_restore_reachable Run.fgsa_reachable_stateBefore
  Run.SleepTests.p Run.SleepTests.P Run.SleepTests.proposal Run.SleepTests.row
  Run.SleepTests.head Run.SleepTests.env Run.SleepTests.run
  Run.SleepTests.joinEnv Run.SleepTests.joinRun Run.SleepTests.valid
  Run.SleepTests.non_public_wake Run.SleepTests.receipt_before_tick
  Run.SleepTests.durable_run Run.SleepTests.retained_not_fresh Run.SleepTests.join_valid
  Run.SleepContinuationTests.retained_origin
  Run.SleepContinuationTests.joined_strict
  Run.SleepContinuationTests.same_time_bound
  Run.SleepContinuationTests.retained_block_bound
  Run.SleepContinuationTests.wake_epoch_equiv
  Run.SleepContinuationTests.gate_empty
  Run.SleepContinuationTests.admission_public
  Run.SleepTests.join_duties Run.SleepTests.wake_at_tick Run.SleepTests.initial_duties
  Run.reachable_stateBefore Run.reachable_stateBeforeTime Run.reachable_readAt
  Run.reachable_final Run.reachable_postClock Run.reachable_postTick
  Run.storeBundle_stateBefore Run.storeBundle_stateBeforeTime Run.storeBundle_readAt
  Run.storeBundle_final Run.storeBundle_postClock Run.storeBundle_postTick
  Run.inv0_stateBefore Run.cstoreInv_stateBefore Run.metaInv_stateBefore
  Run.nestOK_stateBefore Run.outputNesting_run Run.leaseBelowOutput_stateBefore
  Run.leaseBelowOutput_honest Run.stored_proposal_delivered
  Run.fgsa_clock_now Run.fgsaHooks Run.handles_wellFormed Run.fgsaAdmissionTime
  Run.fgsaTimely Run.fgsaAcceptanceInv Run.fgsaTrigger Run.fgsa_slot_threshold_iff
  Run.fgsa_round_threshold_iff Run.fgsaTimelyClock Run.fgsaAcceptance Run.fgsaAdmitSound
  Run.fgsaTimelyClock_clockOf Run.fgsaTimelyClock_actTime Run.fgsaTrigger_def Run.fgsa_trigger_of_emit
  Run.fgsa_trigger_of_accept Run.Tests.fgsa_carried_row_cap_control
  Run.ownRecord_fold_run Run.fgsa_emits_head Run.fgsa_emits_row
  Run.fgsa_emitsAt_row Run.fgsa_emits_proposal Run.fgsa_tick_asleep
  Run.fgsa_attest_decode Run.fgsa_carried_row Run.EmitsRow
  Run.EmittedRowsNoSlash Run.decodeRowObject Run.fgClientEvent
  Run.fgClientEvents Run.fgsa_tick_rows_of_seats Run.fgsa_client_trace_of_seats
  Run.fgsa_linked_seats Run.fgsa_ownSeats_bijSeat Run.fgsa_decode_attest_object
  Run.fgsa_client_trace Run.emittedRowsNoSlash
  Run.fgsa_tick_time_strict
  Run.fgsa_tick_unique
  Run.fgsa_tick_total
  Run.fgsa_tick_before_delivery
  Run.fgsa_postClock_slot
  Run.fgsa_proposal_slot
  Run.fgsa_vote_slot
  Run.fgsa_action_slot_round
  Run.fgsa_gate_slot
  Run.fgsa_saved_label_origin
  Run.fgsa_gate_fresh
  Run.fgsa_gate_clock_bridge
  Run.fgsa_stateBefore_bounds
  Run.fgsa_preTick_now_le
  Run.fgsa_preTick_restartTime_at_wake
  Run.fgsa_preTick_now_lt_joined
  Run.fgsa_preTick_now_lt_iff
  Run.fgsa_preTick_votes_stamped_le
  Run.fgsa_gate_saved_unjoined
  Run.timely_of_relay_retained
  Run.fgsa_admissionTime_public
  Run.fgsa_preTick_now_lt
  Run.fgsa_release_votes_stamped
  Run.fgsa_vote_stamp_keys
  Run.fgsa_release_clockPre
  Run.fgsa_release_input_votes_stamped
  Run.fgsa_stored_block_slots
  Run.fgsa_release_count_bridge
  Run.fgsa_action_gate_time
  Run.fgsa_action_reads_gate
  Run.fgsa_gate_saved_result
  Run.fgsa_stored_block_origin
  Run.fgsa_preTick_eq_timeRead
  Run.fgsaAC Run.fgsa_clockPre_gateView Run.fgsaAC_anchor_le_output
  Run.fgsaAC_lease_le_output Run.fgsaAC_gate_write
  Run.fgsaAC_output_step Run.fgsaAC_laws
  Run.fgsaAC_slot_gate_reads
  Run.depsS_of_not_block Run.depsS_of_not_proposal Run.fgsa_hWF_of_delivery
  Run.fgsa_hReady_of_not_block Run.fgsa_hReady_of_parentStored
  Run.fgsa_accepted_by_deadline_of_parentStored
  Run.Tests.DigestScope.body_collision_admitted Run.Tests.DigestScope.body_collision_control
  Run.Tests.DigestScope.head_direct_scope Run.Tests.DigestScope.head_body_scope
  Run.Tests.DigestScope.head_scope_control Run.Tests.NVDigest.proposal_slot_root
  Run.Tests.NVDigest.same_slot_collision Run.Tests.NVDigest.live_horizon_grid
  # ROOT-DIGEST: public fixture inventory.
  AvailableChain.FGSA.Run.Tests.DigestScope.ba
  AvailableChain.FGSA.Run.Tests.DigestScope.collisionA
  AvailableChain.FGSA.Run.Tests.DigestScope.collisionB
  AvailableChain.FGSA.Run.Tests.DigestScope.collisionParams
  AvailableChain.FGSA.Run.Tests.DigestScope.collisionRun
  AvailableChain.FGSA.Run.Tests.DigestScope.collisionWireA
  AvailableChain.FGSA.Run.Tests.DigestScope.collisionWireB
  AvailableChain.FGSA.Run.Tests.DigestScope.env
  AvailableChain.FGSA.Run.Tests.DigestScope.fakeHead
  AvailableChain.FGSA.Run.Tests.DigestScope.fakeHeadBody
  AvailableChain.FGSA.Run.Tests.DigestScope.headProposal
  AvailableChain.FGSA.Run.Tests.DigestScope.headRun
  AvailableChain.FGSA.Run.Tests.DigestScope.headWire
  AvailableChain.FGSA.Run.Tests.DigestScope.pT
  AvailableChain.FGSA.Run.Tests.DigestScope.traceRun
  AvailableChain.FGSA.Run.Tests.NVDigest.live_horizon_grid
  AvailableChain.FGSA.Run.Tests.NVDigest.nvDigest
  # WP12b/c spec construction helpers (AvailableChainFGSARun/Proofs/Spec, moved by w12d).
  AvailableChain.FGSA.Spec.spec_assigned_check_iff
  AvailableChain.FGSA.Spec.spec_assigned_parent_membership
  AvailableChain.FGSA.Spec.spec_assigned_proposal_emission
  AvailableChain.FGSA.Spec.spec_block_identity_step
  AvailableChain.FGSA.Spec.spec_discarded_event_step
  AvailableChain.FGSA.Spec.spec_duplicate_delivery_stutter
  AvailableChain.FGSA.Spec.spec_identity_gate_assigned
  AvailableChain.FGSA.Spec.spec_identity_gate_refused
  AvailableChain.FGSA.Spec.spec_identity_refusal_step
  AvailableChain.FGSA.Spec.spec_identity_store_induction
  AvailableChain.FGSA.Spec.spec_mapped_delivery_wire
  AvailableChain.FGSA.Spec.spec_missing_dependency_stutter
  AvailableChain.FGSA.Spec.spec_no_full_row_target_reader
  AvailableChain.FGSA.Spec.spec_parent_identity_filtered
  AvailableChain.FGSA.Spec.spec_parent_identity_root
  AvailableChain.FGSA.Spec.spec_prune_append
  AvailableChain.FGSA.Spec.spec_prune_delivery_conditions
  AvailableChain.FGSA.Spec.spec_prune_delivery_valid
  AvailableChain.FGSA.Spec.spec_prune_emits
  AvailableChain.FGSA.Spec.spec_prune_execution_valid
  AvailableChain.FGSA.Spec.spec_prune_final
  AvailableChain.FGSA.Spec.spec_prune_matched_cut
  AvailableChain.FGSA.Spec.spec_prune_no_restart
  AvailableChain.FGSA.Spec.spec_prune_observation
  AvailableChain.FGSA.Spec.spec_prune_schedule
  AvailableChain.FGSA.Spec.spec_prune_signatures
  AvailableChain.FGSA.Spec.spec_prune_sublist
  AvailableChain.FGSA.Spec.spec_prune_tick_cut
  AvailableChain.FGSA.Spec.spec_prune_tick_mem
  AvailableChain.FGSA.Spec.spec_ready_wire_step
  AvailableChain.FGSA.Spec.spec_ready_wire_valid
  AvailableChain.FGSA.Spec.spec_restart_retained_block_trace
  AvailableChain.FGSA.Spec.spec_restart_delivery_cases
  AvailableChain.FGSA.Spec.spec_restart_delivery_valid
  AvailableChain.FGSA.Spec.spec_restart_execution_valid
  AvailableChain.FGSA.Spec.spec_restart_matched_cut_agreement
  AvailableChain.FGSA.Spec.spec_restart_no_public_tick
  AvailableChain.FGSA.Spec.spec_restart_outside_no_restart
  AvailableChain.FGSA.Spec.spec_restart_schedule
  AvailableChain.FGSA.Spec.spec_restart_self_delivery
  AvailableChain.FGSA.Spec.spec_restart_signatures
  AvailableChain.FGSA.Spec.spec_revised_target_execution
  AvailableChain.FGSA.Spec.spec_row_finality_root_match
  AvailableChain.FGSA.Spec.spec_row_height_root_match
  AvailableChain.FGSA.Spec.spec_row_target_identity_trace
  AvailableChain.FGSA.Spec.spec_simulation_event_key
  AvailableChain.FGSA.Spec.spec_simulation_event_stutter
  AvailableChain.FGSA.Spec.spec_simulation_proposal_retained
  AvailableChain.FGSA.Spec.spec_simulation_wire_stutter
  AvailableChain.FGSA.Spec.spec_simulation_wire_valid
  AvailableChain.FGSA.Spec.spec_stutter_event_list
)
# Keep the explicit sleep expectations and check all current public declarations.
if [ "${SOURCE_ONLY:-0}" != 1 ]; then
  gate_inventory_args scripts/fgsa-run-expected.txt
  AX_OPTS+=("${GATE_INVENTORY[@]}")
fi
python3 -B scripts/current-inventory.py fgsa-run scripts/fgsa-run-expected.txt

# T7.11 content agreement.
AX_OPTS+=(Run.contentAgree_run)

# T7.8 public receipt and stamp declarations.
AX_OPTS+=(Run.excludesS_honestRow_false)
AX_OPTS+=(
  Run.blockOf?
  Run.fgsa_clockOf_nonneg
  Run.processed_stable
  Run.rowPool_provenance
  Run.fgsa_vote_stamp_source
  Run.fgsa_vote_accepted_before
  Run.fgsa_block_stamp_source
  Run.fgsa_block_accepted_before
  Run.fgsa_head_excluded_before
  Run.fgsa_head_receipt
  Run.fgsa_head_cap_sources
  Run.fgsa_proposal_receipt
  Run.fgsa_honest_head_receipt
)

# Remove comments (the tokenizer of scripts/check-fgsa.sh): strings, character
# literals, raw strings (r"...", r#"..."#) and nested block comments. A "--"
# in a string does not start a comment, and a "/-" in a line comment does not
# open a block comment.
strip_comments='
  local $/; my $s = <STDIN>; my $o = ""; my $d = 0;
  while ((pos($s) // 0) < length $s) {
    if ($d > 0) {
      if    ($s =~ /\G\/-/gc)   { $d++ }
      elsif ($s =~ /\G-\//gc)   { $d--; $o .= " " }
      elsif ($s =~ /\G(\n)/gc)  { $o .= $1 }
      else                      { $s =~ /\G./gcs }
    }
    elsif ($s =~ /\G--[^\n]*/gc)                         { }
    elsif ($s =~ /\G\/-/gc)                              { $d = 1 }
    elsif ($s =~ /\Gr(#*)".*?"\1/gcs)                    { $o .= "\"\"" }
    elsif ($s =~ /\G"(?:\\.|[^"\\])*"/gcs)               { $o .= "\"\"" }
    elsif ($s =~ /\G([\w\p{N}.!?][\w\p{N}.!?\x27]*)/gc)  { $o .= $1 }
    elsif ($s =~ /\G\x27(?:\\.|[^\\\x27])\x27/gc)        { $o .= "c" }
    else                                                 { $s =~ /\G(.)/gcs; $o .= $1 }
  }
  print $o;'
# The modules of the import header of a file, one per line, after comment
# removal: [module] then [public] [meta] import [all] <Name>, any whitespace.
# Fail closed: if the rest of the file still has the token `import` or
# `prelude`, it prints the line `!UNPARSED`.
header_imports='
  local $/; my $s = <STDIN>;
  $s =~ s/^\s+//; $s =~ s/^module\s+//;
  while ($s =~ s/^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_.]*)\s*//) {
    print "$1\n";
  }
  print "!UNPARSED\n" if $s =~ /(?<![\w.\x27!?])(?:import|prelude)(?![\w\x27!?])/;'
imports_of() { perl -CSD -e "$strip_comments" < "$1" | perl -CSD -e "$header_imports"; }
# The library source files under base directory $1, relative to it.
source_files() { gate_source_files "$1" AvailableChainFGSARun; }

# The Tests/ modules under base directory $1 (the library glob builds them;
# the root does not import them, BUILD B7-TESTS).
test_modules() {
  source_files "$1" | grep -i '^AvailableChainFGSARun/Tests/' |
    sed -E 's/\.[lL][eE][aA][nN]$//; s|/|.|g' || true
}
# Root imports under base directory $1: every source file outside Tests/ is a
# root import, and the root imports no Tests/ module.
check_root_imports() {
  local base=$1 missing tests
  missing=$(comm -23 \
    <(source_files "$base" | grep -iv '^AvailableChainFGSARun/Tests/' |
        sed -E 's/\.[lL][eE][aA][nN]$//; s|/|.|g' | sort) \
    <(imports_of "$base/$(gate_source_file "$base" AvailableChainFGSARun.lean)" | sort))
  [ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; return 1; }
  tests=$(imports_of "$base/$(gate_source_file "$base" AvailableChainFGSARun.lean)" |
    grep '^AvailableChainFGSARun\.Tests\.' || true)
  [ -z "$tests" ] || { echo "ROOT IMPORTS A TEST MODULE: $tests"; return 1; }
  if imports_of "$base/$(gate_source_file "$base" AvailableChainFGSARun.lean)" |
      grep -qx '!UNPARSED'; then
    echo "UNPARSED IMPORT HEADER: AvailableChainFGSARun.lean"; return 1
  fi
}

# The direct-import allowlist (plan §3.1, "Imports, with layers") under base
# directory $1. Internal imports follow the layers: Model/ imports Model/;
# Statements/ imports Model/ and Statements/; Proofs/ imports Model/,
# Statements/ and Proofs/; Tests/ and the root import any library module. The
# root imports only library modules. External, all layers:
# AvailableChainEngineV2.*, AvailableChainFGSA.Model.*,
# AvailableChainFGSA.Statements.*, AvailableChainModel.Objects.{Identifiers,
# Time, Blocks, Codec}, AvailableChainModel.Generic.Env, AvailableChainSimplexFG.*,
# AvailableChainGridCO.Model.{Protocol, Walk}, AvailableChainSA.Model.Protocol,
# Mathlib.*, AvailableChainGeneric.Statements.*. Proofs/ and Tests/ also:
# AvailableChainGeneric.Proofs.*, AvailableChainKitV2.*,
# AvailableChainFGSA.Proofs.*, AvailableChainKitFG.*. Tests/ also:
# AvailableChainFGSA.Tests.Support. Everything else is refused, in particular
# the v1 engine (AvailableChainModel.Generic.Run), AvailableChainStatements.*,
# AvailableChainKit.*, AvailableChainGridCO.Proofs.*, AvailableChainFramework.*,
# AvailableChainRegistry.*, AvailableChainSAPC.*, AvailableChainLStar.*.
check_direct_imports() {
  local base=$1 bad=0 f rel layer m
  for f in $(source_files "$base") AvailableChainFGSARun.lean; do
    rel=${f#AvailableChainFGSARun/}
    if [ "$f" = AvailableChainFGSARun.lean ]; then layer=root; else layer=${rel%%/*}; fi
    for m in $(imports_of "$base/$(gate_source_file "$base" "$f")"); do
      if [ "$m" = '!UNPARSED' ]; then echo "UNPARSED IMPORT HEADER: $f"; bad=1; continue; fi
      run_import_allowed "$layer" "$m" && continue
      echo "IMPORT NOT ALLOWED: $f imports $m"; bad=1
    done
  done
  return $bad
}

# The v1/v2 name clash (plan §3.1, TR9): v1 `Auth` and `Signed` (namespace
# `AvailableChain`) and v2 `Auth` and `Signed` (namespace `AvailableChain.V2`)
# clash. On comment-free text, an `open` or `export` of a namespace whose last
# component is `V2` (`AvailableChain.V2`, or `V2` inside `AvailableChain`) must
# be selective, `open AvailableChain.V2 (…)`, with one namespace, and the list
# names neither `Auth` nor `Signed`. A plain, `hiding` or `renaming` form is
# refused. A `namespace` with a component `V2` is refused (it opens
# `AvailableChain.V2`). An `open` command runs to the next line that starts in
# column 0; an `open` with no namespace on that text is refused (fail closed).
v2_open='
  local $/; my $s = <STDIN>;
  my %kw = map { $_ => 1 } qw(theorem lemma def abbrev structure inductive class
    instance namespace section end variable open export example noncomputable
    private protected public attribute set_option universe mutual axiom opaque
    macro syntax notation elab local where);
  my $comps = sub { my $n = shift; $n =~ s/[«»]//g; split /\./, $n };
  while ($s =~ /(?<![\w.\x27!?])(open|export|namespace)(?![\w.\x27!?])/g) {
    my ($cmd, $pos) = ($1, pos($s));
    my ($txt) = substr($s, $pos) =~ /\A(.*?)(?=\n\S|\z)/s;
    if ($cmd eq "namespace") {
      my ($n) = $txt =~ /\A\s*(\S+)/;
      print "V2 NAMESPACE: namespace $n\n" if defined $n && grep { $_ eq "V2" } $comps->($n);
      next;
    }
    my @toks = $txt =~ /(\([^)]*\)|[^\s()]+)/g;
    my (@names, $sel, $mode);
    for my $t (@toks) {
      if ($t =~ /^\(/) { $sel = $t; last }
      if ($t eq "hiding" || $t eq "renaming") { $mode = $t; last }
      last if $t eq "in" || $kw{$t};
      next if $t eq "scoped";
      push @names, $t;
    }
    if (!@names) { print "UNPARSED OPEN: $cmd$txt\n"; next }
    for my $n (@names) {
      my @c = $comps->($n);
      next unless $c[-1] eq "V2";
      if (defined $sel && @names == 1 && !defined $mode) {
        print "V2 OPEN LISTS $1: $cmd $n $sel\n"
          if $sel =~ /(?<![\w.\x27!?])(Auth|Signed)(?![\w.\x27!?])/;
      } else {
        print "PLAIN V2 OPEN: $cmd @names" . (defined $mode ? " $mode" : "") . "\n";
      }
    }
  }'
check_v2_open() {
  local base=$1 bad=0 f out
  for f in $(source_files "$base") AvailableChainFGSARun.lean; do
    out=$(perl -CSD -e "$strip_comments" < "$base/$(gate_source_file "$base" "$f")" |
      perl -CSD -e "$v2_open")
    if [ -n "$out" ]; then printf '%s\n' "$out"; echo "V2 NAME CLASH in $f"; bad=1; fi
  done
  return $bad
}

if [ "${SOURCE_ONLY:-0}" != 1 ]; then
  echo "== lake build --wfail AvailableChainFGSARun"
  gate_build --wfail AvailableChainFGSARun
  # The check support library (the owner map of generated constants) is not a
  # default target: build it here, so that a clean checkout works.
  echo "== lake build --wfail AvailableChainCheckSupport"
  gate_build --wfail AvailableChainCheckSupport
fi
echo "== root imports"
check_root_imports . || exit 2
echo "== native evaluation"
status=0
for f in $(source_files .) AvailableChainFGSARun.lean; do
  if perl -CSD -e "$strip_comments" < "$(gate_source_file . "$f")" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native := true|ofReduceBool|ofReduceNat' >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
[ $status -eq 0 ] || exit 1
echo "== direct imports"
check_direct_imports . || exit 1
echo "== v1/v2 name clash (open AvailableChain.V2)"
check_v2_open . || exit 1
if [ "${SOURCE_ONLY:-0}" = 1 ]; then
  echo "FGSA Run source checks: PASS"
  exit 0
fi
echo "== axioms, build coverage, import closure, used constants"
# The Tests/ modules are not in the root closure: check them as extra roots.
TEST_MODS=($(test_modules .))
TEST_ROOTS=()
for m in "${TEST_MODS[@]}"; do TEST_ROOTS+=(--root "$m"); done
gate_with_slot python3 -B scripts/write-check-inventories.py --scope fgsa-run --check
gate_with_slot lake env lean --run scripts/CheckFGSARunAxioms.lean "${TEST_ROOTS[@]}" "${AX_OPTS[@]}"
echo "== lease instances"
gate_with_slot lake env lean --run scripts/CheckFGSARunLease.lean "${TEST_MODS[@]}"

neg=$(mktemp -d "$PWD/.lake/fgsa-run-neg.XXXXXX")
trap 'rm -rf "$neg"' EXIT

# Keep each fixture private; only completed logs go to stdout.
gate_pool_init "$neg/controls"
if [ "$NEG" = 1 ]; then echo "== negative controls"
else echo "negative controls: SKIPPED (NEG=0)"; fi
# expect_fail NAME CODE OUT PATTERN...: the check failed with CODE and printed
# every PATTERN (fixed strings).
expect_fail() {
  local name=$1 code=$2 out=$3 p; shift 3
  gate_control_check "$name" "$code" "$out" || exit 1
  if [ "$code" -eq 0 ]; then echo "$out"; echo "NEGATIVE CONTROL NOT DETECTED: $name"; exit 1; fi
  for p in "$@"; do
    if [[ $out != *"$p"* ]]; then
      echo "$out"; echo "NEGATIVE CONTROL $name: missing \"$p\""; exit 1
    fi
  done
  echo "rejected, as expected: $name"
}
# A scratch copy of the source tree for the text controls.
mk_tree() {
  mkdir -p "$neg/tree"
  cp -R "$(gate_source_dir AvailableChainFGSARun)" \
    "$(gate_source_path AvailableChainFGSARun)" "$neg/tree/"
  printf '[[lean_lib]]\nname = "AvailableChainFGSARun"\nglobs = ["AvailableChainFGSARun.*"]\n' \
    > "$neg/tree/lakefile.toml"
  mkdir -p "$neg/tree/AvailableChainFGSARun/"{Model,Statements,Proofs,Tests}
}
run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }
# lean_c OUT SRC: compile SRC to the .olean OUT, with $neg on the search path.
lean_c() { lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$1" "$2"' "$neg" "$1" "$2"; }

control_unlisted() {
mk_tree
printf 'module\npublic import AvailableChainLStar.Model.Protocol\n' > "$neg/tree/AvailableChainFGSARun/Model/NegA.lean"
echo 'public import AvailableChainFGSARun.Model.NegA' >> "$neg/tree/AvailableChainFGSARun.lean"
run check_direct_imports "$neg/tree"
expect_fail "unlisted library" $code "$out" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Model/NegA.lean imports AvailableChainLStar.Model.Protocol"
}

control_layer() {
mk_tree
printf 'module\npublic import AvailableChainKitV2.ClockLaws\npublic import AvailableChainFGSA.Proofs.StoreInv\n' \
  > "$neg/tree/AvailableChainFGSARun/Model/NegB.lean"
printf 'module\npublic import AvailableChainFGSARun.Proofs.X\npublic import AvailableChainKitFG.Correspondence\n' \
  > "$neg/tree/AvailableChainFGSARun/Statements/NegB.lean"
printf 'module\npublic import AvailableChainFGSA.Tests.Support\n' > "$neg/tree/AvailableChainFGSARun/Proofs/NegB.lean"
printf 'module\npublic import AvailableChainFGSA.Tests.Smoke\n' > "$neg/tree/AvailableChainFGSARun/Tests/NegB.lean"
run check_direct_imports "$neg/tree"
expect_fail "wrong-layer import" $code "$out" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Model/NegB.lean imports AvailableChainKitV2.ClockLaws" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Model/NegB.lean imports AvailableChainFGSA.Proofs.StoreInv" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Statements/NegB.lean imports AvailableChainFGSARun.Proofs.X" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Statements/NegB.lean imports AvailableChainKitFG.Correspondence" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Proofs/NegB.lean imports AvailableChainFGSA.Tests.Support" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Tests/NegB.lean imports AvailableChainFGSA.Tests.Smoke"
}

control_import_forms() {
mk_tree
printf 'module\npublic import /- dependency -/ AvailableChainFramework.Profile\npublic\n  import\n  AvailableChainSAPC.Model.Choice\n' \
  > "$neg/tree/AvailableChainFGSARun/Proofs/NegC.lean"
run check_direct_imports "$neg/tree"
expect_fail "import after a comment and a line break" $code "$out" \
  "imports AvailableChainFramework.Profile" "imports AvailableChainSAPC.Model.Choice"
}

control_v1_imports() {
# New (plan §3.1): the v1 engine, the v1 Kit, the v1 statements and a Grid CO
# proof module are refused in every layer, Proofs/ and Tests/ included.
mk_tree
printf 'module\npublic import AvailableChainGridCO.Proofs.Basic\npublic import AvailableChainKit.Engine.Execution\n' \
  > "$neg/tree/AvailableChainFGSARun/Proofs/NegD.lean"
printf 'module\npublic import AvailableChainModel.Generic.Run\npublic import AvailableChainStatements.Generic.Claims\npublic import AvailableChainGridCO.Proofs.Hooks\n' \
  > "$neg/tree/AvailableChainFGSARun/Tests/NegD.lean"
run check_direct_imports "$neg/tree"
expect_fail "v1 engine, v1 Kit, v1 statements and Grid CO proof imports" $code "$out" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Proofs/NegD.lean imports AvailableChainGridCO.Proofs.Basic" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Proofs/NegD.lean imports AvailableChainKit.Engine.Execution" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Tests/NegD.lean imports AvailableChainModel.Generic.Run" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Tests/NegD.lean imports AvailableChainStatements.Generic.Claims" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Tests/NegD.lean imports AvailableChainGridCO.Proofs.Hooks"
}

orphan_tree() {
mk_tree
printf 'module\n@[expose] public section\ntheorem negOrphan : False := sorry\nend\n' \
  > "$neg/tree/AvailableChainFGSARun/Proofs/NegOrphan.lean"
printf 'module\n@[expose] public section\ntheorem negOrphanC : False := sorry\nend\n' \
  > "$neg/tree/AvailableChainFGSARun/Proofs/NegOrphanC.LEAN"
echo '/- public import AvailableChainFGSARun.Proofs.NegOrphan -/' >> "$neg/tree/AvailableChainFGSARun.lean"
echo 'public import AvailableChainFGSARun.Tests.Protocol' >> "$neg/tree/AvailableChainFGSARun.lean"
}

control_orphan() {
orphan_tree
run check_root_imports "$neg/tree"
expect_fail "orphan modules behind a commented import and with a .LEAN name (root check)" \
  $code "$out" "NOT IMPORTED BY THE ROOT: AvailableChainFGSARun.Proofs.NegOrphan" \
  "AvailableChainFGSARun.Proofs.NegOrphanC"
}

control_test_root() {
orphan_tree
# The same tree with the orphans removed: the root import of a Tests module.
rm "$neg/tree/AvailableChainFGSARun/Proofs/NegOrphan.lean" "$neg/tree/AvailableChainFGSARun/Proofs/NegOrphanC.LEAN"
run check_root_imports "$neg/tree"
expect_fail "a root import of a Tests module (root check, B7-TESTS)" \
  $code "$out" "ROOT IMPORTS A TEST MODULE: AvailableChainFGSARun.Tests.Protocol"
}

control_closure() {
orphan_tree
# The compiled checks: the orphan files (with a sorry) against the build, and
# forbidden libraries in the import closure (L* is new in this list).
cat > "$neg/RunClosureNeg.lean" <<'LEAN'
import AvailableChainSAPC.Model.Choice
import AvailableChainLStar.Model.Protocol
LEAN
lean_c "$neg/RunClosureNeg.olean" "$neg/RunClosureNeg.lean"
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSARunAxioms.lean --root RunClosureNeg --files "$0/tree/AvailableChainFGSARun" "${@}"' "$neg" "${AX_OPTS[@]}"
expect_fail "orphan modules and forbidden closure (axiom script)" $code "$out" \
  "NOT IN THE BUILD: AvailableChainFGSARun.Proofs.NegOrphan " \
  "NOT IN THE BUILD: AvailableChainFGSARun.Proofs.NegOrphanC " \
  "FORBIDDEN LIBRARY IN THE IMPORT CLOSURE: AvailableChainSAPC" \
  "FORBIDDEN LIBRARY IN THE IMPORT CLOSURE: AvailableChainLStar"
}

header_tree() {
# Header forms and file names that an earlier parser missed (G13 fold MINOR-2;
# the auditor's files in scripts/fgsa-controls/): a module name with «», a
# `prelude` line, a .LEAN file, and a linked directory. Each imports L*, which
# the allowlist forbids. A Grid CO proof module in Proofs/ (new) goes with
# them. First the text check, then the compiled check (the modules compiled as
# library modules, over a copy of the library build).
mk_tree
cp scripts/fgsa-controls/AdvG.lean scripts/fgsa-controls/AdvP.lean \
  scripts/fgsa-controls/AdvCase.LEAN "$neg/tree/AvailableChainFGSARun/Model/"
mkdir -p "$neg/sub" && cp scripts/fgsa-controls/Sub/X.lean "$neg/sub/"
ln -s "$neg/sub" "$neg/tree/AvailableChainFGSARun/Model/Sub"
printf 'module\npublic import AvailableChainGridCO.Proofs.Basic\n' > "$neg/tree/AvailableChainFGSARun/Proofs/NegGrid.lean"
printf 'public import AvailableChainFGSARun.Model.%s\n' AdvG AdvP AdvCase Sub.X \
  >> "$neg/tree/AvailableChainFGSARun.lean"
echo 'public import AvailableChainFGSARun.Proofs.NegGrid' >> "$neg/tree/AvailableChainFGSARun.lean"
}

control_header_text() {
header_tree
run check_direct_imports "$neg/tree"
expect_fail "header forms and file names (text allowlist)" $code "$out" \
  "UNPARSED IMPORT HEADER: AvailableChainFGSARun/Model/AdvG.lean" \
  "UNPARSED IMPORT HEADER: AvailableChainFGSARun/Model/AdvP.lean" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Model/AdvCase.LEAN imports AvailableChainLStar.Model.Protocol" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Model/Sub/X.lean imports AvailableChainLStar.Model.Protocol" \
  "IMPORT NOT ALLOWED: AvailableChainFGSARun/Proofs/NegGrid.lean imports AvailableChainGridCO.Proofs.Basic"
}

control_header_compiled() {
header_tree
mkdir -p "$neg/c"
cp -R .lake/build/lib/lean/AvailableChainFGSARun .lake/build/lib/lean/AvailableChainFGSARun.* "$neg/c/"
mkdir -p "$neg/c/AvailableChainFGSARun/Model/Sub" "$neg/c/AvailableChainFGSARun/Proofs"
for m in Model/AdvG:Model/AdvG.lean Model/AdvP:Model/AdvP.lean Model/AdvCase:Model/AdvCase.LEAN \
    Model/Sub/X:Model/Sub/X.lean Proofs/NegGrid:Proofs/NegGrid.lean; do
  lake env lean -o "$neg/c/AvailableChainFGSARun/${m%%:*}.olean" "$neg/tree/AvailableChainFGSARun/${m#*:}"
done
run lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean --run scripts/CheckFGSARunAxioms.lean --root AvailableChainFGSARun.Model.AdvG --root AvailableChainFGSARun.Model.AdvP --root AvailableChainFGSARun.Model.AdvCase --root AvailableChainFGSARun.Model.Sub.X --root AvailableChainFGSARun.Proofs.NegGrid --files "$0/tree/AvailableChainFGSARun" "${@}"' "$neg" "${AX_OPTS[@]}"
expect_fail "header forms and file names (compiled allowlist)" $code "$out" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSARun.Model.AdvG imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSARun.Model.AdvP imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSARun.Model.AdvCase imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSARun.Model.Sub.X imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSARun.Proofs.NegGrid imports AvailableChainGridCO.Proofs.Basic"
}

control_v2_open() {
# New (plan §3.1, TR9): the v1/v2 name clash. A plain `open AvailableChain.V2`,
# `open V2` inside `AvailableChain` with `hiding`, a selective list with `Auth`
# or `Signed`, the namespace on a second line, an `export`, and a `namespace`
# with a component `V2`; in a .LEAN file and in a linked directory too. A
# selective list without `Auth` and `Signed` passes.
mk_tree
if [ "$NEG" = 1 ]; then
printf 'module\nnamespace AvailableChain.FGSA.Run\nopen AvailableChain.V2\nend AvailableChain.FGSA.Run\n' \
  > "$neg/tree/AvailableChainFGSARun/Model/NegOpenA.lean"
printf 'module\nnamespace AvailableChain\nopen V2 hiding Auth Signed\nopen AvailableChain.V2 (Run Signed)\nexport AvailableChain.V2 (Auth)\nend AvailableChain\n' \
  > "$neg/tree/AvailableChainFGSARun/Statements/NegOpenB.lean"
printf 'module\nopen AvailableChain.Generic\n  AvailableChain.V2\nopen AvailableChain.V2 (Run tick) in\ndef ok : Nat := 0\nnamespace AvailableChain.V2.Extra\nend AvailableChain.V2.Extra\n' \
  > "$neg/tree/AvailableChainFGSARun/Proofs/NegOpenC.LEAN"
mkdir -p "$neg/osub"
printf 'module\nopen «AvailableChain».«V2»\n' > "$neg/osub/Y.lean"
ln -s "$neg/osub" "$neg/tree/AvailableChainFGSARun/Tests/OSub"
fi
printf 'module\nopen AvailableChain.V2 (Run tick)\nopen AvailableChain.V2.Engine\n' \
  > "$neg/tree/AvailableChainFGSARun/Tests/PosOpen.lean"
run check_v2_open "$neg/tree"
if [ "$NEG" = 1 ]; then
expect_fail "v1/v2 name clash (open, export, namespace)" $code "$out" \
  "PLAIN V2 OPEN: open AvailableChain.V2" "V2 NAME CLASH in AvailableChainFGSARun/Model/NegOpenA.lean" \
  "PLAIN V2 OPEN: open V2 hiding" "V2 OPEN LISTS Signed: open AvailableChain.V2 (Run Signed)" \
  "V2 OPEN LISTS Auth: export AvailableChain.V2 (Auth)" "V2 NAME CLASH in AvailableChainFGSARun/Statements/NegOpenB.lean" \
  "PLAIN V2 OPEN: open AvailableChain.Generic AvailableChain.V2" \
  "V2 NAMESPACE: namespace AvailableChain.V2.Extra" \
  "V2 NAME CLASH in AvailableChainFGSARun/Proofs/NegOpenC.LEAN" \
  "V2 NAME CLASH in AvailableChainFGSARun/Tests/OSub/Y.lean"
fi
if [[ $out == *'PosOpen.lean'* ]]; then
  echo "$out"; echo "NEGATIVE CONTROL v1/v2 name clash: a selective open was refused"; exit 1
fi
if [ "$NEG" = 0 ] && [ "$code" -ne 0 ]; then
  echo "$out"; echo "NEGATIVE CONTROL v1/v2 name clash: a selective open was refused"; exit 1
fi
}

control_used_constants() {
# A control constant must be a proof-module theorem, or a def that no model
# module re-exports (a def can move to a model module; a theorem cannot).
# New (plan §3.1): the used-constant check. The store proofs reach the v1 Kit,
# the v1 statements and the v1 engine. The control also imports Grid CO Map
# directly, so it does not depend on the store's Grid CO proof imports. It
# uses a v1 Kit constant, a v1 statements constant, a v1 engine constant, and
# a Grid CO proof predicate in a statement (the T7.W wrapper rule).
mk_tree
cat > "$neg/tree/AvailableChainFGSARun/Proofs/NegUse.lean" <<'LEAN'
module
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainGridCO.Proofs.Map
public import AvailableChainKit.Engine.EngineClock
@[expose] public section
namespace AvailableChain.FGSA.Run
def negKitClock {n : Nat} (P : AvailableChain.Generic.ProtocolSpec n) : Type :=
  AvailableChain.Engine.ClockLaws P
def negStatements : Type := AvailableChain.Statements.Generic.Constants
theorem negGridProof (n : Nat) : True :=
  have _h := GridCO.initial_prefix_deadline_order n
  trivial
end AvailableChain.FGSA.Run
end
LEAN
echo 'public import AvailableChainFGSARun.Proofs.NegUse' >> "$neg/tree/AvailableChainFGSARun.lean"
mkdir -p "$neg/c/AvailableChainFGSARun/Proofs"
cp -R .lake/build/lib/lean/AvailableChainFGSARun .lake/build/lib/lean/AvailableChainFGSARun.* "$neg/c/"
lake env lean -o "$neg/c/AvailableChainFGSARun/Proofs/NegUse.olean" "$neg/tree/AvailableChainFGSARun/Proofs/NegUse.lean"
run lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean --run scripts/CheckFGSARunAxioms.lean --root AvailableChainFGSARun.Proofs.NegUse --files "$0/tree/AvailableChainFGSARun" "${@}"' "$neg" "${AX_OPTS[@]}"
expect_fail "used constants of the v1 Kit, v1 statements, v1 engine and Grid CO proofs" $code "$out" \
  "FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negKitClock uses AvailableChain.Engine.ClockLaws (AvailableChainKit.Engine.EngineClock)" \
  "FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negKitClock uses AvailableChain.Generic.ProtocolSpec (AvailableChainModel.Generic.Run)" \
  "FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negStatements uses AvailableChain.Statements.Generic.Constants (AvailableChainStatements.Generic.Constants)" \
  "FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negGridProof uses AvailableChain.GridCO.initial_prefix_deadline_order (AvailableChainGridCO.Proofs.Map)"
}

control_walk_type() {
# New (review gate G-walk, the T7.W wrapper statement rule): no declaration
# TYPE of the library may name a Grid CO proof constant, so the used-constant
# check scans types, not only values. The control is a theorem whose statement
# names the Grid CO proof predicate `GridCO.ComparableTargets` and whose proof
# is the hypothesis with the predicate's body: only its type names the
# forbidden constant. Import Map directly so the control does not depend on
# the store's Grid CO proof imports.
mk_tree
cat > "$neg/tree/AvailableChainFGSARun/Proofs/NegWalk.lean" <<'LEAN'
module
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainGridCO.Proofs.Map
@[expose] public section
namespace AvailableChain.FGSA.Run
/-- NEGATIVE CONTROL (T7.W wrapper statement rule): the statement names the Grid
CO proof predicate `GridCO.ComparableTargets`. The used-constant check must
reject this declaration. -/
theorem negctl_walkWrapper_proofPredicate {n : Nat} (st : GridCO.State n)
    (h : ∀ K g d, (K, g, d) ∈ st.obligations →
      ∀ B level expiry, (B, level, expiry) ∈ st.obligations →
        Block.compatible K B = true) : GridCO.ComparableTargets st :=
  h
end AvailableChain.FGSA.Run
end
LEAN
echo 'public import AvailableChainFGSARun.Proofs.NegWalk' >> "$neg/tree/AvailableChainFGSARun.lean"
mkdir -p "$neg/c/AvailableChainFGSARun/Proofs"
cp -R .lake/build/lib/lean/AvailableChainFGSARun .lake/build/lib/lean/AvailableChainFGSARun.* "$neg/c/"
lake env lean -o "$neg/c/AvailableChainFGSARun/Proofs/NegWalk.olean" "$neg/tree/AvailableChainFGSARun/Proofs/NegWalk.lean"
run lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean --run scripts/CheckFGSARunAxioms.lean --root AvailableChainFGSARun.Proofs.NegWalk --files "$0/tree/AvailableChainFGSARun" "${@}"' "$neg" "${AX_OPTS[@]}"
expect_fail "a Grid CO proof predicate in a statement type (G-walk)" $code "$out" \
  "FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negctl_walkWrapper_proofPredicate uses AvailableChain.GridCO.ComparableTargets (AvailableChainGridCO.Proofs.Map)"
}

control_constant_owner() {
# New (T7.2 R-A, Opus 2): generated constants are judged by their owner
# definition. NEGATIVE: a proof that unfolds a definition of a forbidden module
# (`GridCO.ComparableTargets`, Grid CO proofs) by its generated equation
# (`eq_def`); the equation is refused through its owner. POSITIVE: proofs that `split` and
# `simp` over `GridCO.admitVote` and `GridCO.excludes` (Grid CO model); Lean
# realizes private matcher equations in the library that use
# `_sparseCasesOn_<k>.else_eq` constants of `AvailableChainGridCO.Proofs.Map`,
# and the check accepts them, because their owners are Grid CO model
# definitions.
mk_tree
if [ "$NEG" = 1 ]; then
cat > "$neg/tree/AvailableChainFGSARun/Proofs/NegOwner.lean" <<'LEAN'
module
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainGridCO.Proofs.Map
@[expose] public section
namespace AvailableChain.FGSA.Run
theorem negOwnerRoots {n : Nat} (st : GridCO.State n) (h : GridCO.ComparableTargets st) :
    ∀ K g d, (K, g, d) ∈ st.obligations →
      ∀ B level expiry, (B, level, expiry) ∈ st.obligations →
        Block.compatible K B = true := by
  rw [GridCO.ComparableTargets.eq_def] at h
  exact h
end AvailableChain.FGSA.Run
end
LEAN
echo 'public import AvailableChainFGSARun.Proofs.NegOwner' >> "$neg/tree/AvailableChainFGSARun.lean"
fi
cat > "$neg/tree/AvailableChainFGSARun/Proofs/PosOwner.lean" <<'LEAN'
module
public import AvailableChainFGSA.Proofs.StoreInv
@[expose] public section
namespace AvailableChain.FGSA.Run
theorem posOwnerSplit (q : GridCO.Params) {n : Nat} (st : GridCO.State n) (o : GridCO.Wire n) :
    (GridCO.admitVote q st o).now = st.now := by
  unfold GridCO.admitVote
  split
  · dsimp only; split <;> rfl
  · rfl
theorem posOwnerSimp (q : GridCO.Params) {n : Nat} {st st' : GridCO.State n}
    (hv : st'.votes = st.votes) (hn : st'.now = st.now) (o : GridCO.Wire n) :
    GridCO.excludes q st' o = GridCO.excludes q st o := by
  simp only [GridCO.excludes, GridCO.votesAt, hv, hn]
end AvailableChain.FGSA.Run
end
LEAN
echo 'public import AvailableChainFGSARun.Proofs.PosOwner' >> "$neg/tree/AvailableChainFGSARun.lean"
mkdir -p "$neg/c/AvailableChainFGSARun/Proofs"
cp -R .lake/build/lib/lean/AvailableChainFGSARun .lake/build/lib/lean/AvailableChainFGSARun.* "$neg/c/"
owner_mods=(PosOwner)
# Merge must pass the whole scan, including Tests/ outside the root closure.
owner_roots=(--root AvailableChainFGSARun.Proofs.PosOwner "${TEST_ROOTS[@]}")
if [ "$NEG" = 1 ]; then
  owner_mods=(NegOwner PosOwner)
  owner_roots=(--root AvailableChainFGSARun.Proofs.NegOwner --root AvailableChainFGSARun.Proofs.PosOwner)
fi
for m in "${owner_mods[@]}"; do
  lake env lean -o "$neg/c/AvailableChainFGSARun/Proofs/$m.olean" "$neg/tree/AvailableChainFGSARun/Proofs/$m.lean"
done
run lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean --run scripts/CheckFGSARunAxioms.lean "${@}"' "$neg" \
  "${owner_roots[@]}" --files "$neg/tree/AvailableChainFGSARun" "${AX_OPTS[@]}"
if [ "$NEG" = 1 ]; then
expect_fail "a generated equation of a Grid CO proof definition (owner)" $code "$out" \
  "FORBIDDEN CONSTANT: AvailableChain.FGSA.Run.negOwnerRoots uses" \
  "(owner AvailableChain.GridCO.ComparableTargets (AvailableChainGridCO.Proofs.Map))"
elif [ "$code" -ne 0 ]; then
  echo "$out"; echo "POSITIVE CONTROL owner mapping: a Grid CO model matcher equation was refused"; exit 1
fi
if printf '%s\n' "$out" | grep -F 'FORBIDDEN CONSTANT' | grep -qv 'negOwnerRoots'; then
  echo "$out"; echo "POSITIVE CONTROL owner mapping: a Grid CO model matcher equation was refused"; exit 1
fi
echo "accepted, as expected: generated equations of Grid CO model definitions (owner)"
}

control_lease() {
# Lease controls (the controls of scripts/check-fgsa.sh, over the run library):
# a direct default-instance call; the anchored gate and tick at the grid
# policy; an alias wrapper with its own policy parameter in another namespace;
# a generic wrapper whose policy binder has an alias type; an imported wrapper
# that fixes the default instance inside.
cat > "$neg/FGSALeaseNeg.lean" <<'LEAN'
import AvailableChainFGSARun
import AvailableChainFGSA
namespace AvailableChain.FGSA
/-- A GridCO gate at the default instance `gridLeasePolicy`. -/
def leaseNegControl (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.gate p st r
/-- The anchored GridCO gate at `gridLeasePolicy`. -/
def leaseNegGateFrom (p : GridCO.Params) (a : Block) (st : GridCO.State 1) (r : Nat) :
    GridCO.State 1 :=
  @GridCO.gateFrom GridCO.gridLeasePolicy p 1 .block a st r
/-- The anchored GridCO tick at `gridLeasePolicy`. -/
def leaseNegClockFrom (p : GridCO.Params) (a : Block) (st : GridCO.State 1) (t : Int) :
    GridCO.State 1 :=
  @GridCO.clockFrom GridCO.gridLeasePolicy p 1 .block a st t
end AvailableChain.FGSA
namespace AvailableChain.LeaseAuditAlias
def gate (_policy : GridCO.LeasePolicy) (p : GridCO.Params)
    (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  @GridCO.gate GridCO.gridLeasePolicy p 1 .block st r
end AvailableChain.LeaseAuditAlias
namespace AvailableChain.FGSA
def badGate (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  AvailableChain.LeaseAuditAlias.gate GridCO.slowLeasePolicy p st r
end AvailableChain.FGSA
namespace AvailableChain.GridCO
abbrev PolicyAlias : Type := LeasePolicy
def sneakyGate [PolicyAlias] (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 .block st r
end AvailableChain.GridCO
namespace AvailableChain.FGSA
def badGate2 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  @GridCO.sneakyGate GridCO.slowLeasePolicy p st r
end AvailableChain.FGSA
LEAN
cat > "$neg/FGSALeaseLib.lean" <<'LEAN'
import AvailableChainFGSARun
import AvailableChainFGSA
namespace AvailableChain.GridCO
/-- An imported wrapper with no policy parameter that fixes the default. -/
def fixedGate (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 .block st r
end AvailableChain.GridCO
namespace LeaseMk
/-- Outside `AvailableChain`: a new policy value built with the constructor. -/
def mkGate (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) (r : Nat) :
    AvailableChain.GridCO.State 1 :=
  @AvailableChain.GridCO.gate ⟨false⟩ p 1 .block st r
end LeaseMk
LEAN
cat > "$neg/FGSALeaseUse.lean" <<'LEAN'
import FGSALeaseLib
namespace AvailableChain.FGSA
def badGate3 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.fixedGate p st r
def badGate4 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  LeaseMk.mkGate p st r
end AvailableChain.FGSA
LEAN
for m in FGSALeaseNeg FGSALeaseLib FGSALeaseUse; do
  lean_c "$neg/$m.olean" "$neg/$m.lean"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSARunLease.lean FGSALeaseNeg FGSALeaseUse' "$neg"
expect_fail "lease controls" $code "$out" \
  "leaseNegControl: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "leaseNegGateFrom: AvailableChain.GridCO.gateFrom at AvailableChain.GridCO.gridLeasePolicy" \
  "leaseNegClockFrom: AvailableChain.GridCO.clockFrom at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.LeaseAuditAlias.gate: has a policy parameter" \
  "AvailableChain.GridCO.sneakyGate: has a policy parameter" \
  "AvailableChain.GridCO.fixedGate: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "LeaseMk.mkGate: mentions AvailableChain.GridCO.LeasePolicy.mk (reach)"
}

control_imported_lease() {
# Imported definitions (G13 fold MINOR-1; the auditor's AdvLib/AdvUse in
# scripts/fgsa-controls/): a let-bound and a beta-bound default policy, a
# private wrapper, an irreducible alias of the policy type, and a wrapper
# outside the namespace AvailableChain (the reachability backstop).
cp scripts/fgsa-controls/AdvLib.lean scripts/fgsa-controls/AdvUse.lean "$neg/"
for m in AdvLib AdvUse; do
  lean_c "$neg/$m.olean" "$neg/$m.lean"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSARunLease.lean AdvUse' "$neg"
expect_fail "lease controls in imported definitions" $code "$out" \
  "AvailableChain.GridCO.fixedLet: AvailableChain.GridCO.gate at #0" \
  "AvailableChain.GridCO.fixedBeta: AvailableChain.GridCO.gate at #0" \
  "AdvLib.0.AvailableChain.GridCO.fixedPriv: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.FGSA.useIrr: AvailableChain.GridCO.genI at cast" \
  "Evil.fixedGate: mentions AvailableChain.GridCO.gridLeasePolicy (reach)"
}

lease_owner_files() {
# Generated constants (T7.2 R-A; the owner map of
# scripts/AvailableChainCheckSupport/GeneratedOwner.lean). NEGATIVE: an
# imported definition with no policy parameter that fixes the default policy,
# used through its generated equation (`eq_def`): its owner is inspected and
# refused. POSITIVE: `split` and `simp` over `GridCO.admitVote` and
# `GridCO.excludes` (private matcher equations and sparse `casesOn`
# equations): no report. OWNER PATH ONLY: a generated equation with a policy
# parameter, realized in the scanned module, is skipped, and only its owner's
# inspection refuses it. No control separates the owner map from the earlier
# `eq_<k>`/`eq_def` rule: that rule was stricter than needed, never unsound (it
# scanned a private generated constant as an ordinary one). The owner map is
# safe: every generated constant that it skips has its owner inspected, and
# the policy is checked at every use.
cat > "$neg/RunLeaseOwnLib.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.GridCO
/-- An imported definition with no policy parameter that fixes the default. -/
def ownerFixedGate (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 .block st r
/-- A policy-generic imported definition that passes its own policy through a
beta-redex: at `gate` the policy is a bound variable, not an own parameter. -/
def ownerBetaGen [L : LeasePolicy] (p : Params) (st : State 1) (r : Nat) : State 1 :=
  (fun (pol : LeasePolicy) => @gate pol p 1 .block st r) L
end AvailableChain.GridCO
LEAN
cat > "$neg/RunLeaseOwnOnly.lean" <<'LEAN'
import RunLeaseOwnLib
-- Realizes the equation `ownerBetaGen.eq_1` (it has the policy parameter `L`)
-- in this scanned module; no declaration of this module mentions the owner.
attribute [simp] AvailableChain.GridCO.ownerBetaGen.eq_1
namespace AvailableChain.FGSA
def ownOnlyAnchor : Nat := 0
end AvailableChain.FGSA
LEAN
cat > "$neg/RunLeaseOwnNeg.lean" <<'LEAN'
import RunLeaseOwnLib
namespace AvailableChain.FGSA
theorem negLeaseOwner (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) :
    GridCO.ownerFixedGate p st r = GridCO.ownerFixedGate p st r := by
  rw [GridCO.ownerFixedGate.eq_def]
end AvailableChain.FGSA
LEAN
cat > "$neg/RunLeaseOwnPos.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.FGSA
theorem posLeaseSplit (q : GridCO.Params) {n : Nat} (st : GridCO.State n) (o : GridCO.Wire n) :
    (GridCO.admitVote q st o).now = st.now := by
  unfold GridCO.admitVote
  split
  · dsimp only; split <;> rfl
  · rfl
theorem posLeaseSimp (q : GridCO.Params) {n : Nat} {st st' : GridCO.State n}
    (hv : st'.votes = st.votes) (hn : st'.now = st.now) (o : GridCO.Wire n) :
    GridCO.excludes q st' o = GridCO.excludes q st o := by
  simp only [GridCO.excludes, GridCO.votesAt, hv, hn]
end AvailableChain.FGSA
LEAN
}

compile_lease_owner() {
for m in "$@"; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
}

control_lease_owner() {
lease_owner_files
compile_lease_owner RunLeaseOwnLib RunLeaseOwnNeg
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSARunLease.lean RunLeaseOwnNeg' "$neg"
expect_fail "lease: a policy-fixing definition through its generated equation (owner)" $code "$out" \
  "AvailableChain.GridCO.ownerFixedGate: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.FGSA.negLeaseOwner: mentions AvailableChain.GridCO.gridLeasePolicy (reach)"
}

control_lease_owner_only() {
lease_owner_files
compile_lease_owner RunLeaseOwnLib RunLeaseOwnOnly
# OWNER PATH ONLY: the generated equation with a policy parameter is skipped
# (it is not scanned as a constant of the scanned module, so no "has a policy
# parameter" report), and its owner is inspected and refused. No other report
# (no backstop "reach" line): the owner mentions no default policy.
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSARunLease.lean RunLeaseOwnOnly' "$neg"
expect_fail "lease: a policy-generic owner caught only through its skipped equation" $code "$out" \
  "BAD LEASE INSTANCE AvailableChain.GridCO.ownerBetaGen: AvailableChain.GridCO.gate at #0"
if [ "$(printf '%s\n' "$out" | grep -cF 'BAD LEASE INSTANCE')" -ne 1 ]; then
  echo "$out"; echo "NEGATIVE CONTROL lease owner path: a report other than the owner's"; exit 1
fi
}

positive_lease_owner() {
lease_owner_files
compile_lease_owner RunLeaseOwnPos
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSARunLease.lean RunLeaseOwnPos' "$neg"
gate_control_check "lease owner map" "$code" "$out" || exit 1
if [ "$code" -ne 0 ] || [[ $out == *'BAD LEASE INSTANCE'* ]]; then
  echo "$out"; echo "POSITIVE CONTROL lease owner map: split/simp over GridCO.admitVote was refused"; exit 1
fi
echo "accepted, as expected: lease: generated equations of Grid CO model definitions (owner)"
}

control_missing_expected() {
# A name in --expect that the scan does not find fails the check (fail closed).
run lake env lean --run scripts/CheckFGSARunAxioms.lean "${TEST_ROOTS[@]}" \
  "${AX_OPTS[@]}" Run.negNotADeclaration
expect_fail "an expected name that is not checked" $code "$out" \
  "NOT CHECKED: Run.negNotADeclaration" "1 expected names not checked"
}

if [ "$NEG" = 1 ]; then
  gate_pool_add control_unlisted
  gate_pool_add control_layer
  gate_pool_add control_import_forms
  gate_pool_add control_v1_imports
  gate_pool_add control_orphan
  gate_pool_add control_test_root
  gate_pool_add control_closure
  gate_pool_add control_header_text
  gate_pool_add control_header_compiled
fi
# Mixed controls retain their positive checks and serial order in both tiers.
gate_control_serial control_v2_open
if [ "$NEG" = 1 ]; then
  gate_pool_add control_used_constants
  gate_pool_add control_walk_type
fi
gate_control_serial control_constant_owner
if [ "$NEG" = 1 ]; then
  gate_pool_add control_lease
  gate_pool_add control_imported_lease
  gate_pool_add control_lease_owner
  gate_pool_add control_lease_owner_only
fi
gate_control_serial positive_lease_owner
if [ "$NEG" = 1 ]; then gate_pool_add control_missing_expected; fi
gate_pool_wait
echo "all FGSA run checks pass"
