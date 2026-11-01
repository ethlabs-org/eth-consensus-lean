module
public import AvailableChainFGSAInhabit.WeakContinuationW1 -- shake: keep (type checks)

/-! W1 port inventory and type checks.

Source: lf-w2, commit 338d4ba. The checks below list every retained public name.
All other facts keep their content after the duty-engine and window-model port.

Mechanical name changes:
* participation -> witness_participation; prefix_times -> witness_prefix_times.
* window_bounds -> witness_window_bounds.
* gen_proposalRows_closed -> gen_proposalRows_origin.
* W1Uniform -> GenUniformStores; W1Deps -> GenDeps; W1Unique -> GenSingleDutyUnique.

Changed helper contracts:
* params/design_numbers: wF = 1 -> K_W = 2; row labels are now fixed.
* bounds keep the legacy arithmetic; witness_window_bounds adds the current W arithmetic.
* endpoint: B_H params 4 -> B_HF params 1 4.
* agreement_of_suffix, agreement, replay_of_agreement: add row delay 1 and delta equality.
* tick_nodup_without_gossip: ProtocolSpec -> ProtocolSpecD, with due-label injectivity.
* gen_tick_seat: a signing label -> a duty and its signing label.
* gen_derive_positive: the old scalar height -> heightView.
* gen_attest_valid: unconditional row validity -> validity of each released optional row.
* i7_admitRow_duplicate, i7_decode_row: remove the round; use the fixed label and RowPayload.
* w1_proposal_rows: validity plus a row-round bound -> validity (rows have no round).
* w1_proposal_wf: remove the unused current-slot equality.
* GenSingleDutyUnique/w1_emits_unique: key uniqueness -> single-duty key uniqueness.
* w1_row_accept: remove round, knowledge, and key-uniqueness conditions; accept each full row.
* w1_emission_time: label time -> duty time for a single-duty label.
* w1_not_past: an arbitrary node state -> the actual generated prefix state.
  The proof uses the durable sent set for fixed-label rows.
* w1_strongRecovery: add row delay 1, family synchrony, and LivenessBoundW.
* w1_cleanContinuation: add row delay 1 and family synchrony.
* All engine run, replay, execution, and synchrony names use V2.D.
  Generic duty facts use Gen.V2.Duty. The store uses Window.on_block and R6W.

Dropped old proof helpers:
* gen_process_row_height, gen_rows_height, gen_height_events_positive:
  superseded by the current window height laws.
* gen_height_pair_fields: superseded by KitFG.height_pair_vote_fields.
* i7RefusalAtEight, i7_refusal_at_eight, i7_rows_at_six:
  old signed-empty-row diagnostics. R3 suppresses empty rows in this model;
  the old round-labelled empty-row terms no longer have the row-payload type.
  These diagnostics are not used by ExecutionValid or either recovery fact.
-/

open AvailableChain AvailableChain.FGSA AvailableChain.FGSA.Run
open AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

#check params
#check Validator
#check Event
#check World
#check strongEnv
#check weakEnv
#check seatOf
#check runData
#check nodes
#check tickBatch
#check deliverOne
#check timeBatch
#check buildPrefix
#check source
#check buildSuffix
#check continuation
#check design_numbers
#check delta_ratio
#check bounds
#check witness_window_bounds
#check horizons
#check endpoint
#check witness_covered
#check environments
#check honest_sets
#check faulty_sets
#check fault_bound
#check strong_awake
#check weak_awake_iff
#check awake_agreement
#check strong_awake_set
#check weak_awake_set_before
#check weak_awake_set_after
#check awake_counts
#check witness_participation
#check strict_drop
#check later_sleep
#check cstar
#check linked
#check gap_positive
#check gap_aligned
#check source_gap
#check boundary_duties
#check delivery_fold_mem
#check timeBatch_shape
#check timeBatch_time
#check timeBatch_no_restart
#check nodes_complete
#check timeBatch_tick
#check witness_prefix_times
#check suffix_times
#check prefix_no_restart
#check suffix_no_restart
#check no_restart
#check event_prefix
#check suffix_after_endpoint
#check agreement_of_suffix
#check agreement
#check witness_committees
#check recovery_awake
#check prefix_tick
#check suffix_tick
#check source_horizon_nonneg
#check continuation_horizon_nonneg
#check source_in_horizon
#check continuation_in_horizon
#check source_honest_only
#check continuation_honest_only
#check source_tick_public
#check continuation_tick_public
#check witness_source_tick_total
#check continuation_tick_total
#check suffix_has_ticks
#check phase_le_two
#check key_le_delivery
#check delivery_fold_sorted
#check timeBatch_sorted
#check prefix_sorted
#check suffix_sorted
#check source_sorted
#check continuation_sorted
#check replay_of_agreement
#check source_replay
#check genFold
#check GenFresh
#check genFold_append
#check genFresh_append
#check tick_fold_replay
#check tickBatch_replay
#check tick_list_fresh
#check delivery_fold_replay_fresh
#check timeBatch_replay_fresh
#check prefix_replay_fresh
#check suffix_replay_fresh
#check genFresh_get
#check genFold_runData
#check genFresh_join
#check runData_fresh
#check continuation_events_eq
#check continuation_genFresh
#check continuation_fresh
#check source_fresh
#check GenEmits
#check GenOrigin
#check genEmits_cons
#check genEmits_append_left
#check genEmits_append_right
#check genOrigin_append
#check tick_fold_origin
#check tickBatch_origin
#check delivery_fold_sublist
#check timeBatch_block
#check prefix_blocks
#check suffix_blocks
#check timeBatch_origin
#check prefix_origin
#check suffix_origin
#check genEmits_runData
#check gen_tick_holder
#check genOrigin_unforgeable
#check continuation_genOrigin
#check continuation_unforgeable
#check source_emits_weak_to_strong
#check source_unforgeable
#check tick_nodup_without_gossip
#check gen_tick_nodup
#check tick_fold_nodup
#check tickBatch_nodup
#check timeBatch_nodup
#check prefix_nodup
#check suffix_nodup
#check source_nodup
#check continuation_nodup
#check witness_source_schedule
#check continuation_schedule
#check runData_stateBefore
#check genOrigin_runData
#check source_delivery_origin
#check continuation_delivery_origin
#check gen_nonproposal_deps
#check gen_derive_positive
#check gen_attest_valid
#check gen_tick_seat
#check gen_tick_nonproposal_wire
#check delivery_fold_offered
#check timeBatch_offered
#check genOrigin_nonproposal_wire
#check source_nonproposal_wire
#check continuation_nonproposal_wire
#check i7_admitRow_duplicate
#check i7_clock_fields
#check i7_clock_proposals
#check i7_clock_rowPool
#check i7_reconcile_fields
#check i7_admitRow_eq
#check i7_foldl_admitRow_eq
#check i7_tick_st
#check GenStoredRows
#check gen_proposalRows_origin
#check gen_storedRows_clock
#check gen_storedRows_fold
#check gen_storedRows_process
#check gen_process_pool_mono
#check GenPoolWitness
#check gen_tick_proposal_rows
#check gen_tick_pool_fields
#check gen_tick_fold_pool
#check gen_deliver_pool
#check gen_delivery_fold_pool
#check gen_timeBatch_pool
#check gen_prefix_pool
#check gen_suffix_pool
#check i7_prefix_selected_rows
#check i7_suffix_selected_rows
#check i7_clock_votes
#check GenKnown
#check gen_known_mono
#check gen_known_clock
#check gen_known_row
#check gen_known_rows
#check gen_known_vote
#check i7_lift_baseVote
#check gen_known_base_proposal
#check i7_decode_vote
#check i7_decode_row
#check i7_decode_proposal
#check gen_known_reconcile
#check gen_known_process
#check gen_tick_children_known
#check gen_tick_fold_known
#check gen_delivery_fold_known
#check gen_timeBatch_known
#check gen_timeBatch_delivered
#check GenPast
#check GenCarried
#check gen_past_append
#check gen_past_bound
#check gen_batch_carried
#check gen_prefix_carried
#check gen_suffix_carried
#check genCarried_runData
#check source_carried
#check continuation_carried
#check source_signatures
#check continuation_signatures
#check i7_tick_fold_pool_eq
#check i7_batch_emitted_rows
#check i7_prefix_emitted_rows
#check i7_suffix_emitted_rows
#check gen_past_row_valid
#check gen_prefix_rows_valid
#check gen_suffix_rows_valid
#check i7_prefix_proposal_rows_valid
#check i7_suffix_proposal_rows_valid
#check i7_eight_in_both_runs
#check w1_proposal_rows
#check w1_proposal_votes
#check w1_proposal_wf
#check w1_known_fold
#check w1_rows_at_index
#check w1_emit_wire
#check w1_source_schedule
#check w1_source_wire
#check w1_continuation_wire
#check w1_process_inert
#check w1_deliver_st
#check w1_offer_st
#check w1_tickBatch_st
#check GenUniformStores
#check w1_offer_uniform
#check w1_objects_uniform
#check w1_batch_uniform
#check w1_prefix_uniform
#check w1_suffix_uniform
#check w1_tickBatch_emits
#check w1_reachable
#check w1_tick_deps
#check w1_batch_deps_start
#check w1_deps_mono
#check w1_deliver_deps
#check GenDeps
#check w1_deps_append
#check w1_delivery_fold_deps
#check w1_ticks_deps
#check w1_batch_deps
#check w1_prefix_deps
#check w1_suffix_deps
#check w1_deps_get
#check w1_continuation_genDeps
#check w1_continuation_deps
#check w1_source_deps
#check w1_source_execution
#check w1_continuation_execution
#check w1_suffix_eq
#check w1_prefix_schedule
#check GenSingleDutyUnique
#check w1_emits_unique
#check w1_head_accept
#check w1_row_accept
#check w1_processed_mono
#check w1_process_processed
#check w1_deliver_processed
#check w1_fold_processed
#check w1_deliver_now
#check w1_fold_complete
#check w1_nonproposal_accept
#check w1_batch_nonproposal_complete
#check w1_proposal_only
#check w1_proposal_singleton
#check w1_proposal_accept
#check w1_batch_proposal_complete
#check w1_prefix_emits
#check w1_batch_complete
#check w1_prefix_complete
#check w1_suffix_complete
#check w1_emission_time
#check w1_not_past
#check w1_clock_processed
#check w1_known_fold_local
#check w1_batch_known_receipt
#check w1_nonproposal_receipt
#check w1_fold_no_local
#check w1_prefix_tick_zero
#check w1_proposal_fresh_start
#check w1_proposal_receipt
#check w1_batch_receipt
#check w1_batch_tick_state
#check w1_locate_emission
#check w1_prefix_broadcast
#check w1_fold_stable
#check w1_prefix_prefix
#check w1_prefix_stable
#check w1_past_complete
#check w1_index_after
#check w1_index_stable
#check w1_handles_carries
#check w1_child_processed
#check w1_prefix_relay
#check w1_direct_handle
#check w1_prefix_sync
#check w1_source_state
#check w1_source_emits
#check w1_source_sync
#check w1_continuation_eq
#check w1_continuation_sync
#check w1_strongRecovery
#check w1_cleanContinuation

example : V2.D.ExecutionValid strongEnv source := w1_source_execution
example : V2.D.ExecutionValid weakEnv continuation := w1_continuation_execution
example : StrongRecoverySearchPrefix₂ params unitCodec strongEnv source 4 1 :=
  w1_strongRecovery
example : CleanContinuation₂ params unitCodec strongEnv source weakEnv continuation 1 :=
  w1_cleanContinuation
example : Gen.V2.Duty.PartialSynchronyBy strongEnv source (fgsaDelay strongEnv.Δ 1) :=
  w1_strongRecovery.sync
example : Gen.V2.Duty.PartialSynchronyBy weakEnv continuation (fgsaDelay weakEnv.Δ 1) :=
  w1_cleanContinuation.sync
example : source.horizon = 253 ∧ continuation.horizon = 269 := horizons
example : (Gen.V2.Duty.awakeHonest weakEnv continuation 254).card <
    (Gen.V2.Duty.awakeHonest strongEnv source 253).card := strict_drop

#check w1_cleanContinuationSleep

example : ((tickBatch 254 V2.D.World.init).1 (1 : Validator)).st =
    (V2.D.World.init (P := fgsa params unitCodec) (1 : Validator)).st :=
  w1_tickBatch_sleep_st 254 _ 1 (by decide)
