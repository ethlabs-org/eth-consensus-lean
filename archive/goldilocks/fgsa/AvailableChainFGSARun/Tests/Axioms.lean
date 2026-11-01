module
public import AvailableChainFGSARun.Proofs.RootResolution -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.RootLease -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.NamedDelivery -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.HeadIdentity -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.NamedScope -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.WindowExclusion -- shake: keep (axioms)
public import AvailableChainFGSARun.Statements.Slashing -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.AncestorDeadlines -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.ReceiptCoverage -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.EmissionWellFormed -- shake: keep (axioms)
public import AvailableChainFGSARun.Model.Protocol -- shake: keep (axioms)
public import AvailableChainFGSARun.Model.Families -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Protocol -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Excludes -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Interface -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.ClockLaws -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Reachable -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Content -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Hooks -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Readiness -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Acceptance -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Emission -- shake: keep (axioms)
public import AvailableChainFGSARun.Statements.Client -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.ClientTrace -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Slashing -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.HeadHistory -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.ProposalHistory -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.ReadyAcceptance -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.FGSource -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.Join -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.RowHistory -- shake: keep (#print axioms)
public import AvailableChainFGSARun.Proofs.Schedule -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.AC -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Receipts -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Spec.Simulation -- shake: keep (#print axioms)

/-! Kernel dependency audit of the FG-SA run library (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md`, T7.1): one `#print axioms`
line for each public theorem and each E5 value of the library. Each line
prints only `propext`, `Classical.choice`, `Quot.sound`, or no axiom.
`scripts/CheckFGSARunAxioms.lean` checks every constant of the library
mechanically. -/

-- Interface and clock laws (T7.3, T7.4)
#print axioms AvailableChain.FGSA.Run.fgsaInterface
#print axioms AvailableChain.FGSA.Run.fgsaOutputs
#print axioms AvailableChain.FGSA.Run.finalizedOut
#print axioms AvailableChain.FGSA.Run.proposalTime_fgsa
#print axioms AvailableChain.FGSA.Run.propLabel_injective
#print axioms AvailableChain.FGSA.Run.fgsaClock
#print axioms AvailableChain.FGSA.Run.fgsa_monoAlong_preceq_F
#print axioms AvailableChain.FGSA.Run.fgsa_restore_now
#print axioms AvailableChain.FGSA.Run.fgsaRestoreTimeLaw
#print axioms AvailableChain.FGSA.Run.fgsa_hrestore_retained
#print axioms AvailableChain.FGSA.Run.fgsa_hrestore_field_retained

-- Model/Protocol.lean (T7.2)
#print axioms AvailableChain.FGSA.Run.toWireEquiv
#print axioms AvailableChain.FGSA.Run.slotOf_offset
#print axioms AvailableChain.FGSA.Run.duties_spec
#print axioms AvailableChain.FGSA.Run.duties_nodup
#print axioms AvailableChain.FGSA.Run.fgsa

-- Model/Families.lean (T7.2)
#print axioms AvailableChain.FGSA.Run.fgsaFamilies
#print axioms AvailableChain.FGSA.Run.fgsaIso

-- Proofs/Protocol.lean (T7.2)
#print axioms AvailableChain.FGSA.Run.restore_st
#print axioms AvailableChain.FGSA.Run.restore_rec
#print axioms AvailableChain.FGSA.Run.clock_rec
#print axioms AvailableChain.FGSA.Run.process_rec
#print axioms AvailableChain.FGSA.Run.recordOwn_st
#print axioms AvailableChain.FGSA.Run.recordOwn_rec
#print axioms AvailableChain.FGSA.Run.attest_signer_irrel
#print axioms AvailableChain.FGSA.Run.act_fg
#print axioms AvailableChain.FGSA.Run.recordOwn_attest
#print axioms AvailableChain.FGSA.Run.act_prop
#print axioms AvailableChain.FGSA.Run.act_prop_zero
#print axioms AvailableChain.FGSA.Run.withApp_zero
#print axioms AvailableChain.FGSA.Run.rowsOk_withApp
#print axioms AvailableChain.FGSA.Run.singleSeat_prop
#print axioms AvailableChain.FGSA.Run.linked_selfVisible
#print axioms AvailableChain.FGSA.Run.tick_st
#print axioms AvailableChain.FGSA.Run.ofWire_toWire
#print axioms AvailableChain.FGSA.Run.toWire_ofWire
#print axioms AvailableChain.FGSA.Run.toWire_injective
#print axioms AvailableChain.FGSA.Run.toWire_ofHead
#print axioms AvailableChain.FGSA.Run.toWire_ofRow
#print axioms AvailableChain.FGSA.Run.ofRow_injective
#print axioms AvailableChain.FGSA.Run.ofHead_injective
#print axioms AvailableChain.FGSA.Run.ofRow_auth
#print axioms AvailableChain.FGSA.Run.decode_eq_vote
#print axioms AvailableChain.FGSA.Run.decode_eq_row
#print axioms AvailableChain.FGSA.Run.decode_eq_block
#print axioms AvailableChain.FGSA.Run.rowWire_decode
#print axioms AvailableChain.FGSA.Run.processedS_ofRow
#print axioms AvailableChain.FGSA.Run.excludesS_ofRow
#print axioms AvailableChain.FGSA.Run.handlesS_ofRow_iff

-- Proofs/Excludes.lean (T7.2, `excludes_inert`)
#print axioms AvailableChain.FGSA.Run.Internal.eraseDups_nodup'
#print axioms AvailableChain.FGSA.Run.Internal.grid_equivocates_mono
#print axioms AvailableChain.FGSA.Run.Internal.grid_votesAt_subset
#print axioms AvailableChain.FGSA.Run.Internal.lt_sub_one_iff_add_one_lt
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_head_iff
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_head
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_congr
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_now
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_of_excludes
#print axioms AvailableChain.FGSA.Run.Internal.grid_excludes_of_votes
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitVote_keeps
#print axioms AvailableChain.FGSA.Run.Internal.grid_fold_keeps
#print axioms AvailableChain.FGSA.Run.Internal.grid_fold_now
#print axioms AvailableChain.FGSA.Run.Internal.grid_fold_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitProposal_now
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitProposal_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.grid_admitProposal_keeps
#print axioms AvailableChain.FGSA.Run.excludesS_of_vote
#print axioms AvailableChain.FGSA.Run.excludesS_of_row
#print axioms AvailableChain.FGSA.Run.excludesS_of_block
#print axioms AvailableChain.FGSA.Run.excludesS_of_none
#print axioms AvailableChain.FGSA.Run.row_wire_roundtrip
#print axioms AvailableChain.FGSA.Run.admitBlock_of_blockExcluded
#print axioms AvailableChain.FGSA.Run.excludesS_inert
#print axioms AvailableChain.FGSA.Run.excludes_inert
#print axioms AvailableChain.FGSA.Run.Internal.admitRow_base
#print axioms AvailableChain.FGSA.Run.Internal.foldl_admitRow_base
#print axioms AvailableChain.FGSA.Run.Internal.ite_reconcile
#print axioms AvailableChain.FGSA.Run.process_base_now
#print axioms AvailableChain.FGSA.Run.process_keeps_grid
#print axioms AvailableChain.FGSA.Run.process_keeps_block
#print axioms AvailableChain.FGSA.Run.excludesS_process
#print axioms AvailableChain.FGSA.Run.Internal.foldl_vn
#print axioms AvailableChain.FGSA.Run.Internal.saGateFrom_vn
#print axioms AvailableChain.FGSA.Run.Internal.clockPre_vn
#print axioms AvailableChain.FGSA.Run.Internal.gateStep_vn
#print axioms AvailableChain.FGSA.Run.clock_vn
#print axioms AvailableChain.FGSA.Run.process_votes_subset
#print axioms AvailableChain.FGSA.Run.Internal.slotOf_mono
#print axioms AvailableChain.FGSA.Run.excludesS_clock
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_vote
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_row
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_block
#print axioms AvailableChain.FGSA.Run.excludesFixed_of_none
#print axioms AvailableChain.FGSA.Run.excludesFixed_excludesS
#print axioms AvailableChain.FGSA.Run.excludesFixed_process
#print axioms AvailableChain.FGSA.Run.excludesFixed_clock
#print axioms AvailableChain.FGSA.Run.excludes_inert_epoch
#print axioms AvailableChain.FGSA.Run.excludesFixed_inert_epoch
#print axioms AvailableChain.FGSA.Run.Epoch.weaken
#print axioms AvailableChain.FGSA.Run.epoch_of_restartFree
#print axioms AvailableChain.FGSA.Run.excludes_stable_epoch
#print axioms AvailableChain.FGSA.Run.excludesFixed_stable_epoch

-- Run-to-store bridge (T7.5)
#print axioms AvailableChain.FGSA.Run.reachable_stateBefore
#print axioms AvailableChain.FGSA.Run.reachable_stateBeforeTime
#print axioms AvailableChain.FGSA.Run.reachable_readAt
#print axioms AvailableChain.FGSA.Run.reachable_final
#print axioms AvailableChain.FGSA.Run.reachable_postClock
#print axioms AvailableChain.FGSA.Run.reachable_postTick
#print axioms AvailableChain.FGSA.Run.storeBundle_stateBefore
#print axioms AvailableChain.FGSA.Run.storeBundle_stateBeforeTime
#print axioms AvailableChain.FGSA.Run.storeBundle_readAt
#print axioms AvailableChain.FGSA.Run.storeBundle_final
#print axioms AvailableChain.FGSA.Run.storeBundle_postClock
#print axioms AvailableChain.FGSA.Run.storeBundle_postTick
#print axioms AvailableChain.FGSA.Run.inv0_stateBefore
#print axioms AvailableChain.FGSA.Run.cstoreInv_stateBefore
#print axioms AvailableChain.FGSA.Run.metaInv_stateBefore
#print axioms AvailableChain.FGSA.Run.nestOK_stateBefore
#print axioms AvailableChain.FGSA.Run.outputNesting_run
#print axioms AvailableChain.FGSA.Run.leaseBelowOutput_stateBefore
#print axioms AvailableChain.FGSA.Run.leaseBelowOutput_honest
#print axioms AvailableChain.FGSA.Run.stored_proposal_delivered
-- Hook and receipt laws (T7.7)
#print axioms AvailableChain.FGSA.Run.fgsa_clock_now
#print axioms AvailableChain.FGSA.Run.fgsaHooks
#print axioms AvailableChain.FGSA.Run.handles_wellFormed
#print axioms AvailableChain.FGSA.Run.fgsaAdmissionTime
#print axioms AvailableChain.FGSA.Run.fgsaTimely
#print axioms AvailableChain.FGSA.Run.fgsaAcceptanceInv
#print axioms AvailableChain.FGSA.Run.fgsaTrigger
#print axioms AvailableChain.FGSA.Run.fgsa_slot_threshold_iff
#print axioms AvailableChain.FGSA.Run.fgsa_round_threshold_iff
#print axioms AvailableChain.FGSA.Run.fgsaTimelyClock
#print axioms AvailableChain.FGSA.Run.fgsaAcceptance
#print axioms AvailableChain.FGSA.Run.fgsaAdmitSound
#print axioms AvailableChain.FGSA.Run.fgsaTimelyClock_clockOf
#print axioms AvailableChain.FGSA.Run.fgsaTimelyClock_actTime
#print axioms AvailableChain.FGSA.Run.fgsaTrigger_def
#print axioms AvailableChain.FGSA.Run.fgsa_trigger_of_emit
#print axioms AvailableChain.FGSA.Run.fgsa_trigger_of_accept
-- T7.9 part A
#print axioms AvailableChain.FGSA.Run.ownRecord_fold_run
#print axioms AvailableChain.FGSA.Run.fgsa_emits_head
#print axioms AvailableChain.FGSA.Run.fgsa_emits_row
#print axioms AvailableChain.FGSA.Run.fgsa_emitsAt_row
#print axioms AvailableChain.FGSA.Run.fgsa_emits_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_tick_asleep
#print axioms AvailableChain.FGSA.Run.fgsa_attest_decode
#print axioms AvailableChain.FGSA.Run.fgsa_carried_row
#print axioms AvailableChain.FGSA.Run.EmitsRow
#print axioms AvailableChain.FGSA.Run.EmittedRowsNoSlash
#print axioms AvailableChain.FGSA.Run.decodeRowObject
#print axioms AvailableChain.FGSA.Run.fgClientEvent
#print axioms AvailableChain.FGSA.Run.fgClientEvents
#print axioms AvailableChain.FGSA.Run.fgsa_tick_rows_of_seats
#print axioms AvailableChain.FGSA.Run.fgsa_client_trace_of_seats
#print axioms AvailableChain.FGSA.Run.fgsa_linked_seats
#print axioms AvailableChain.FGSA.Run.fgsa_ownSeats_bijSeat
#print axioms AvailableChain.FGSA.Run.fgsa_decode_attest_object
#print axioms AvailableChain.FGSA.Run.fgsa_client_trace
#print axioms AvailableChain.FGSA.Run.emittedRowsNoSlash

-- Schedule facts (T7.6)
#print axioms AvailableChain.FGSA.Run.fgsa_tick_time_strict
#print axioms AvailableChain.FGSA.Run.fgsa_tick_unique
#print axioms AvailableChain.FGSA.Run.fgsa_tick_total
#print axioms AvailableChain.FGSA.Run.fgsa_tick_before_delivery
#print axioms AvailableChain.FGSA.Run.fgsa_postClock_slot
#print axioms AvailableChain.FGSA.Run.fgsa_proposal_slot
#print axioms AvailableChain.FGSA.Run.fgsa_vote_slot
#print axioms AvailableChain.FGSA.Run.fgsa_action_slot_round
#print axioms AvailableChain.FGSA.Run.fgsa_gate_slot
#print axioms AvailableChain.FGSA.Run.fgsa_saved_label_origin
#print axioms AvailableChain.FGSA.Run.fgsa_gate_fresh
#print axioms AvailableChain.FGSA.Run.fgsa_gate_clock_bridge
#print axioms AvailableChain.FGSA.Run.fgsa_stateBefore_bounds
#print axioms AvailableChain.FGSA.Run.fgsa_preTick_now_lt
#print axioms AvailableChain.FGSA.Run.fgsa_release_votes_stamped
#print axioms AvailableChain.FGSA.Run.fgsa_vote_stamp_keys
#print axioms AvailableChain.FGSA.Run.fgsa_release_clockPre
#print axioms AvailableChain.FGSA.Run.fgsa_release_input_votes_stamped
#print axioms AvailableChain.FGSA.Run.fgsa_stored_block_slots
#print axioms AvailableChain.FGSA.Run.fgsa_release_count_bridge
#print axioms AvailableChain.FGSA.Run.fgsa_action_gate_time
#print axioms AvailableChain.FGSA.Run.fgsa_action_reads_gate
#print axioms AvailableChain.FGSA.Run.fgsa_gate_saved_result
#print axioms AvailableChain.FGSA.Run.fgsa_stored_block_origin
#print axioms AvailableChain.FGSA.Run.fgsa_preTick_eq_timeRead

-- AC instance (T7.15)
#print axioms AvailableChain.FGSA.Run.fgsaAC
#print axioms AvailableChain.FGSA.Run.fgsa_clockPre_gateView
#print axioms AvailableChain.FGSA.Run.fgsaAC_anchor_le_output
#print axioms AvailableChain.FGSA.Run.fgsaAC_lease_le_output
#print axioms AvailableChain.FGSA.Run.fgsaAC_gate_write
#print axioms AvailableChain.FGSA.Run.fgsaAC_output_step
#print axioms AvailableChain.FGSA.Run.fgsaAC_laws
#print axioms AvailableChain.FGSA.Run.fgsaAC_slot_gate_reads
-- Readiness producers and the generic receipt boundary.
#print axioms AvailableChain.FGSA.Run.depsS_of_not_block
#print axioms AvailableChain.FGSA.Run.depsS_of_not_proposal
#print axioms AvailableChain.FGSA.Run.fgsa_hWF_of_delivery
#print axioms AvailableChain.FGSA.Run.fgsa_hReady_of_not_block
#print axioms AvailableChain.FGSA.Run.fgsa_hReady_of_parentStored
#print axioms AvailableChain.FGSA.Run.fgsa_accepted_by_deadline_of_parentStored

-- Receipt and stamp proofs (T7.8).
#print axioms AvailableChain.FGSA.Run.blockOf?
#print axioms AvailableChain.FGSA.Run.fgsa_clockOf_nonneg
#print axioms AvailableChain.FGSA.Run.processed_stable
#print axioms AvailableChain.FGSA.Run.rowPool_provenance
#print axioms AvailableChain.FGSA.Run.fgsa_vote_stamp_source
#print axioms AvailableChain.FGSA.Run.fgsa_vote_accepted_before
#print axioms AvailableChain.FGSA.Run.fgsa_block_stamp_source
#print axioms AvailableChain.FGSA.Run.fgsa_block_accepted_before
#print axioms AvailableChain.FGSA.Run.fgsa_head_excluded_before
#print axioms AvailableChain.FGSA.Run.fgsa_head_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_head_cap_sources
#print axioms AvailableChain.FGSA.Run.fgsa_proposal_receipt
#print axioms AvailableChain.FGSA.Run.fgsa_honest_head_receipt
#print axioms AvailableChain.FGSA.Run.excludesS_honestRow_false

-- Content agreement (T7.11).
#print axioms AvailableChain.FGSA.Run.contentAgree_run

-- T7.9 Part B: row validity, proposal parent, wire check and application decoding.
#print axioms AvailableChain.FGSA.Run.fgsa_emissionRowsValid
#print axioms AvailableChain.FGSA.Run.fgsa_propose_parent_lt
#print axioms AvailableChain.FGSA.Run.honest_emit_wellFormed
#print axioms AvailableChain.FGSA.Run.decode_honest


-- Proofs/AncestorDeadlinesStore.lean and Proofs/AncestorDeadlines.lean (F1.3 clause 3)
#print axioms AvailableChain.FGSA.AncestorDeadlines.protectsUntil
#print axioms AvailableChain.FGSA.ancestorDeadlines_of_obligations_eq
#print axioms AvailableChain.FGSA.ancestorDeadlines_init
#print axioms AvailableChain.FGSA.ancestorDeadlines_reconcile
#print axioms AvailableChain.FGSA.ancestorDeadlines_process
#print axioms AvailableChain.FGSA.ancestorDeadlines_expire
#print axioms AvailableChain.FGSA.ancestorDeadlines_release
#print axioms AvailableChain.FGSA.ancestorDeadlines_clockPre
#print axioms AvailableChain.FGSA.ancestorDeadlines_clock_offGate
#print axioms AvailableChain.FGSA.ancestorDeadlines_gateStep
#print axioms AvailableChain.FGSA.ancestorDeadlines_clock
#print axioms AvailableChain.FGSA.Run.ancestorDeadlines_recordOwn
#print axioms AvailableChain.FGSA.Run.ancestorDeadlines_restore

-- F1.3 store facts, proved from the model without GridCO proof constants.
#print axioms AvailableChain.FGSA.writeKeys_deadline_cases
#print axioms AvailableChain.FGSA.writeKeys_row_cases
#print axioms AvailableChain.FGSA.gateFrom_eq_writeKeys_fgsa
#print axioms AvailableChain.FGSA.DeadlinesAtMost
#print axioms AvailableChain.FGSA.DeadlinesAtMost_def
#print axioms AvailableChain.FGSA.writeKeys_mem_of_key_fgsa

-- Statements/Slashing.lean
#print axioms AvailableChain.FGSA.Run.fgsaEvidence
#print axioms AvailableChain.FGSA.Run.fgsaSlashing

-- Proofs/Slashing.lean
#print axioms AvailableChain.FGSA.Run.fgsaSlashing_slashes_iff_of_seats
#print axioms AvailableChain.FGSA.Run.fgsaSlashing_slashes_iff_of_linked

-- Migration 06: duty uniqueness, durable emission, and R6.
#print axioms AvailableChain.FGSA.Run.fgsa_dutiesInjectiveAt
#print axioms AvailableChain.FGSA.Run.fgsa_head_singleDuty
#print axioms AvailableChain.FGSA.Run.fgsa_prop_singleDuty
#print axioms AvailableChain.FGSA.Run.fgsa_emitOnceUnder
#print axioms AvailableChain.FGSA.Run.attest_some_record
#print axioms AvailableChain.FGSA.Run.attest_none_record
#print axioms AvailableChain.FGSA.Run.attest_some_fresh
#print axioms AvailableChain.FGSA.Run.invalidForParent_mono
#print axioms AvailableChain.FGSA.Run.invalidForParent_clock
#print axioms AvailableChain.FGSA.Run.admitBlock_of_invalidForParent
#print axioms AvailableChain.FGSA.Run.invalidForParent_no_carried
#print axioms AvailableChain.FGSA.Run.propose_rowsValid
#print axioms AvailableChain.FGSA.Run.fgsa_accepted_rowsValid
#print axioms AvailableChain.FGSA.Run.fgsa_trigger_rowsValid
#print axioms AvailableChain.FGSA.Run.fgsa_trigger_invalid_false

#print axioms AvailableChain.FGSA.Run.isRowObject
#print axioms AvailableChain.FGSA.Run.isRowObject_def
#print axioms AvailableChain.FGSA.Run.fgsaDelay
#print axioms AvailableChain.FGSA.Run.fgsaDelay_def
#print axioms AvailableChain.FGSA.Run.fgsaDelay_row
#print axioms AvailableChain.FGSA.Run.fgsaDelay_nonrow
#print axioms AvailableChain.FGSA.Run.fgsaDelay_self

-- S4.2b: entry history, terminal retention, and checked admission transfer.
#print axioms AvailableChain.FGSA.Run.stored_rows_r3W
#print axioms AvailableChain.FGSA.Run.stored_chain_rowsValidW
#print axioms AvailableChain.FGSA.Run.exact_row_exclusion_checkedW
#print axioms AvailableChain.FGSA.Run.exact_row_exclusionW

-- ROOT-DIGEST: public root and content declarations.
#print axioms AvailableChain.FGSA.Run.DirectRootBlockInRun
#print axioms AvailableChain.FGSA.Run.RootBlockInRun

-- ROOT-DIGEST-2: new public W1 declarations from the signed checkpoint inventory.
namespace AvailableChain.FGSA.Run
#print axioms DirectNamedProposalInRun
#print axioms HeadTargetAtEmission
#print axioms NamedProposalInRun
#print axioms contentAgree_of_namedScope
#print axioms emitted_payload_parent_base_stored
#print axioms headTargetAtEmission_exists
#print axioms headTargetAtEmission_unique
#print axioms namedAncestor_eq
#print axioms namedOrigin_reachable
#print axioms namedProposal_eq
#print axioms namedScope_ancestor
#print axioms namedScope_collision
#print axioms namedScope_compatible_iff
#print axioms namedScope_delivered
#print axioms namedScope_erase_injective
#print axioms namedScope_held
#print axioms namedScope_preceq_iff
#print axioms proposal_trigger_in_root_scope
end AvailableChain.FGSA.Run

-- ROOT-DIGEST-2 W2: exact named origin and root resolution producers.
#print axioms AvailableChain.FGSA.Run.process_namedBodies_subset
#print axioms AvailableChain.FGSA.Run.stored_block_eq_of_root_eq
#print axioms AvailableChain.FGSA.Run.headTargetAtEmission_stored
#print axioms AvailableChain.FGSA.Run.headTargetAtEmission_scope
#print axioms AvailableChain.FGSA.Run.resolvedHead_root
#print axioms AvailableChain.FGSA.Run.headTargetAtEmission_receiver_eq
#print axioms AvailableChain.FGSA.Run.headTargetAtEmission_at_tick
#print axioms AvailableChain.FGSA.Run.headTargetAtEmission_of_stored
#print axioms AvailableChain.FGSA.Run.stored_eq_headVote
#print axioms AvailableChain.FGSA.Run.namedScope_stored_proposal
#print axioms AvailableChain.FGSA.Run.stored_named_body_delivery
#print axioms AvailableChain.FGSA.Run.stored_named_body_ancestor
#print axioms AvailableChain.FGSA.Run.namedProposalInRun_genesis_or_delivered
#print axioms AvailableChain.FGSA.Run.namedProposalInRun_origin
#print axioms AvailableChain.FGSA.Run.namedStored_eq
#print axioms AvailableChain.FGSA.RootLease.root_write_unique_keys
#print axioms AvailableChain.FGSA.RootLease.root_write_protectsUntil
#print axioms AvailableChain.FGSA.RootLease.root_expire_protectsUntil
#print axioms AvailableChain.FGSA.RootLease.root_release_protectsUntil
#print axioms AvailableChain.FGSA.Run.findByRoot_subtree
#print axioms AvailableChain.FGSA.Run.goldfishScoreOn_subtree
#print axioms AvailableChain.FGSA.Run.clockPre_headDomain
#print axioms AvailableChain.FGSA.Run.actView_score
#print axioms AvailableChain.FGSA.Run.actView_resolve_of_mem
#print axioms AvailableChain.FGSA.Run.resolvedTarget_root
#print axioms AvailableChain.FGSA.Run.resolvedTarget_of_mem
#print axioms AvailableChain.FGSA.Run.base_resolve_target
#print axioms AvailableChain.FGSA.Run.actView_resolve_target
#print axioms AvailableChain.FGSA.Run.clock_stored_block_eq
#print axioms AvailableChain.FGSA.Run.prefixSupport_body
#print axioms AvailableChain.FGSA.Run.confirmation_support_body
#print axioms AvailableChain.FGSA.Run.resolvedHead_target
#print axioms AvailableChain.FGSA.Run.resolvedHead_of_lookup
#print axioms AvailableChain.FGSA.Run.cleanSupport_domain_score
#print axioms AvailableChain.FGSA.Run.actView_target_of_resolvedHead
#print axioms AvailableChain.FGSA.Run.resolvedTarget_mem
#print axioms AvailableChain.FGSA.Run.actView_support_in_domain

#print axioms AvailableChain.FGSA.Run.fgsa_fgAction_unjoined_source_none
#print axioms AvailableChain.FGSA.Run.fgsa_clock_restartTime
#print axioms AvailableChain.FGSA.Run.fgsa_process_restartTime
#print axioms AvailableChain.FGSA.Run.fgsa_restartTime_bound
#print axioms AvailableChain.FGSA.Run.fgsa_joinedNow_of_joinedEnv
#print axioms AvailableChain.FGSA.Run.fgsa_joinedNow_of_caughtUp
#print axioms AvailableChain.FGSA.Run.fgsa_joinedNow_of_awakeClosed
#print axioms AvailableChain.FGSA.Run.fgsa_emitted_row_no_prior_processed
#print axioms AvailableChain.FGSA.Spec.spec_prune_restart_mem
#print axioms AvailableChain.FGSA.Spec.spec_prune_sleep

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

#print axioms AvailableChain.FGSA.Run.ReceiptCoverageSleepPremises
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageSleepStatement
#print axioms AvailableChain.FGSA.Run.ReceiptCoverageSleepStatement_def
