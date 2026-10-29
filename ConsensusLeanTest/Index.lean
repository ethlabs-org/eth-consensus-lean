module
public import ConsensusLeanTest.Blocks
public import ConsensusLeanTest.Common
public import ConsensusLeanTest.Controls
public import ConsensusLeanTest.Gaps
public import ConsensusLeanTest.Goldilocks
public import ConsensusLeanTest.Good
public import ConsensusLeanTest.Leaks
public import ConsensusLeanTest.Lift
public import ConsensusLeanTest.Model
public import ConsensusLeanTest.Network
public import ConsensusLeanTest.Problem
public import ConsensusLeanTest.Realizable
public import ConsensusLeanTest.Regimes
public import ConsensusLeanTest.Shape
public import ConsensusLeanTest.Support
public import ConsensusLeanTest.Vacuity
public import ConsensusLean
public import Solution

/-! # Name index

Every name a reviewer or the README relies on, checked to exist by the build
(`example := @X`). This checks **existence only**, not strength: what a test
proves is its own statement (compiled in the gate). The declaration check
(`scripts/check.sh`, EthLib check-decls) scans every declaration of every module.

Kept here: the endpoint theorems, every theorem of the rejecting-test files
(`Problem`, `Network`, `Regimes`, `Good`, `Leaks`, `Vacuity`), the names cited
by `Gaps` and the Goldilocks sheet, and the former audit list. -/

/-! ## Endpoints -/

example := @Consensus.Review.acceptedGood
example := @Consensus.Review.regimesRealizable
example := @Consensus.Review.logFaithful
example := @Consensus.Review.heldIffServed
example := @Consensus.Shape.Accepted.good
example := @Consensus.Shape.Accepted.activeService
example := @Consensus.Shape.refinement
example := @Consensus.Shape.regimes_realizable
example := @Consensus.Model.sysOf_adequate

/-! ## L0 (problem and facts) -/

example := @Consensus.CommLog.Delivers.prefix
example := @Consensus.CommLog.Delivers.reindex
example := @Consensus.CommLog.EagerFrom.delivers
example := @Consensus.CommLog.EagerFrom.psync
example := @Consensus.CommLog.EagerFrom.syncUntil
example := @Consensus.CommLog.PSync.mono
example := @Consensus.CommLog.PSync.syncUntil_zero
example := @Consensus.EnvPoint.EtaReadyAbove.awakeForm
example := @Consensus.EnvPoint.EtaReadyAbove.mono
example := @Consensus.EnvPoint.EtaReadyAbove.readyAbove
example := @Consensus.EnvPoint.EtaSleepyOn.mono
example := @Consensus.EnvPoint.EtaSleepyOn.sleepyOn
example := @Consensus.EnvPoint.HealthyOn.awakeOfAll
example := @Consensus.EnvPoint.HealthyOn.faultsBelow
example := @Consensus.EnvPoint.etaReadyAbove_zero
example := @Consensus.EnvPoint.etaSet_mono
example := @Consensus.EnvPoint.etaSleepyOn_zero
example := @Consensus.EnvPoint.readyAbove_iff_union
example := @Consensus.EnvPoint.readyAt_subset_awakeAt
example := @Consensus.Good.final_agree
example := @Consensus.Good.final_safe_healthy
example := @Consensus.Good.healedSafe_prefix
example := @Consensus.Good.outage_prefix
example := @Consensus.Good.persists_final_compatible
example := @Consensus.Good.served
example := @Consensus.Good.sleepySafe_prefix
example := @Consensus.Params.standard_admissible
example := @Consensus.System.Healthy.of_le
example := @Consensus.System.Outage.of_le
example := @Consensus.System.Sleepy.of_le
example := @Consensus.System.outage_eta_zero
example := @Consensus.System.cDur_of_catchUp
example := @Consensus.System.agree_of_accountable
example := @Consensus.Trace.PrefixOf.endCut_eq
example := @Consensus.Trace.PrefixOf.protectedUpTo
example := @Consensus.Trace.PrefixOf.readySafeUpTo
example := @Consensus.Trace.TxLive.served

example := @Consensus.System.Sleepy
example := @Consensus.System.Healthy
example := @Consensus.System.Outage
example := @Consensus.System.cDur
example := @Consensus.System.heal
example := @Consensus.System.ready
example := @Consensus.System.lat
example := @Consensus.Behaviour.healthyLive
example := @Consensus.Behaviour.finalAccountable
example := @Consensus.Trace.ReadySafeUpTo
example := @Consensus.CommLog.SendsFromZero

/-! ## L1 (model and proofs) -/
example := @Consensus.Model.Run.mem_viewIdx_iff
example := @Consensus.Model.Run.seen_source
example := @Consensus.Model.Run.viewIdx_mono

example := @Consensus.Model.Obj.Contains.trans
example := @Consensus.Model.Run.SameTrace.log_eq
example := @Consensus.Model.Run.candidates_signer
example := @Consensus.Model.Run.credentials_of_causal
example := @Consensus.Model.Run.held_iff_served
example := @Consensus.Model.Run.honestNeverSlashed
example := @Consensus.Model.Run.log_sendsFromZero
example := @Consensus.Model.Run.not_hashCollision_of_injective
example := @Consensus.Model.Run.not_slashable_of_causal
example := @Consensus.Model.Run.rehash_trace
example := @Consensus.Model.Run.selected_of_observed
example := @Consensus.Model.Run.signed_seen_released
example := @Consensus.Model.Run.truncate_prefix
example := @Consensus.Model.Run.truncate_valid
example := @Consensus.Model.Run.txHeld_mem_mempool
example := @Consensus.Model.SelSpec.admits_exists
example := @Consensus.Model.canonical_run_from
example := @Consensus.Model.canonical_run_from_causal
example := @Consensus.Model.holds_of_injective
example := @Consensus.Model.mem_honestEvidence_iff
example := @Consensus.Model.protects
example := @Consensus.Model.protects_iff
example := @Consensus.Model.releaseAll_eq_carried
example := @Consensus.Model.releaseAll_noConflict
example := @Consensus.Model.sysOf_delivers_iff
example := @Consensus.Model.sysOf_eagerFrom
example := @Consensus.Model.sysOf_laws
example := @Consensus.Model.sysOf_log_faithful
example := @Consensus.Model.sysOf_nonFraming

/-! ## Blocks -/

example := @Consensus.Blocks.NotReadyOn.mono
example := @Consensus.Blocks.NotReadyOn.of_card_le
example := @Consensus.Blocks.NotReadyOn.readyAt_nonempty
example := @Consensus.Blocks.NotReadyOn.shrink
example := @Consensus.Blocks.Pattern.range
example := @Consensus.Blocks.Pattern.span_le
example := @Consensus.Blocks.Pattern.span_range
example := @Consensus.Blocks.PatternRecurrence.exists_honest
example := @Consensus.Blocks.PatternRecurrence.exists_inside
example := @Consensus.Blocks.PatternRecurrence.mono
example := @Consensus.Blocks.PatternRecurrence.reads_upTo
example := @Consensus.Blocks.PatternRecurrence.shrink
example := @Consensus.Blocks.PatternRecurrence.single_of_zero
example := @Consensus.Blocks.ledgerOf_prefix
example := @Consensus.Blocks.patternRecurrence_of_all
example := @Consensus.Blocks.patternRecurrence_of_periodic
example := @Consensus.Blocks.Recurrence.exists_bad_slot
example := @Consensus.Blocks.Recurrence.pattern_good
example := @Consensus.Blocks.Recurrence.BadSlotSlack

/-! ## L2 (shape) and test values -/

example := @Consensus.Shape.Accepted.behaviour
example := @Consensus.Shape.ProgressFits
example := @Consensus.Shape.ProgressReq.Fits
example := @Consensus.Shape.ProgressReq.Tolerates
example := @Consensus.Shape.ProgressTolerant
example := @Consensus.Shape.ProposalLive.ready
example := @Consensus.Shape.ProposalLiveReady.of_noReady
example := @Consensus.Shape.RealizableActive.toRealizable
example := @Consensus.Shape.BadProposerEvery
example := @Consensus.Shape.badSlotRole
example := @Consensus.Shape.badSel
example := @Consensus.Shape.badSel_admits
example := @Consensus.Shape.badSel_bad
example := @Consensus.Shape.badSel_good_mem
example := @Consensus.Shape.bad_selection
example := @Consensus.Shape.ShapeClaimsAt
example := @Consensus.Shape.active_relay
example := @Consensus.Shape.bftContract_admissible
example := @Consensus.Shape.coverage
example := @Consensus.Shape.etaReadyAbove_of_card
example := @Consensus.Shape.gst_le_heal
example := @Consensus.Shape.healthy_witness
example := @Consensus.Shape.healthy_witness_sel
example := @Consensus.Shape.real_run_sel
example := @Consensus.Shape.honestProposal_payload
example := @Consensus.Shape.ledgerTrace
example := @Consensus.Shape.one_lt_beta_mul_card
example := @Consensus.Shape.outage_witness
example := @Consensus.Shape.proposalLive_txLive
example := @Consensus.Shape.shapeProgress
example := @Consensus.Shape.sleepyStress_witness
example := @Consensus.Shape.sleepy_witness
example := @Consensus.Shape.streamletContract_progressFits
example := @Consensus.Shape.streamletContract_progressTolerant
example := @Consensus.Shape.tendermintContract_progressFits
example := @Consensus.Shape.tendermintContract_progressTolerant

/-! ## Goldilocks (values and sheet) -/

example := @Consensus.EnvPoint.two_mul_card_faulty_union_lt
example := @Consensus.Shape.GoldilocksExtraAt
example := @Consensus.Shape.GoldilocksExtraAt.crossNest
example := @Consensus.Shape.GoldilocksExtraAt.finalFirst
example := @Consensus.Shape.GoldilocksExtraAt.finalRecur
example := @Consensus.Shape.GoldilocksExtraAt.growHealed
example := @Consensus.Shape.GoldilocksExtraAt.growSleepy
example := @Consensus.Shape.GoldilocksExtraAt.includeHealed
example := @Consensus.Shape.GoldilocksExtraAt.includeSleepy
example := @Consensus.Shape.GoldilocksExtraAt.liveDC
example := @Consensus.Shape.GoldilocksExtraAt.outageWindow
example := @Consensus.Shape.GoldilocksExtraAt.weakCrossNest
example := @Consensus.Shape.GoldilocksExtraAt.weakGrow
example := @Consensus.Shape.GoldilocksExtraAt.weakInclude
example := @Consensus.Shape.GoldilocksExtraAt.weakSafe
example := @Consensus.Shape.GoldilocksTarget.confirmed_persists
example := @Consensus.Shape.GoldilocksTarget.confirmed_safe_healed
example := @Consensus.Shape.GoldilocksTarget.confirmed_safe_healed_prefix
example := @Consensus.Shape.GoldilocksTarget.confirmed_safe_sleepy
example := @Consensus.Shape.GoldilocksTarget.confirmed_safe_sleepy_prefix
example := @Consensus.Shape.GoldilocksTarget.confirmed_txLive_healed
example := @Consensus.Shape.GoldilocksTarget.confirmed_txLive_sleepy
example := @Consensus.Shape.GoldilocksTarget.finalized_accountable
example := @Consensus.Shape.GoldilocksTarget.finalized_monotone
example := @Consensus.Shape.GoldilocksTarget.finalized_safe_below_third
example := @Consensus.Shape.GoldilocksTarget.finalized_txLive
example := @Consensus.Shape.GoldilocksTarget.goldilocks_good
example := @Consensus.Shape.GoldilocksTarget.nested
example := @Consensus.Shape.GoldilocksTarget.nonFraming
example := @Consensus.Shape.GoldilocksTarget.outage_final_compatible
example := @Consensus.Shape.budget_implies_V
example := @Consensus.Shape.finRec_span
example := @Consensus.Shape.finalCut
example := @Consensus.Shape.finalRecur_delay_vs_window
example := @Consensus.Shape.final_heal_covers_window
example := @Consensus.Shape.final_latency_covers_window
example := @Consensus.Shape.gHealFin_eq
example := @Consensus.Shape.gHeal_eq
example := @Consensus.Shape.gReady_eq
example := @Consensus.Shape.gc_eq
example := @Consensus.Shape.goldilocksContract
example := @Consensus.Shape.goldilocks_admissible
example := @Consensus.Shape.goldilocks_progressFits
example := @Consensus.Shape.goldilocks_progressTolerant
example := @Consensus.Shape.range_head
example := @Consensus.Shape.reference_bounds

/-! ## Tests: Blocks -/

example := @Consensus.Shape.Tests.Blocks.recurrence_has_teeth
example := @Consensus.Shape.Tests.Blocks.span_guard

/-! ## Tests: Controls -/

example := @Consensus.Shape.Tests.Controls.ctrlK_progressTolerant
example := @Consensus.Shape.Tests.Controls.ctrl_realizable
example := @Consensus.Shape.Tests.Controls.outage_control
example := @Consensus.Shape.Tests.Controls.positive_controls

/-! ## Tests: Goldilocks -/

example := @Consensus.Shape.Tests.Goldilocks.collapse_prefix_only
example := @Consensus.Shape.Tests.Goldilocks.outageWindow_prefix_only
example := @Consensus.Shape.Tests.Goldilocks.pp223_numbers
example := @Consensus.Shape.Tests.Goldilocks.stable_is_confirmed
example := @Consensus.Shape.Tests.Goldilocks.weakPremise_inhabited

/-! ## Tests: Good -/

example := @Consensus.Shape.Tests.Good.briefPoint_faulty
example := @Consensus.Shape.Tests.Good.briefPoint_readyAt
example := @Consensus.Shape.Tests.Good.censoring_progress_rejected
example := @Consensus.Shape.Tests.Good.empty_valid_not_adequate
example := @Consensus.Shape.Tests.Good.empty_valid_not_good
example := @Consensus.Shape.Tests.Good.eta_sleepy_counts_brief
example := @Consensus.Shape.Tests.Good.eta_sleepy_history_sensitive
example := @Consensus.Shape.Tests.Good.eta_sleepy_startup
example := @Consensus.Shape.Tests.Good.excuse_true_not_good
example := @Consensus.Shape.Tests.Good.false_progress_not_good
example := @Consensus.Shape.Tests.Good.healthy_rotating_sleeper
example := @Consensus.Shape.Tests.Good.no_admissible_not_adequate
example := @Consensus.Shape.Tests.Good.no_admissible_not_good
example := @Consensus.Shape.Tests.Good.prefixPoint_faulty
example := @Consensus.Shape.Tests.Good.prefixPoint_readyAt
example := @Consensus.Shape.Tests.Good.prefix_sync_then_async
example := @Consensus.Shape.Tests.Good.rotPoint_awake_card
example := @Consensus.Shape.Tests.Good.rotPoint_faulty
example := @Consensus.Shape.Tests.Good.stable_alias_final_sleepy_live
example := @Consensus.Shape.Tests.Good.startPoint_awakeIn
example := @Consensus.Shape.Tests.Good.startPoint_faulty
example := @Consensus.Shape.Tests.Good.startPoint_readyAt

/-! ## Tests: Leaks -/

example := @Consensus.Shape.Tests.Leaks.conflictsTrue_silent
example := @Consensus.Shape.Tests.Leaks.env_ready
example := @Consensus.Shape.Tests.Leaks.fabricated
example := @Consensus.Shape.Tests.Leaks.familyC_mono
example := @Consensus.Shape.Tests.Leaks.familyC_state
example := @Consensus.Shape.Tests.Leaks.goodHash_injective
example := @Consensus.Shape.Tests.Leaks.proposeButGenesis
example := @Consensus.Shape.Tests.Leaks.recorder_live
example := @Consensus.Shape.Tests.Leaks.recorder_live_testK
example := @Consensus.Shape.Tests.Leaks.recorder_live_testK_healed
example := @Consensus.Shape.Tests.Leaks.refuted_of_empty
example := @Consensus.Shape.Tests.Leaks.releaseAll_mono
example := @Consensus.Shape.Tests.Leaks.releaseAll_record
example := @Consensus.Shape.Tests.Leaks.releaseAll_state
example := @Consensus.Shape.Tests.Leaks.schema_daCore
example := @Consensus.Shape.Tests.Leaks.silent
example := @Consensus.Shape.Tests.Leaks.testK_progressTolerant
example := @Consensus.Shape.Tests.Leaks.testSel_admits

/-! ## Tests: Model -/

example := @Consensus.Shape.Tests.Model.conflictsTrue_releases_unsigned_only
example := @Consensus.Shape.Tests.Model.forged_role_invalid
example := @Consensus.Shape.Tests.Model.held_at_deadline
example := @Consensus.Shape.Tests.Model.not_held_before_relay
example := @Consensus.Shape.Tests.Model.unit_ticks

/-! ## Tests: Network -/

example := @Consensus.Shape.Tests.Network.agreesUpTo_empty_messages
example := @Consensus.Shape.Tests.Network.waker_within_bound
example := @Consensus.Shape.Tests.Network.waker_within_bound_silent
example := @Consensus.Shape.Tests.Network.waker_not_instant
example := @Consensus.Shape.Tests.Network.faithful_receipt
example := @Consensus.Shape.Tests.Network.faithful_relayedRun
example := @Consensus.Shape.Tests.Network.held0
example := @Consensus.Shape.Tests.Network.held1
example := @Consensus.Shape.Tests.Network.held_all
example := @Consensus.Shape.Tests.Network.held_restart
example := @Consensus.Shape.Tests.Network.negative_send_covered
example := @Consensus.Shape.Tests.Network.receipt_at_deadline
example := @Consensus.Shape.Tests.Network.silent_not_psync
example := @Consensus.Shape.Tests.Network.silent_run_valid
example := @Consensus.Shape.Tests.Network.tickedRun_valid
example := @Consensus.Shape.Tests.Network.truncate_relayedRun

/-! ## Tests: Problem -/

example := @Consensus.Shape.Tests.Problem.finalized_stable_not_nested
example := @Consensus.Shape.Tests.Problem.inCuts_zero
example := @Consensus.Shape.Tests.Problem.incompatible_laws
example := @Consensus.Shape.Tests.Problem.incompatible_not_agree
example := @Consensus.Shape.Tests.Problem.init_rollback_not_monotone
example := @Consensus.Shape.Tests.Problem.local_accountability_teeth
example := @Consensus.Shape.Tests.Problem.omitted_laws
example := @Consensus.Shape.Tests.Problem.omitted_not_txLive
example := @Consensus.Shape.Tests.Problem.oneSource_submitted
example := @Consensus.Shape.Tests.Problem.other_node_no_submission
example := @Consensus.Shape.Tests.Problem.rollback_laws
example := @Consensus.Shape.Tests.Problem.rollback_not_monotone
example := @Consensus.Shape.Tests.Problem.shortHistory_not_awake_delta
example := @Consensus.Shape.Tests.Problem.shortHistory_ready
example := @Consensus.Shape.Tests.Problem.sleeping_source_not_submitted
example := @Consensus.Shape.Tests.Problem.stable_confirmed_nested

/-! ## Tests: Realizable -/

example := @Consensus.Shape.Tests.Realizable.allProposers_no_witness
example := @Consensus.Shape.Tests.Realizable.coverage_keeps_selection
example := @Consensus.Shape.Tests.Realizable.healed_witness_late
example := @Consensus.Shape.Tests.Realizable.healed_witness_late_control
example := @Consensus.Shape.Tests.Realizable.outage_witness_late
example := @Consensus.Shape.Tests.Realizable.outage_witness_late_control
example := @Consensus.Shape.Tests.Realizable.rotating_notReadyOn_false
example := @Consensus.Shape.Tests.Realizable.rotating_notReadyOn_trivial
example := @Consensus.Shape.Tests.Realizable.rotating_proposalLive_vacuous
example := @Consensus.Shape.Tests.Realizable.tendermint_largeIdx_prog

/-! ## Tests: Regimes -/

example := @Consensus.Shape.Tests.Regimes.faulty_third_not_healthy
example := @Consensus.Shape.Tests.Regimes.healthy_needs_full_participation
example := @Consensus.Shape.Tests.Regimes.healthy_wake_at_gst
example := @Consensus.Shape.Tests.Regimes.logA_held
example := @Consensus.Shape.Tests.Regimes.outage_async_log
example := @Consensus.Shape.Tests.Regimes.outage_times_teeth
example := @Consensus.Shape.Tests.Regimes.psync_lost_message
example := @Consensus.Shape.Tests.Regimes.ptL_no_wake
example := @Consensus.Shape.Tests.Regimes.ptS_faulty
example := @Consensus.Shape.Tests.Regimes.ptS_readyAbove
example := @Consensus.Shape.Tests.Regimes.ptS_readyAt
example := @Consensus.Shape.Tests.Regimes.silentLog_delivers
example := @Consensus.Shape.Tests.Regimes.sleepy_with_sleeper

/-! ## Tests: Shapes -/

example := @Consensus.Shape.Tests.Shapes.poll_disabled_forged
example := @Consensus.Shape.Tests.Shapes.poll_duty_every_tick
example := @Consensus.Shape.Tests.Shapes.poll_proposal_local_height

/-! ## Tests: Vacuity -/

example := @Consensus.Shape.Tests.Vacuity.admissibility_rejections
example := @Consensus.Shape.Tests.Vacuity.allProposers_unfit
example := @Consensus.Shape.Tests.Vacuity.credential_forgery_excluded
example := @Consensus.Shape.Tests.Vacuity.forgedProposal_invalid
example := @Consensus.Shape.Tests.Vacuity.noProgressFit_contract
example := @Consensus.Shape.Tests.Vacuity.noService_not_accepted
example := @Consensus.Shape.Tests.Vacuity.notReadyAtMost_fits
example := @Consensus.Shape.Tests.Vacuity.recur_noSlack_not_tolerant
example := @Consensus.Shape.Tests.Vacuity.recur_single_one_not_tolerant
example := @Consensus.Shape.Tests.Vacuity.recur_single_one_bad_slots
example := @Consensus.Shape.Tests.Vacuity.notReadyAtMost_one_not_realizable
example := @Consensus.Shape.Tests.Vacuity.notReadyAtMost_below_not_realizable
example := @Consensus.Shape.Tests.Vacuity.notReadyAtMost_one_not_tolerant
example := @Consensus.Shape.Tests.Vacuity.reject_alpha
example := @Consensus.Shape.Tests.Vacuity.reject_alpha_any
example := @Consensus.Shape.Tests.Vacuity.reject_budget
example := @Consensus.Shape.Tests.Vacuity.reject_catchUp
example := @Consensus.Shape.Tests.Vacuity.reject_cover
example := @Consensus.Shape.Tests.Vacuity.reject_beta
example := @Consensus.Shape.Tests.Vacuity.reject_theta
example := @Consensus.Shape.Tests.Vacuity.standard_admissible
