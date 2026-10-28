import Lean
open Lean

/-- Audit every declaration owned by every Consensus module, including tests
and generated declarations. Run after the six-library Lake build:
`lake env lean --run contract/CheckConsensusAxioms.lean`. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut modules : Array Name := #[]
  for file in ← (System.FilePath.mk "contract").walkDir do
    if file.extension == some "lean" then
      let parts := (file.withExtension "").components.drop 1
      if parts.head!.startsWith "Consensus" then
        modules := modules.push (parts.foldl Name.str .anonymous)
  if modules.isEmpty then
    IO.eprintln "No Consensus modules found"
    return 2
  let env ← importModules (modules.map ({ module := · })) {}
  for name in #[`Consensus.Model.holds_of_injective, `Consensus.Model.Run.rehash_trace,
      `Consensus.System.agree_of_accountable, `Consensus.EnvPoint.two_mul_card_faulty_union_lt,
      `Consensus.Model.Run.txHeld_mem_mempool, `Consensus.Model.SelSpec.admits_exists,
      `Consensus.Model.sysOf_laws, `Consensus.Model.Run.selected_of_observed,
      `Consensus.Model.Run.candidates_signer, `Consensus.Model.Run.credentials_of_causal,
      `Consensus.Shape.Tests.Model.forged_role_invalid, `Consensus.Shape.Tests.Model.unit_ticks,
      `Consensus.Model.Run.honestNeverSlashed, `Consensus.Model.sysOf_nonFraming,
      `Consensus.Model.releaseAll_eq_carried, `Consensus.Model.Run.signed_seen_released,
      `Consensus.Model.releaseAll_noConflict,
      `Consensus.Shape.Tests.Model.conflictsTrue_releases_unsigned_only,
      `Consensus.Blocks.ledgerOf_prefix, `Consensus.Blocks.patternRecurrence_of_all,
      `Consensus.Blocks.PatternRecurrence.exists_honest,
      `Consensus.Shape.Tests.Blocks.recurrence_has_teeth, `Consensus.Shape.refinement,
      `Consensus.Shape.proposalLive_txLive, `Consensus.Shape.ledgerTrace,
      `Consensus.Shape.honestProposal_payload, `Consensus.Shape.Tests.Leaks.silent,
      `Consensus.Shape.Tests.Leaks.fabricated, `Consensus.Shape.Tests.Leaks.proposeButGenesis,
      `Consensus.Shape.Tests.Leaks.conflictsTrue_silent,
      `Consensus.Shape.Tests.Leaks.recorder_live_testK,
      `Consensus.Shape.Tests.Shapes.poll_proposal_local_height,
      `Consensus.Shape.Tests.Shapes.poll_duty_every_tick,
      `Consensus.Shape.Tests.Shapes.poll_disabled_forged,
      `Consensus.Model.Run.not_slashable_of_causal, `Consensus.Shape.coverage,
      `Consensus.Shape.active_relay, `Consensus.Shape.Tests.Realizable.coverage_keeps_selection,
      `Consensus.Blocks.PatternRecurrence.exists_inside, `Consensus.Model.sysOf_log_faithful,
      `Consensus.Model.Run.held_iff_served, `Consensus.Model.sysOf_delivers_iff,
      `Consensus.CommLog.PSync.mono, `Consensus.CommLog.Delivers.reindex,
      `Consensus.CommLog.EagerFrom.delivers, `Consensus.Model.Run.SameTrace.log_eq,
      `Consensus.Shape.Tests.Realizable.allProposers_no_witness,
      `Consensus.Shape.Tests.Network.endpoint_waker,
      `Consensus.Shape.Tests.Network.endpoint_waker_silent,
      `Consensus.Shape.Tests.Network.receipt_at_deadline,
      `Consensus.Shape.Tests.Network.held_restart,
      `Consensus.Shape.Tests.Network.faithful_relayedRun,
      `Consensus.Shape.Tests.Network.faithful_receipt,
      `Consensus.Shape.Tests.Network.negative_send_covered,
      `Consensus.Shape.Tests.Network.agreesUpTo_empty_messages,
      `Consensus.CommLog.PSync.syncUntil_zero, `Consensus.CommLog.EagerFrom.syncUntil,
      `Consensus.Model.Run.log_sendsFromZero, `Consensus.Shape.Tests.Model.held_at_deadline,
      `Consensus.Shape.Tests.Model.not_held_before_relay, `Consensus.Model.canonical_run_from,
      `Consensus.Model.Run.truncate_valid, `Consensus.Model.Run.truncate_prefix,
      `Consensus.Shape.Tests.Network.silent_run_valid,
      `Consensus.Shape.Tests.Network.truncate_relayedRun, `Consensus.Good.final_agree,
      `Consensus.Good.final_safe_healthy, `Consensus.Good.persists_final_compatible,
      `Consensus.Good.sleepySafe_prefix, `Consensus.Good.healedSafe_prefix,
      `Consensus.Good.outage_prefix, `Consensus.Model.sysOf_adequate,
      `Consensus.Model.sysOf_eagerFrom, `Consensus.Params.standard_admissible,
      `Consensus.EnvPoint.HealthyOn.faultsBelow, `Consensus.CommLog.EagerFrom.psync,
      `Consensus.CommLog.Delivers.prefix, `Consensus.Trace.PrefixOf.readySafeUpTo,
      `Consensus.Trace.PrefixOf.protectedUpTo, `Consensus.Trace.PrefixOf.endCut_eq,
      `Consensus.Regime.Sleepy.of_le, `Consensus.Regime.Healthy.of_le,
      `Consensus.Regime.Outage.of_le, `Consensus.Shape.Tests.Good.false_progress_not_good,
      `Consensus.EnvPoint.etaReadyAbove_zero, `Consensus.EnvPoint.EtaReadyAbove.readyAbove,
      `Consensus.EnvPoint.EtaReadyAbove.mono, `Consensus.EnvPoint.etaSleepyOn_zero,
      `Consensus.EnvPoint.EtaSleepyOn.sleepyOn, `Consensus.EnvPoint.EtaSleepyOn.mono,
      `Consensus.EnvPoint.readyAbove_iff_union, `Consensus.EnvPoint.etaSet_mono,
      `Consensus.EnvPoint.readyAt_subset_awakeAt, `Consensus.EnvPoint.EtaReadyAbove.awakeForm,
      `Consensus.EnvPoint.HealthyOn.awakeOfAll, `Consensus.Regime.outage_eta_zero,
      `Consensus.Shape.etaReadyAbove_of_card, `Consensus.Shape.lt_card_of_card,
      `Consensus.Shape.Tests.Good.eta_sleepy_history_sensitive,
      `Consensus.Shape.Tests.Good.eta_sleepy_counts_brief,
      `Consensus.Shape.Tests.Good.eta_sleepy_startup,
      `Consensus.Shape.Tests.Good.stable_alias_final_sleepy_live,
      `Consensus.Shape.Tests.Good.no_admissible_not_adequate,
      `Consensus.Shape.Tests.Good.no_admissible_not_good,
      `Consensus.Shape.Tests.Good.empty_valid_not_adequate,
      `Consensus.Shape.Tests.Good.empty_valid_not_good,
      `Consensus.Shape.Tests.Good.excuse_true_not_good,
      `Consensus.Shape.Tests.Good.prefix_sync_then_async,
      `Consensus.Shape.Tests.Good.healthy_rotating_sleeper, `Consensus.Shape.Accepted.behaviour,
      `Consensus.Shape.Accepted.adequate, `Consensus.Blocks.PatternRecurrence.single_of_zero,
      `Consensus.Blocks.PatternRecurrence.mono, `Consensus.Blocks.PatternRecurrence.shrink,
      `Consensus.Blocks.NotReadyOn.mono, `Consensus.Blocks.NotReadyOn.shrink,
      `Consensus.Shape.shapeProgress, `Consensus.Shape.gst_le_heal,
      `Consensus.Model.canonical_run_from_causal,
      `Consensus.Shape.Tests.Leaks.recorder_live_testK_healed,
      `Consensus.Shape.Tests.Problem.local_accountability_teeth,
      `Consensus.Shape.Tests.Vacuity.allProposers_unfit,
      `Consensus.Shape.Tests.Vacuity.noProgressFit_contract,
      `Consensus.Shape.Tests.Blocks.span_guard, `Consensus.Shape.bftContract_admissible,
      `Consensus.Shape.goldilocks_progressFits, `Consensus.Shape.goldilocks_admissible,
      `Consensus.Shape.reference_bounds, `Consensus.Shape.budget_implies_V,
      `Consensus.Shape.range_head, `Consensus.Blocks.Pattern.span_le,
      `Consensus.Blocks.Pattern.span_range, `Consensus.Shape.GoldilocksTarget.goldilocks_good,
      `Consensus.Shape.GoldilocksTarget.nested,
      `Consensus.Shape.GoldilocksTarget.finalized_monotone,
      `Consensus.Shape.GoldilocksTarget.nonFraming,
      `Consensus.Shape.GoldilocksTarget.finalized_accountable,
      `Consensus.Shape.GoldilocksTarget.finalized_safe_below_third,
      `Consensus.Shape.GoldilocksTarget.confirmed_safe_sleepy,
      `Consensus.Shape.GoldilocksTarget.confirmed_safe_sleepy_prefix,
      `Consensus.Shape.GoldilocksTarget.confirmed_safe_healed,
      `Consensus.Shape.GoldilocksTarget.confirmed_safe_healed_prefix,
      `Consensus.Shape.GoldilocksTarget.confirmed_persists,
      `Consensus.Shape.GoldilocksTarget.outage_final_compatible,
      `Consensus.Shape.GoldilocksTarget.confirmed_txLive_sleepy,
      `Consensus.Shape.GoldilocksTarget.confirmed_txLive_healed,
      `Consensus.Shape.GoldilocksTarget.finalized_txLive,
      `Consensus.Shape.Tests.Goldilocks.pp223_numbers,
      `Consensus.Shape.Tests.Goldilocks.stable_is_confirmed,
      `Consensus.Shape.Tests.Goldilocks.collapse_prefix_only,
      `Consensus.Shape.Tests.Goldilocks.outageWindow_prefix_only,
      `Consensus.Shape.Tests.Goldilocks.weakPremise_inhabited, `Consensus.Shape.finalCut,
      `Consensus.Shape.finRec_span, `Consensus.Shape.final_latency_covers_window,
      `Consensus.Shape.final_heal_covers_window, `Consensus.Shape.finalRecur_delay_vs_window,
      `Consensus.Shape.streamletContract_progressFits,
      `Consensus.Shape.tendermintContract_progressFits,
      `Consensus.Shape.Tests.Vacuity.notReadyAtMost_fits, `Consensus.Shape.ProposalLive.ready,
      `Consensus.Shape.ProposalLiveReady.of_noReady, `Consensus.Blocks.NotReadyOn.readyAt_nonempty,
      `Consensus.Blocks.PatternRecurrence.reads_upTo,
      `Consensus.Shape.Tests.Realizable.rotating_notReadyOn_false,
      `Consensus.Shape.Tests.Realizable.rotating_notReadyOn_trivial,
      `Consensus.Shape.Tests.Realizable.tendermint_largeIdx_prog,
      `Consensus.Blocks.NotReadyOn.of_card_le,
      `Consensus.Shape.Tests.Realizable.rotating_proposalLive_vacuous,
      `Consensus.Shape.Tests.Vacuity.credential_forgery_excluded,
      `Consensus.Shape.Tests.Vacuity.forgedProposal_invalid,
      `Consensus.Shape.Tests.Vacuity.noService_not_accepted, `Consensus.Shape.regimes_realizable,
      `Consensus.Shape.Tests.Good.censoring_progress_rejected,
      `Consensus.Shape.Tests.Vacuity.notReadyAtMost_one_not_realizable,
      `Consensus.Shape.Tests.Vacuity.notReadyAtMost_one_not_tolerant,
      `Consensus.Shape.sleepyStress_witness, `Consensus.Shape.healthyStress_witness,
      `Consensus.Shape.goldilocks_progressTolerant,
      `Consensus.Shape.streamletContract_progressTolerant,
      `Consensus.Shape.tendermintContract_progressTolerant,
      `Consensus.Shape.Tests.Controls.ctrlK_progressTolerant,
      `Consensus.Shape.Tests.Leaks.testK_progressTolerant, `Consensus.Shape.realizable_active,
      `Consensus.Shape.RealizableActive.toRealizable, `Consensus.Shape.Accepted.good,
      `Consensus.Shape.Accepted.activeService, `Consensus.Trace.TxLive.served,
      `Consensus.Shape.sleepy_witness, `Consensus.Shape.healthy_witness,
      `Consensus.Shape.outage_witness, `Consensus.Shape.Tests.Controls.positive_controls,
      `Consensus.Shape.Tests.Controls.outage_control,
      `Consensus.Shape.Tests.Regimes.silentLog_delivers,
      `Consensus.Shape.Tests.Regimes.psync_lost_message,
      `Consensus.Shape.Tests.Regimes.outage_async_log,
      `Consensus.Shape.Tests.Regimes.sleepy_with_sleeper,
      `Consensus.Shape.Tests.Regimes.healthy_wake_at_gst,
      `Consensus.Shape.Tests.Regimes.healthy_needs_two_thirds,
      `Consensus.Shape.Tests.Regimes.faulty_third_not_healthy,
      `Consensus.Shape.Tests.Regimes.outage_times_teeth,
      `Consensus.Shape.Tests.Vacuity.standard_admissible,
      `Consensus.Shape.Tests.Vacuity.reject_theta, `Consensus.Shape.Tests.Vacuity.reject_phi,
      `Consensus.Shape.Tests.Vacuity.reject_cover, `Consensus.Shape.Tests.Vacuity.reject_alpha,
      `Consensus.Shape.Tests.Vacuity.reject_budget, `Consensus.Shape.Tests.Vacuity.reject_catchUp,
      `Consensus.Shape.Tests.Vacuity.admissibility_rejections,
      `Consensus.Shape.Tests.Vacuity.reject_alpha_any,
      `Consensus.Shape.Tests.Realizable.healed_witness_late,
      `Consensus.Shape.Tests.Realizable.outage_witness_late,
      `Consensus.Shape.Tests.Realizable.healed_witness_late_control,
      `Consensus.Shape.Tests.Realizable.outage_witness_late_control,
      `Consensus.Shape.Tests.Controls.ctrl_realizable,
      `Consensus.Model.Run.not_hashCollision_of_injective,
      `Consensus.Shape.Tests.Reformulations.goldilocksBindings_iff,
      `Consensus.Shape.Tests.Reformulations.streamletContract_eq,
      `Consensus.Shape.Tests.Reformulations.tendermintContract_eq,
      `Consensus.Shape.Tests.Reformulations.accountablySafe_iff,
      `Consensus.Shape.Tests.Problem.shortHistory_not_awake_delta,
      `Consensus.Shape.Tests.Leaks.schema_daCore] do
    unless env.contains name do
      IO.eprintln s!"Missing required theorem: {name}"
      return 2
  let mut checked := 0
  let mut bad := false
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        checked := checked + 1
        let axioms ← Core.CoreM.toIO' (collectAxioms name)
          { fileName := "CheckConsensusAxioms", fileMap := .ofString "" } { env := env }
        for ax in axioms do
          unless allowed.contains ax do
            IO.eprintln s!"Unexpected axiom: {name} uses {ax}"
            bad := true
  if checked == 0 then
    IO.eprintln "No Consensus declarations found"
    return 2
  IO.println s!"Audited {checked} declarations across {modules.size} modules; standard axioms only: {!bad}"
  return if bad then 1 else 0
