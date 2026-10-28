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
  for name in #[`Consensus.Model.canonical_run, `Consensus.Model.holds_of_injective,
      `Consensus.Model.Run.rehash_trace, `Consensus.System.agree_of_accountable,
      `Consensus.Premise.extremal_realizable, `Consensus.Premise.eval_of_evalAt,
      `Consensus.EnvPoint.two_mul_card_faulty_union_lt,
      `Consensus.ProblemClaims.agree_of_accountable,
      `Consensus.Shape.Tests.Premise.provided_mismatch,
      `Consensus.Shape.Tests.Premise.protected_after_window,
      `Consensus.Shape.Tests.Premise.protected_wake_after,
      `Consensus.Model.Run.txHeld_mem_mempool, `Consensus.Model.SelSpec.admits_exists,
      `Consensus.Model.sysOf_laws, `Consensus.Model.Run.selected_of_observed,
      `Consensus.Model.Run.candidates_signer, `Consensus.Model.Run.credentials_of_causal,
      `Consensus.Shape.Tests.Model.forged_role_invalid,
      `Consensus.Shape.Tests.Model.unit_ticks,
      `Consensus.Model.Run.honestNeverSlashed, `Consensus.Model.sysOf_nonFraming,
      `Consensus.Model.releaseAll_eq_carried, `Consensus.Model.Run.signed_seen_released,
      `Consensus.Model.releaseAll_noConflict,
      `Consensus.Shape.Tests.Model.conflictsTrue_releases_unsigned_only,
      `Consensus.Blocks.ledgerOf_prefix, `Consensus.Blocks.patternRecurrence_of_all,
      `Consensus.Blocks.PatternRecurrence.exists_honest,
      `Consensus.Shape.Tests.Blocks.recurrence_has_teeth,
      `Consensus.Shape.refinement, `Consensus.Shape.proposalLive_txLive,
      `Consensus.Shape.ledgerTrace, `Consensus.Shape.honestProposal_payload,
      `Consensus.Shape.Tests.Leaks.silent, `Consensus.Shape.Tests.Leaks.fabricated,
      `Consensus.Shape.Tests.Leaks.proposeButGenesis,
      `Consensus.Shape.Tests.Leaks.conflictsTrue_silent,
      `Consensus.Shape.Tests.Leaks.recorder_live_testK,
      `Consensus.Shape.Tests.Leaks.recorder_live_testK_negGST,
      `Consensus.Shape.Tests.Shapes.poll_proposal_local_height,
      `Consensus.Shape.Tests.Shapes.poll_duty_every_tick,
      `Consensus.Shape.Tests.Shapes.poll_disabled_forged,
      `Consensus.Model.canonical_run_causal, `Consensus.Model.Run.not_slashable_of_causal,
      `Consensus.Shape.coverage, `Consensus.Shape.premise_realizable,
      `Consensus.Shape.goldilocks_realizable, `Consensus.Shape.streamlet_realizable,
      `Consensus.Shape.tendermint_realizable, `Consensus.Shape.goldilocksContract_wellFormed,
      `Consensus.Shape.active_relay,
      `Consensus.Shape.Tests.Realizable.coverage_keeps_selection,
      `Consensus.Shape.Tests.Realizable.contradictory_wf_not_realizable,
      `Consensus.Shape.Tests.Controls.positive_controls,
      `Consensus.Shape.Tests.Controls.resilience_control,
      `Consensus.Shape.Tests.Vacuity.zero_catchUp_not_shapeClaims,
      `Consensus.Shape.Tests.Vacuity.escape_zero_rejected,
      `Consensus.Shape.Tests.Vacuity.recoveryEscape_zero_rejected,
      `Consensus.Shape.Tests.Vacuity.accountable_zero_rejected,
      `Consensus.Shape.Tests.Vacuity.stable_without_recovery_rejected,
      `Consensus.Shape.Tests.Vacuity.noSync_live_rejected,
      `Consensus.Shape.Tests.Vacuity.noSync_recovery_rejected,
      `Consensus.Shape.Tests.Vacuity.goldilocks_structural,
      `Consensus.Shape.Tests.Vacuity.credential_forgery_excluded,
      `Consensus.Shape.Tests.Vacuity.forgedProposal_invalid,
      `Consensus.Premise.TimesHold.shift, `Consensus.Premise.sleeper_realizable,
      `Consensus.Premise.eventually_evalEnv, `Consensus.Blocks.PatternRecurrence.exists_inside,
      `Consensus.Shape.witness_at, `Consensus.Shape.resilience_realizable,
      `Consensus.Shape.delivers, `Consensus.Shape.Accepted.problemClaims,
      `Consensus.Shape.Accepted.serves_and_delivers,
      `Consensus.Shape.Tests.Premise.horizonCap_rejected,
      `Consensus.Shape.Tests.Premise.protectedAtCap_rejected,
      `Consensus.Shape.Tests.Premise.gstCap_rejected,
      `Consensus.Shape.Tests.Premise.atHorizon_rejected,
      `Consensus.Shape.Tests.Premise.horizonStart_rejected,
      `Consensus.Shape.Tests.Premise.outageWindow_shift,
      `Consensus.Shape.Tests.Vacuity.noService_not_accepted,
      `Consensus.Shape.Tests.Realizable.confinedOutage_not_realizable,
      `Consensus.Model.sysOf_log_faithful, `Consensus.Model.Run.held_iff_served,
      `Consensus.Model.sysOf_delivers_iff, `Consensus.CommLog.PSync.mono,
      `Consensus.CommLog.Delivers.reindex, `Consensus.CommLog.EagerFrom.delivers,
      `Consensus.Model.Run.delivers_of_eager, `Consensus.Model.Run.SameTrace.log_eq,
      `Consensus.Shape.Tests.Realizable.allProposers_no_witness,
      `Consensus.Shape.Tests.Network.endpoint_waker,
      `Consensus.Shape.Tests.Network.endpoint_waker_silent,
      `Consensus.Shape.Tests.Network.receipt_at_deadline,
      `Consensus.Shape.Tests.Network.held_restart,
      `Consensus.Shape.Tests.Network.psync_mono_instance,
      `Consensus.Shape.Tests.Network.faithful_relayedRun,
      `Consensus.Shape.Tests.Network.faithful_receipt,
      `Consensus.Shape.Tests.Network.negative_send_covered,
      `Consensus.Shape.Tests.Network.agreesUpTo_empty_messages,
      `Consensus.CommLog.PSync.syncUntil_zero, `Consensus.CommLog.EagerFrom.syncUntil,
      `Consensus.Model.Run.log_sendsFromZero,
      `Consensus.Shape.Tests.Model.held_at_deadline,
      `Consensus.Shape.Tests.Model.not_held_before_relay,
      `Consensus.Model.canonical_run_from, `Consensus.Model.Run.truncate_valid,
      `Consensus.Model.Run.truncate_prefix,
      `Consensus.Shape.Tests.Network.silent_run_valid,
      `Consensus.Shape.Tests.Network.truncate_relayedRun,
      `Consensus.Good.final_agree, `Consensus.Good.final_safe_healthy,
      `Consensus.Good.persists_final_compatible, `Consensus.Good.sleepySafe_prefix,
      `Consensus.Good.healedSafe_prefix, `Consensus.Good.outage_prefix,
      `Consensus.Model.sysOf_adequate, `Consensus.Model.sysOf_eagerFrom,
      `Consensus.Params.standard_admissible, `Consensus.EnvPoint.HealthyOn.faultsBelow,
      `Consensus.CommLog.EagerFrom.psync, `Consensus.CommLog.Delivers.prefix,
      `Consensus.Trace.PrefixOf.readySafeUpTo, `Consensus.Trace.PrefixOf.protectedUpTo,
      `Consensus.Trace.PrefixOf.endCut_eq,
      `Consensus.Regime.Sleepy.of_le, `Consensus.Regime.Healthy.of_le,
      `Consensus.Regime.Outage.of_le,
      `Consensus.Shape.Tests.Good.false_progress_not_good,
      `Consensus.Shape.Tests.Good.empty_valid_not_good,
      `Consensus.Shape.Tests.Good.excuse_true_not_good,
      `Consensus.Shape.Tests.Good.prefix_sync_then_async,
      `Consensus.Shape.Tests.Good.healthy_rotating_sleeper] do
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
