module
public import ConsensusLean.Instances.Goldilocks.Proofs.FGSafety.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACSteps.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.FGStore.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACBase.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ComposeAnyAC.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
public import ConsensusLean.Instances.Goldilocks.Proofs.Regimes.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Healing.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Reports
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.SleepyGrowth.Main

@[expose] public section

/-! # Proved Goldilocks milestones (not certified)

The finished Goldilocks milestones other than the obligations endpoint, each a theorem whose
statement is the milestone definition itself (`Instances/Goldilocks/Milestones/Statements`),
proved by its milestone proof. They are not Challenge statements and not on the trusted surface
(`docs/decisions.md` §"Trusted surface and Challenge scope"). These named theorems keep each one
proved: check.sh step 3b gates their closure (no unfinished proof, no other axiom), and the pins
below fail on a new axiom. -/

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- Goldilocks M₁, FG safety. -/
theorem Consensus.Goldilocks.FG.fGSafety : Consensus.Goldilocks.FG.FGSafety :=
  Consensus.Goldilocks.FG.fg_safety

/-- Goldilocks ACSteps, the AC step lemmas. -/
theorem Consensus.Goldilocks.SA.aCSteps : Consensus.Goldilocks.SA.ACSteps :=
  Consensus.Goldilocks.SA.acSteps

/-- Goldilocks FGStore, part 1: one FG store. -/
theorem Consensus.Goldilocks.Store.fGStoreLocal : Consensus.Goldilocks.Store.FGStoreLocal :=
  Consensus.Goldilocks.Store.fg_store_local

/-- Goldilocks FGStore, part 2 so far: FG traces (G1.4, the core of G1.10). -/
theorem Consensus.Goldilocks.Store.fGStoreTrace : Consensus.Goldilocks.Store.FGStoreTrace :=
  Consensus.Goldilocks.Store.fg_store_trace

/-- Goldilocks ACBase, the AC interface and the SA's foundations. -/
theorem Consensus.Goldilocks.SA.aCBase : Consensus.Goldilocks.SA.ACBase :=
  Consensus.Goldilocks.SA.acBase

/-- Goldilocks ACBase: the AC trace contract gives reachable states. -/
theorem Consensus.Goldilocks.localRunReachable : Consensus.Goldilocks.LocalRunReachable :=
  fun _ _ _ _ _ _ h => Consensus.Goldilocks.localRun_reachable h

/-- Goldilocks FGStore, part 3: the FG service lemmas (G1.6–G1.8, G1.9 (a)). -/
theorem Consensus.Goldilocks.Store.fGStoreService : Consensus.Goldilocks.Store.FGStoreService :=
  Consensus.Goldilocks.Store.fg_store_service

/-- Goldilocks Compose/AnyAC: the interface statements (C0.1, C0.3), for any AC. -/
theorem Consensus.Goldilocks.Compose.composeInterfaceStatements :
    Consensus.Goldilocks.Compose.ComposeInterfaceStatements :=
  Consensus.Goldilocks.Compose.compose_interface_statements

/-- Goldilocks Compose/AnyAC: the node statements (C0.2, C0.4, C0.5), for any AC. -/
theorem Consensus.Goldilocks.Compose.composeNodeStatements :
    Consensus.Goldilocks.Compose.ComposeNodeStatements :=
  Consensus.Goldilocks.Compose.compose_node_statements

/-! Goldilocks Persist: part 1, the run statements (Compose/Run), and part 2, C1.1 and its
corollary (Compose/Persist). -/

/-- Goldilocks Persist: `EventOrder`. -/
theorem Consensus.Goldilocks.Compose.eventOrder : Consensus.Goldilocks.Compose.EventOrder :=
  Consensus.Goldilocks.Compose.event_order

/-- Goldilocks Persist: `ReadyImpliesJoined`. -/
theorem Consensus.Goldilocks.Compose.readyImpliesJoined :
    Consensus.Goldilocks.Compose.ReadyImpliesJoined :=
  Consensus.Goldilocks.Compose.ready_implies_joined

/-- Goldilocks Persist: `ACProjection`. -/
theorem Consensus.Goldilocks.Compose.aCProjection : Consensus.Goldilocks.Compose.ACProjection :=
  Consensus.Goldilocks.Compose.ac_projection

/-- Goldilocks Persist: `FGProjection`. -/
theorem Consensus.Goldilocks.Compose.fGProjection : Consensus.Goldilocks.Compose.FGProjection :=
  Consensus.Goldilocks.Compose.fg_projection

/-- Goldilocks Persist: `GoldilocksACProjection`. -/
theorem Consensus.Goldilocks.Compose.goldilocksACProjection :
    Consensus.Goldilocks.Compose.GoldilocksACProjection :=
  Consensus.Goldilocks.Compose.goldilocks_ac_projection

/-- Goldilocks Persist: `GroupStatesReachable`. -/
theorem Consensus.Goldilocks.Compose.groupStatesReachable :
    Consensus.Goldilocks.Compose.GroupStatesReachable :=
  Consensus.Goldilocks.Compose.group_states_reachable

/-- Goldilocks Persist: `SyncProjection`. -/
theorem Consensus.Goldilocks.Compose.syncProjection : Consensus.Goldilocks.Compose.SyncProjection :=
  Consensus.Goldilocks.Compose.sync_projection

/-- Goldilocks Persist: `JoinedProjection`. -/
theorem Consensus.Goldilocks.Compose.joinedProjection :
    Consensus.Goldilocks.Compose.JoinedProjection :=
  Consensus.Goldilocks.Compose.joined_projection

/-! Goldilocks Regimes: the rows that hold in every run (R.7, R.8; `Statements/Regimes/Always`). -/

/-- Goldilocks Regimes: `OutputsNested`. -/
theorem Consensus.Goldilocks.Regimes.outputsNested : Consensus.Goldilocks.Regimes.OutputsNested :=
  Consensus.Goldilocks.Regimes.outputs_nested

/-- Goldilocks Regimes: `FinalizedMonotone`. -/
theorem Consensus.Goldilocks.Regimes.finalizedMonotone :
    Consensus.Goldilocks.Regimes.FinalizedMonotone :=
  Consensus.Goldilocks.Regimes.finalized_monotone

/-- Goldilocks Regimes: `OutputsValid`. -/
theorem Consensus.Goldilocks.Regimes.outputsValid : Consensus.Goldilocks.Regimes.OutputsValid :=
  Consensus.Goldilocks.Regimes.outputs_valid

/-- Goldilocks Regimes: `FinalAccountable`. -/
theorem Consensus.Goldilocks.Regimes.finalAccountable :
    Consensus.Goldilocks.Regimes.FinalAccountable :=
  Consensus.Goldilocks.Regimes.final_accountable

/-- Goldilocks Regimes: `NonFraming`. -/
theorem Consensus.Goldilocks.Regimes.nonFraming : Consensus.Goldilocks.Regimes.NonFraming :=
  Consensus.Goldilocks.Regimes.non_framing

/-- Goldilocks Regimes: `FinalizedSafe`. -/
theorem Consensus.Goldilocks.Regimes.finalizedSafe : Consensus.Goldilocks.Regimes.FinalizedSafe :=
  Consensus.Goldilocks.Regimes.finalized_safe

/-! Goldilocks Regimes: sleepy strict growth (R.2) at a committee, under growing faults
(`Results/Statements/SleepyGrowth`). -/

/-- Goldilocks Regimes: `Growing.GrowSleepy`. -/
theorem Consensus.Goldilocks.Regimes.Growing.growSleepy :
    Consensus.Goldilocks.Regimes.Growing.GrowSleepy :=
  Consensus.Goldilocks.Regimes.Growing.grow_sleepy

/-- Goldilocks Regimes: `Obligations.Growing.SleepyGrowFinite`, the finite engine growth row. -/
theorem Consensus.Goldilocks.Obligations.Growing.sleepyGrowFinite :
    Consensus.Goldilocks.Obligations.Growing.SleepyGrowFinite :=
  Consensus.Goldilocks.Obligations.Growing.sleepy_grow_finite_at

/-! Goldilocks Healing: C1.2, the AC outcome service (`Healing/Outcome`), and recovery (HR.5,
node O.1, C1.3; `Healing/Recovery`). -/

/-- Goldilocks Healing: `OutcomeService` (C1.2). -/
theorem Consensus.Goldilocks.Compose.outcomeService : Consensus.Goldilocks.Compose.OutcomeService :=
  Consensus.Goldilocks.Healing.Recovery.outcome_service

/-- Goldilocks Healing: `CacheAcceptanceAfterReset` (HR.5). -/
theorem Consensus.Goldilocks.Healing.cacheAcceptanceAfterReset :
    Consensus.Goldilocks.Healing.CacheAcceptanceAfterReset :=
  Consensus.Goldilocks.Healing.recovery_statements.cacheAcceptance

/-- Goldilocks Healing: `PatternRecovery` (node O.1). -/
theorem Consensus.Goldilocks.Healing.patternRecovery :
    Consensus.Goldilocks.Healing.PatternRecovery :=
  Consensus.Goldilocks.Healing.recovery_statements.patternRecovery

/-- Goldilocks Healing: `FinalizingCoverage` (C1.3). -/
theorem Consensus.Goldilocks.Healing.finalizingCoverage :
    Consensus.Goldilocks.Healing.FinalizingCoverage :=
  Consensus.Goldilocks.Healing.recovery_statements.finalizingCoverage

/-! ## Axiom pins -/

/-- info: 'Consensus.Goldilocks.FG.fGSafety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.FG.fGSafety

/-- info: 'Consensus.Goldilocks.SA.aCSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCSteps

/-- info: 'Consensus.Goldilocks.Store.fGStoreLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Store.fGStoreLocal

/-- info: 'Consensus.Goldilocks.Store.fGStoreTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Store.fGStoreTrace

/-- info: 'Consensus.Goldilocks.SA.aCBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCBase

/-- info: 'Consensus.Goldilocks.localRunReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.localRunReachable

/-- info: 'Consensus.Goldilocks.Store.fGStoreService' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Store.fGStoreService

/-- info: 'Consensus.Goldilocks.Compose.composeInterfaceStatements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.composeInterfaceStatements

/-- info: 'Consensus.Goldilocks.Compose.composeNodeStatements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.composeNodeStatements

/-- info: 'Consensus.Goldilocks.Compose.eventOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.eventOrder

/-- info: 'Consensus.Goldilocks.Compose.readyImpliesJoined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.readyImpliesJoined

/-- info: 'Consensus.Goldilocks.Compose.aCProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.aCProjection

/-- info: 'Consensus.Goldilocks.Compose.fGProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.fGProjection

/-- info: 'Consensus.Goldilocks.Compose.goldilocksACProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.goldilocksACProjection

/-- info: 'Consensus.Goldilocks.Compose.groupStatesReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.groupStatesReachable

/-- info: 'Consensus.Goldilocks.Compose.syncProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.syncProjection

/-- info: 'Consensus.Goldilocks.Compose.joinedProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.joinedProjection

/-- info: 'Consensus.Goldilocks.Regimes.outputsNested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.outputsNested

/-- info: 'Consensus.Goldilocks.Regimes.finalizedMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.finalizedMonotone

/-- info: 'Consensus.Goldilocks.Regimes.outputsValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.outputsValid

/-- info: 'Consensus.Goldilocks.Regimes.finalAccountable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.finalAccountable

/-- info: 'Consensus.Goldilocks.Regimes.nonFraming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.nonFraming

/-- info: 'Consensus.Goldilocks.Regimes.finalizedSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.finalizedSafe

/--
info: 'Consensus.Goldilocks.Regimes.Growing.growSleepy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.Growing.growSleepy

/--
info: 'Consensus.Goldilocks.Obligations.Growing.sleepyGrowFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Goldilocks.Obligations.Growing.sleepyGrowFinite

/-- info: 'Consensus.Goldilocks.Compose.outcomeService' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.outcomeService

/-- info: 'Consensus.Goldilocks.Healing.cacheAcceptanceAfterReset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.cacheAcceptanceAfterReset

/-- info: 'Consensus.Goldilocks.Healing.patternRecovery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.patternRecovery

/-- info: 'Consensus.Goldilocks.Healing.finalizingCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.finalizingCoverage

/-- info: 'Consensus.Goldilocks.goldilocks_continues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.goldilocks_continues

end
