module
public import ConsensusLean.Instances.Goldilocks.Proofs.FGSafety.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACSteps.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.FGStore.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACBase.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ComposeAnyAC.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Persist.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Regimes.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Service.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Healing.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Reports
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Main

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
  Consensus.Goldilocks.localRun_reachable

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

/-- Goldilocks Persist: `HonestFastConfirmationsPersist`. -/
theorem Consensus.Goldilocks.Compose.honestFastConfirmationsPersist :
    Consensus.Goldilocks.Compose.HonestFastConfirmationsPersist :=
  Consensus.Goldilocks.Compose.honest_fast_confirmations_persist

/-- Goldilocks Persist: `RecentSourceNextVote`. -/
theorem Consensus.Goldilocks.Compose.recentSourceNextVote :
    Consensus.Goldilocks.Compose.RecentSourceNextVote :=
  Consensus.Goldilocks.Compose.recent_source_next_vote

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

/-! Goldilocks Regimes: the sleepy rows (R.1, R.2; `Statements/Regimes/Sleepy`). -/

/-- Goldilocks Regimes: `SleepySafe`. -/
theorem Consensus.Goldilocks.Regimes.sleepySafe : Consensus.Goldilocks.Regimes.SleepySafe :=
  Consensus.Goldilocks.Regimes.sleepy_safe


/-- Goldilocks Regimes: `IncludeSleepy`. -/
theorem Consensus.Goldilocks.Regimes.includeSleepy : Consensus.Goldilocks.Regimes.IncludeSleepy :=
  Consensus.Goldilocks.Regimes.include_sleepy

/-- Goldilocks Regimes: `GrowSleepy`. -/
theorem Consensus.Goldilocks.Regimes.growSleepy : Consensus.Goldilocks.Regimes.GrowSleepy :=
  Consensus.Goldilocks.Regimes.grow_sleepy

/-! Goldilocks Service: the available chain after C1.1 (A1.6, A1.7; `Compose/Service`). -/

/-- Goldilocks Service: `HeadExtendsRecord`. -/
theorem Consensus.Goldilocks.Compose.headExtendsRecord :
    Consensus.Goldilocks.Compose.HeadExtendsRecord :=
  Consensus.Goldilocks.Compose.head_extends_record

/-- Goldilocks Service: `Inclusion`. -/
theorem Consensus.Goldilocks.Compose.inclusion : Consensus.Goldilocks.Compose.Inclusion :=
  Consensus.Goldilocks.Compose.inclusion_sleepy

/-! Goldilocks Healing: the AC healing statements (H.1, its corollary, H.2; `Healing/AC`), the run
statements (HR.1–HR.4, H.2 on the run, H.3, H.4; `Healing/Run`) and the phase service (HS.1–HS.4;
`Healing/Service`), each a field of its proved bundle in `Proofs/Healing/Main`. -/

/-- Goldilocks Healing: `ACHealingStandaloneAll` (H.1). -/
theorem Consensus.Goldilocks.SA.aCHealingStandaloneAll :
    Consensus.Goldilocks.SA.ACHealingStandaloneAll :=
  fun sp h => Consensus.Goldilocks.Healing.healing_ac_statements.standalone sp h

/-- Goldilocks Healing: `ACHealingStandaloneCorollaryAll` (H.1, corollary). -/
theorem Consensus.Goldilocks.SA.aCHealingStandaloneCorollaryAll :
    Consensus.Goldilocks.SA.ACHealingStandaloneCorollaryAll :=
  fun sp h => Consensus.Goldilocks.SA.ac_healing_standalone_corollary sp h

/-- Goldilocks Healing: `ACHealingStandaloneTightAll` (H.1 at `ḡ + (8k + 4)Δ`). -/
theorem Consensus.Goldilocks.SA.aCHealingStandaloneTightAll :
    Consensus.Goldilocks.SA.ACHealingStandaloneTightAll :=
  fun sp h => Consensus.Goldilocks.SA.ac_healing_standalone_tight sp h

/-- Goldilocks Healing: `ACHealingStandaloneTightCorollaryAll` (H.1 at `ḡ + (8k + 4)Δ`,
corollary: proposal-block inclusion). -/
theorem Consensus.Goldilocks.SA.aCHealingStandaloneTightCorollaryAll :
    Consensus.Goldilocks.SA.ACHealingStandaloneTightCorollaryAll :=
  fun sp h => Consensus.Goldilocks.SA.ac_healing_standalone_tight_corollary sp h

/-- Goldilocks Healing: `ACInclusionAll` (H.2). -/
theorem Consensus.Goldilocks.SA.aCInclusionAll : Consensus.Goldilocks.SA.ACInclusionAll :=
  fun sp h => Consensus.Goldilocks.Healing.healing_ac_statements.inclusion sp h

/-- Goldilocks Healing: `CutAndReset` (HR.1). -/
theorem Consensus.Goldilocks.Healing.cutAndReset : Consensus.Goldilocks.Healing.CutAndReset :=
  Consensus.Goldilocks.Healing.healing_run_statements.cutAndReset

/-- Goldilocks Healing: `PhaseCountAll` (HR.2). -/
theorem Consensus.Goldilocks.Healing.phaseCountAll : Consensus.Goldilocks.Healing.PhaseCountAll :=
  Consensus.Goldilocks.Healing.healing_run_statements.phaseCount

/-- Goldilocks Healing: `ResetExistence` (HR.3). -/
theorem Consensus.Goldilocks.Healing.resetExistence :
    Consensus.Goldilocks.Healing.ResetExistence :=
  Consensus.Goldilocks.Healing.healing_run_statements.resetExistence

/-- Goldilocks Healing: `HeightScopedRetention` (HR.4). -/
theorem Consensus.Goldilocks.Healing.heightScopedRetention :
    Consensus.Goldilocks.Healing.HeightScopedRetention :=
  Consensus.Goldilocks.Healing.healing_run_statements.heightScopedRetention

/-- Goldilocks Healing: `RunInclusion` (H.2 on the run). -/
theorem Consensus.Goldilocks.Healing.runInclusion : Consensus.Goldilocks.Healing.RunInclusion :=
  Consensus.Goldilocks.Healing.healing_run_statements.runInclusion

/-- Goldilocks Healing: `NonInterference` (H.3). -/
theorem Consensus.Goldilocks.Healing.nonInterference :
    Consensus.Goldilocks.Healing.NonInterference :=
  Consensus.Goldilocks.Healing.healing_run_statements.nonInterference

/-- Goldilocks Healing: `AvailableHealing` (H.4). -/
theorem Consensus.Goldilocks.Healing.availableHealing :
    Consensus.Goldilocks.Healing.AvailableHealing :=
  Consensus.Goldilocks.Healing.healing_run_statements.availableHealing

/-- Goldilocks Healing: `ViableWitnessRetention` (HS.1). -/
theorem Consensus.Goldilocks.Healing.viableWitnessRetention :
    Consensus.Goldilocks.Healing.ViableWitnessRetention :=
  Consensus.Goldilocks.Healing.phase_service_statements.viableWitnessRetention

/-- Goldilocks Healing: `CleanLockDrain` (HS.2). -/
theorem Consensus.Goldilocks.Healing.cleanLockDrain :
    Consensus.Goldilocks.Healing.CleanLockDrain :=
  Consensus.Goldilocks.Healing.phase_service_statements.cleanLockDrain

/-- Goldilocks Healing: `FrozenTreeAgreement` (HS.3). -/
theorem Consensus.Goldilocks.Healing.frozenTreeAgreement :
    Consensus.Goldilocks.Healing.FrozenTreeAgreement :=
  Consensus.Goldilocks.Healing.phase_service_statements.frozenTreeAgreement

/-- Goldilocks Healing: `CommonPathAcquisition` (HS.4). -/
theorem Consensus.Goldilocks.Healing.commonPathAcquisition :
    Consensus.Goldilocks.Healing.CommonPathAcquisition :=
  Consensus.Goldilocks.Healing.phase_service_statements.commonPathAcquisition

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

/-- info: 'Consensus.Goldilocks.Compose.honestFastConfirmationsPersist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.honestFastConfirmationsPersist

/-- info: 'Consensus.Goldilocks.Compose.recentSourceNextVote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.recentSourceNextVote

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

/-- info: 'Consensus.Goldilocks.Regimes.sleepySafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.sleepySafe

/-- info: 'Consensus.Goldilocks.Regimes.includeSleepy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.includeSleepy

/-- info: 'Consensus.Goldilocks.Regimes.growSleepy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.growSleepy

/-- info: 'Consensus.Goldilocks.Compose.headExtendsRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.headExtendsRecord

/-- info: 'Consensus.Goldilocks.Compose.inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.inclusion

/-- info: 'Consensus.Goldilocks.SA.aCHealingStandaloneAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCHealingStandaloneAll

/-- info: 'Consensus.Goldilocks.SA.aCHealingStandaloneCorollaryAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCHealingStandaloneCorollaryAll

/-- info: 'Consensus.Goldilocks.SA.aCHealingStandaloneTightAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCHealingStandaloneTightAll

/--
info: 'Consensus.Goldilocks.SA.aCHealingStandaloneTightCorollaryAll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCHealingStandaloneTightCorollaryAll

/-- info: 'Consensus.Goldilocks.SA.aCInclusionAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCInclusionAll

/-- info: 'Consensus.Goldilocks.Healing.cutAndReset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.cutAndReset

/-- info: 'Consensus.Goldilocks.Healing.phaseCountAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.phaseCountAll

/-- info: 'Consensus.Goldilocks.Healing.resetExistence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.resetExistence

/-- info: 'Consensus.Goldilocks.Healing.heightScopedRetention' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.heightScopedRetention

/-- info: 'Consensus.Goldilocks.Healing.runInclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.runInclusion

/-- info: 'Consensus.Goldilocks.Healing.nonInterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.nonInterference

/-- info: 'Consensus.Goldilocks.Healing.availableHealing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.availableHealing

/-- info: 'Consensus.Goldilocks.Healing.viableWitnessRetention' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.viableWitnessRetention

/-- info: 'Consensus.Goldilocks.Healing.cleanLockDrain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.cleanLockDrain

/-- info: 'Consensus.Goldilocks.Healing.frozenTreeAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.frozenTreeAgreement

/-- info: 'Consensus.Goldilocks.Healing.commonPathAcquisition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.commonPathAcquisition

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
