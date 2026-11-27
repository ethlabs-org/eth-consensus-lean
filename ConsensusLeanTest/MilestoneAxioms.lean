module
public import ConsensusLean.Instances.Goldilocks.Proofs.FGSafety.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACSteps.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.FGStore.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ACBase.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.ComposeAnyAC.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.SleepyGrowth.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.OptimisticInclusion.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.CacheAcceptance

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
theorem Consensus.Goldilocks.AC.aCSteps : Consensus.Goldilocks.AC.ACSteps :=
  Consensus.Goldilocks.AC.acSteps

/-- Goldilocks FGStore, part 1: one FG store. -/
theorem Consensus.Goldilocks.Store.fGStoreLocal : Consensus.Goldilocks.Store.FGStoreLocal :=
  Consensus.Goldilocks.Store.fg_store_local

/-- Goldilocks ACBase, the AC interface and the AC's foundations. -/
theorem Consensus.Goldilocks.AC.aCBase : Consensus.Goldilocks.AC.ACBase :=
  Consensus.Goldilocks.AC.acBase

/-- Goldilocks ACBase: the AC trace contract gives reachable states. -/
theorem Consensus.Goldilocks.localRunReachable : Consensus.Goldilocks.LocalRunReachable :=
  fun _ _ _ _ _ _ h => Consensus.Goldilocks.localRun_reachable h

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

/-! Goldilocks Regimes: optimistic inclusion at a committee, under growing faults
(`Results/Statements/OptimisticInclusion`), an internal result on confirmation speed. -/

/-- Goldilocks Regimes: `Growing.OptimisticInclusion`. -/
theorem Consensus.Goldilocks.Regimes.Growing.optimisticInclusion :
    Consensus.Goldilocks.Regimes.Growing.OptimisticInclusion :=
  Consensus.Goldilocks.Regimes.Growing.optimistic_inclusion

/-! Goldilocks Healing: G1.9 (b), cache acceptance, under growing faults
(`Healing/Growing/Run`, the growing form of HR.5). -/

/-- Goldilocks Healing: `Growing.CacheAcceptance` (G1.9 (b)). -/
theorem Consensus.Goldilocks.Healing.Growing.cacheAcceptance :
    Consensus.Goldilocks.Healing.Growing.CacheAcceptance :=
  Consensus.Goldilocks.Healing.Growing.cache_acceptance

/-! ## Axiom pins -/

/-- info: 'Consensus.Goldilocks.FG.fGSafety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.FG.fGSafety

/-- info: 'Consensus.Goldilocks.AC.aCSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.aCSteps

/-- info: 'Consensus.Goldilocks.Store.fGStoreLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Store.fGStoreLocal

/-- info: 'Consensus.Goldilocks.AC.aCBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.AC.aCBase

/-- info: 'Consensus.Goldilocks.localRunReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.localRunReachable

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

/--
info: 'Consensus.Goldilocks.Regimes.Growing.growSleepy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.Growing.growSleepy

/--
info: 'Consensus.Goldilocks.Obligations.Growing.sleepyGrowFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Goldilocks.Obligations.Growing.sleepyGrowFinite

/--
info: 'Consensus.Goldilocks.Regimes.Growing.optimisticInclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.Growing.optimisticInclusion

/--
info: 'Consensus.Goldilocks.Healing.Growing.cacheAcceptance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Consensus.Goldilocks.Healing.Growing.cacheAcceptance

/-- info: 'Consensus.Goldilocks.goldilocks_continues' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.goldilocks_continues

end
