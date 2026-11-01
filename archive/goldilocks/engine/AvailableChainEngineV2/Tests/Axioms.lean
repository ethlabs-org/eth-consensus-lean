module
public import AvailableChainEngineV2.Laws.Isolation -- shake: keep (axioms)
public import AvailableChainEngineV2.Laws.SelfDelivery -- shake: keep (axioms)
public import AvailableChainEngineV2.Conditions.Duty.Committees -- shake: keep (axioms)
public import AvailableChainEngineV2.Conditions.Duty.Delivery -- shake: keep (axioms)
public import AvailableChainEngineV2.Conditions.Duty.Duties -- shake: keep (axioms)
public import AvailableChainEngineV2.Conditions.Duty.Interface -- shake: keep (axioms)
public import AvailableChainEngineV2.Conditions.Duty.Lift -- shake: keep (axioms)
public import AvailableChainEngineV2.Conditions.Duty.Schedule -- shake: keep (axioms)
public import AvailableChainEngineV2.Engine.Duty.Lift -- shake: keep (axioms)
public import AvailableChainEngineV2.Engine.Duty.Run -- shake: keep (axioms)
public import AvailableChainEngineV2.Engine.Duty.Spec -- shake: keep (axioms)
public import AvailableChainEngineV2.Laws.Duty.Hooks -- shake: keep (axioms)
public import AvailableChainEngineV2.Laws.Duty.Isolation -- shake: keep (axioms)
public import AvailableChainEngineV2.Laws.Duty.Outputs -- shake: keep (axioms)
public import AvailableChainEngineV2.Laws.Duty.SelfDelivery -- shake: keep (axioms)

-- Duty engine: every new production theorem.
#print axioms AvailableChain.V2.D.Linked.toCStar
#print axioms AvailableChain.V2.D.CStar.seats_eq
#print axioms AvailableChain.V2.D.eq_propSeat
#print axioms AvailableChain.V2.D.holder_propLabel
-- ROOT-DIGEST W3: deleted global-root audit; scoped replacement.
#print axioms AvailableChain.V2.D.rootInjective_toD_iff
#print axioms AvailableChain.V2.D.apObject_toD_iff
#print axioms AvailableChain.V2.D.interface_toD_iff
#print axioms AvailableChain.V2.D.isolation_toD_iff
#print axioms AvailableChain.V2.D.cStar_toD_iff
#print axioms AvailableChain.V2.D.linked_toD_iff
#print axioms AvailableChain.V2.D.singleSeat_toD_iff
#print axioms AvailableChain.V2.D.noRestart_toD_iff
#print axioms AvailableChain.V2.D.restartFree_toD_iff
#print axioms AvailableChain.V2.D.proposalTime_toD
#print axioms AvailableChain.V2.D.proposerOf_toD
#print axioms AvailableChain.V2.D.scheduleWellFormed_toD_iff
#print axioms AvailableChain.V2.D.deliveryWellFormed_toD_iff
#print axioms AvailableChain.V2.D.unforgeableSignatures_toD_iff
#print axioms AvailableChain.V2.D.partialSynchrony_toD_iff
#print axioms AvailableChain.V2.D.healthyPrefixDelivery_toD_iff
#print axioms AvailableChain.V2.D.emitOk_toD_iff
#print axioms AvailableChain.V2.D.executionValid_toD_iff
#print axioms AvailableChain.V2.D.selfDelivery_toD_iff
#print axioms AvailableChain.V2.D.blockInRun_toD_iff
#print axioms AvailableChain.V2.D.rootInjective_toD_iff
#print axioms AvailableChain.V2.D.outputAt_toD
#print axioms AvailableChain.V2.D.holder_of_mem_tick_toD
#print axioms AvailableChain.V2.D.outputsFactor_toD_iff
#print axioms AvailableChain.V2.D.hooksSound_toD_iff
#print axioms AvailableChain.V2.D.ScheduleWellFormed.mem_emittedAt_iff_emits
#print axioms AvailableChain.V2.D.restartFree_refl
#print axioms AvailableChain.V2.D.not_restartFree_succ_iff
#print axioms AvailableChain.V2.D.restartFree.mono
#print axioms AvailableChain.V2.D.restartFree.append
#print axioms AvailableChain.V2.D.NoRestart.restartFree
#print axioms AvailableChain.V2.D.Run.toD_ofD
#print axioms AvailableChain.V2.D.Run.ofD_toD
#print axioms AvailableChain.V2.D.dutiesInjectiveAt_toD
#print axioms AvailableChain.V2.D.objSelfVisible_toD
#print axioms AvailableChain.V2.D.tick_toD
#print axioms AvailableChain.V2.D.world_init_toD
#print axioms AvailableChain.V2.D.world_step_toD
#print axioms AvailableChain.V2.D.stateBefore_toD
#print axioms AvailableChain.V2.D.stateBeforeTime_toD
#print axioms AvailableChain.V2.D.readAt_toD
#print axioms AvailableChain.V2.D.final_toD
#print axioms AvailableChain.V2.D.emitsAt_toD
#print axioms AvailableChain.V2.D.tickIdx_toD
#print axioms AvailableChain.V2.D.emittedAt_toD
#print axioms AvailableChain.V2.D.emits_toD
#print axioms AvailableChain.V2.D.processes_toD
#print axioms AvailableChain.V2.D.handlesAt_toD
#print axioms AvailableChain.V2.D.acceptsAt_toD
#print axioms AvailableChain.V2.D.holder_toD
#print axioms AvailableChain.V2.D.Run.stateBefore_succ
#print axioms AvailableChain.V2.D.Run.step_tick_eq
#print axioms AvailableChain.V2.D.tick_decomp
#print axioms AvailableChain.V2.D.tick_asleep
#print axioms AvailableChain.V2.D.Run.tickIdx?_spec
#print axioms AvailableChain.V2.D.Run.emittedAt_eq_emitsAt
#print axioms AvailableChain.V2.D.Run.mem_emittedAt_iff_emits
#print axioms AvailableChain.V2.D.HooksSound.foldl_recordOwn_processed
#print axioms AvailableChain.V2.D.HooksSound.foldl_recordOwn_deps
#print axioms AvailableChain.V2.D.HooksSound.foldl_recordOwn_excludes
#print axioms AvailableChain.V2.D.HooksSound.processed_tick
#print axioms AvailableChain.V2.D.HooksSound.deps_tick
#print axioms AvailableChain.V2.D.HooksSound.excludes_tick
#print axioms AvailableChain.V2.D.LabelFamilies.apObject_seat
#print axioms AvailableChain.V2.D.LabelFamilies.apObject_none
#print axioms AvailableChain.V2.D.Isolation.foldl_recordOwn_base
#print axioms AvailableChain.V2.D.Isolation.base_tick
#print axioms AvailableChain.V2.D.Isolation.hooks_congr
#print axioms AvailableChain.V2.D.Isolation.not_ap_of_selfVisible
#print axioms AvailableChain.V2.D.OutputsFactor.confirmed_recordOwn
#print axioms AvailableChain.V2.D.OutputsFactor.stable_recordOwn
#print axioms AvailableChain.V2.D.OutputsFactor.confirmed_tick
#print axioms AvailableChain.V2.D.OutputsFactor.stable_tick
#print axioms AvailableChain.V2.D.Run.holder_of_mem_tick
#print axioms AvailableChain.V2.D.World.step_apply_of_node_ne
#print axioms AvailableChain.V2.D.Run.stateBefore_eq_of_node_ne
#print axioms AvailableChain.V2.D.selfDelivery_admissible
#print axioms AvailableChain.V2.D.Run.getElem?_snoc_of_lt
#print axioms AvailableChain.V2.D.Run.tick_snoc
#print axioms AvailableChain.V2.D.Run.stateBefore_snoc_of_le
#print axioms AvailableChain.V2.D.Run.emitsAt_snoc_of_lt
#print axioms AvailableChain.V2.D.Run.emits_snoc
#print axioms AvailableChain.V2.D.EmitOk.snoc
#print axioms AvailableChain.V2.D.ExecutionValid.snoc_selfDelivery

#print axioms AvailableChain.V2.D.sleepWellFormed_toD_iff
#print axioms AvailableChain.V2.D.restartsAtWakes_toD_iff
#print axioms AvailableChain.V2.D.noRestartOn_toD_iff
#print axioms AvailableChain.V2.D.noRestartAfter_toD_iff
#print axioms AvailableChain.V2.D.linkReadyOn_toD_iff
#print axioms AvailableChain.V2.D.processedByActionCut_toD_iff
#print axioms AvailableChain.V2.D.handledBetween_toD_iff
#print axioms AvailableChain.V2.D.deliveryService_toD_iff
#print axioms AvailableChain.V2.D.deliveryDemand_toD_iff

#print axioms AvailableChain.V2.ExecutionValid.snoc_selfDelivery
