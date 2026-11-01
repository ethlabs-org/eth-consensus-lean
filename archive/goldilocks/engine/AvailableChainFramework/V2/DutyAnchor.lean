module
public import AvailableChainEngineV2.Conditions.Duty.Lift

@[expose] public section

namespace AvailableChain.Framework.V2

/-- Additive anchor for the engine with separate duties and signing labels. -/
def dutyAnchor : Unit :=
  -- AvailableChainEngineV2.Engine.Duty.Lift
  let _ := @AvailableChain.V2.ProtocolSpec.toD
  let _ := @AvailableChain.V2.Run.toD
  let _ := @AvailableChain.V2.D.Run.ofD
  let _ := @AvailableChain.V2.D.Run.toD_ofD
  let _ := @AvailableChain.V2.D.Run.ofD_toD
  let _ := @AvailableChain.V2.D.dutiesInjectiveAt_toD
  let _ := @AvailableChain.V2.D.objSelfVisible_toD
  let _ := @AvailableChain.V2.D.tick_toD
  let _ := @AvailableChain.V2.D.world_init_toD
  let _ := @AvailableChain.V2.D.world_step_toD
  let _ := @AvailableChain.V2.D.stateBefore_toD
  let _ := @AvailableChain.V2.D.stateBeforeTime_toD
  let _ := @AvailableChain.V2.D.readAt_toD
  let _ := @AvailableChain.V2.D.final_toD
  let _ := @AvailableChain.V2.D.emitsAt_toD
  let _ := @AvailableChain.V2.D.tickIdx_toD
  let _ := @AvailableChain.V2.D.emittedAt_toD
  let _ := @AvailableChain.V2.D.emits_toD
  let _ := @AvailableChain.V2.D.processes_toD
  let _ := @AvailableChain.V2.D.handlesAt_toD
  let _ := @AvailableChain.V2.D.acceptsAt_toD
  let _ := @AvailableChain.V2.D.holder_toD
  -- AvailableChainEngineV2.Engine.Duty.Run
  let _ := @AvailableChain.V2.D.World
  let _ := @AvailableChain.V2.D.World.init
  let _ := @AvailableChain.V2.D.Run
  let _ := @AvailableChain.V2.D.Run.mk
  let _ := @AvailableChain.V2.D.Run.honest
  let _ := @AvailableChain.V2.D.Run.horizon
  let _ := @AvailableChain.V2.D.Run.events
  let _ := @AvailableChain.V2.D.Run.seatOf
  let _ := @AvailableChain.V2.D.Run.input
  let _ := @AvailableChain.V2.D.Run.ownSeats
  let _ := @AvailableChain.V2.D.tick
  let _ := @AvailableChain.V2.D.World.step
  let _ := @AvailableChain.V2.D.Run.stateBefore
  let _ := @AvailableChain.V2.D.Run.stateBeforeTime
  let _ := @AvailableChain.V2.D.Run.readAt
  let _ := @AvailableChain.V2.D.Run.final
  let _ := @AvailableChain.V2.D.Run.emitsAt
  let _ := @AvailableChain.V2.D.Run.tickIdx?
  let _ := @AvailableChain.V2.D.Run.emittedAt
  let _ := @AvailableChain.V2.D.Run.emits
  let _ := @AvailableChain.V2.D.Run.processes
  let _ := @AvailableChain.V2.D.Run.handlesAt
  let _ := @AvailableChain.V2.D.Run.acceptsAt
  let _ := @AvailableChain.V2.D.Run.holder
  let _ := @AvailableChain.V2.D.Run.stateBefore_succ
  let _ := @AvailableChain.V2.D.Run.step_tick_eq
  let _ := @AvailableChain.V2.D.tick_decomp
  let _ := @AvailableChain.V2.D.tick_asleep
  let _ := @AvailableChain.V2.D.Run.tickIdx?_spec
  let _ := @AvailableChain.V2.D.Run.emittedAt_eq_emitsAt
  let _ := @AvailableChain.V2.D.Run.mem_emittedAt_iff_emits
  -- AvailableChainEngineV2.Engine.Duty.Spec
  let _ := @AvailableChain.V2.ProtocolSpecD
  let _ := @AvailableChain.V2.ProtocolSpecD.mk
  let _ := @AvailableChain.V2.ProtocolSpecD.State
  let _ := @AvailableChain.V2.ProtocolSpecD.Label
  let _ := @AvailableChain.V2.ProtocolSpecD.Duty
  let _ := @AvailableChain.V2.ProtocolSpecD.signLabel
  let _ := @AvailableChain.V2.ProtocolSpecD.seats
  let _ := @AvailableChain.V2.ProtocolSpecD.Payload
  let _ := @AvailableChain.V2.ProtocolSpecD.Durable
  let _ := @AvailableChain.V2.ProtocolSpecD.init
  let _ := @AvailableChain.V2.ProtocolSpecD.clock
  let _ := @AvailableChain.V2.ProtocolSpecD.actTime
  let _ := @AvailableChain.V2.ProtocolSpecD.duties
  let _ := @AvailableChain.V2.ProtocolSpecD.duties_spec
  let _ := @AvailableChain.V2.ProtocolSpecD.duties_nodup
  let _ := @AvailableChain.V2.ProtocolSpecD.act
  let _ := @AvailableChain.V2.ProtocolSpecD.gossip
  let _ := @AvailableChain.V2.ProtocolSpecD.process
  let _ := @AvailableChain.V2.ProtocolSpecD.selfVisible
  let _ := @AvailableChain.V2.ProtocolSpecD.recordOwn
  let _ := @AvailableChain.V2.ProtocolSpecD.durable
  let _ := @AvailableChain.V2.ProtocolSpecD.restore
  let _ := @AvailableChain.V2.ProtocolSpecD.wellFormed
  let _ := @AvailableChain.V2.ProtocolSpecD.depsPresent
  let _ := @AvailableChain.V2.ProtocolSpecD.processed
  let _ := @AvailableChain.V2.ProtocolSpecD.excludes
  let _ := @AvailableChain.V2.ProtocolSpecD.handles
  let _ := @AvailableChain.V2.ProtocolSpecD.carries
  let _ := @AvailableChain.V2.ProtocolSpecD.Object
  let _ := @AvailableChain.V2.ProtocolSpecD.objSelfVisible
  -- AvailableChainEngineV2.Conditions.Duty.Committees
  let _ := @AvailableChain.V2.D.LabelFamilies
  let _ := @AvailableChain.V2.D.LabelFamilies.mk
  let _ := @AvailableChain.V2.D.LabelFamilies.ap
  let _ := @AvailableChain.V2.D.LabelFamilies.fresh
  let _ := @AvailableChain.V2.D.LabelFamilies.linked
  let _ := @AvailableChain.V2.D.CStar
  let _ := @AvailableChain.V2.D.Linked
  let _ := @AvailableChain.V2.D.SingleSeat
  let _ := @AvailableChain.V2.D.Linked.toCStar
  let _ := @AvailableChain.V2.D.CStar.seats_eq
  -- AvailableChainEngineV2.Conditions.Duty.Delivery
  let _ := @AvailableChain.V2.D.PartialSynchrony
  let _ := @AvailableChain.V2.D.PartialSynchrony.mk
  let _ := @AvailableChain.V2.D.PartialSynchrony.broadcast_emitted
  let _ := @AvailableChain.V2.D.PartialSynchrony.relay_accepted
  let _ := @AvailableChain.V2.D.HealthyPrefixDelivery
  let _ := @AvailableChain.V2.D.HealthyPrefixDelivery.mk
  let _ := @AvailableChain.V2.D.HealthyPrefixDelivery.broadcast_emitted
  let _ := @AvailableChain.V2.D.HealthyPrefixDelivery.relay_accepted
  -- AvailableChainEngineV2.Conditions.Duty.Duties
  let _ := @AvailableChain.V2.D.DutiesInjectiveAt
  -- AvailableChainEngineV2.Conditions.Duty.Interface
  let _ := @AvailableChain.V2.D.Interface
  let _ := @AvailableChain.V2.D.Interface.mk
  let _ := @AvailableChain.V2.D.Interface.confirmed
  let _ := @AvailableChain.V2.D.Interface.stable
  let _ := @AvailableChain.V2.D.Interface.block
  let _ := @AvailableChain.V2.D.Interface.opening
  let _ := @AvailableChain.V2.D.Interface.propLabel
  let _ := @AvailableChain.V2.D.Interface.propDuty
  let _ := @AvailableChain.V2.D.Interface.propDuty_label
  let _ := @AvailableChain.V2.D.Interface.propLabel_single
  let _ := @AvailableChain.V2.D.Interface.propLabel_injective
  let _ := @AvailableChain.V2.D.proposalTime
  let _ := @AvailableChain.V2.D.propSeat
  let _ := @AvailableChain.V2.D.proposerOf
  let _ := @AvailableChain.V2.D.eq_propSeat
  let _ := @AvailableChain.V2.D.holder_propLabel
  let _ := @AvailableChain.V2.D.Output
  let _ := @AvailableChain.V2.D.outputAt
  let _ := @AvailableChain.V2.D.BlockInRun
  let _ := @AvailableChain.V2.D.RootInjective
  -- AvailableChainEngineV2.Conditions.Duty.Lift
  let _ := @AvailableChain.V2.LabelFamilies.toD
  let _ := @AvailableChain.V2.Interface.toD
  let _ := @AvailableChain.V2.D.apObject_toD_iff
  let _ := @AvailableChain.V2.Isolation.toD
  let _ := @AvailableChain.V2.D.Isolation.ofD
  let _ := @AvailableChain.V2.D.Interface.ofD
  let _ := @AvailableChain.V2.D.interface_toD_iff
  let _ := @AvailableChain.V2.D.isolation_toD_iff
  let _ := @AvailableChain.V2.D.cStar_toD_iff
  let _ := @AvailableChain.V2.D.linked_toD_iff
  let _ := @AvailableChain.V2.D.singleSeat_toD_iff
  let _ := @AvailableChain.V2.D.noRestart_toD_iff
  let _ := @AvailableChain.V2.D.restartFree_toD_iff
  let _ := @AvailableChain.V2.D.proposalTime_toD
  let _ := @AvailableChain.V2.D.proposerOf_toD
  let _ := @AvailableChain.V2.D.scheduleWellFormed_toD_iff
  let _ := @AvailableChain.V2.D.deliveryWellFormed_toD_iff
  let _ := @AvailableChain.V2.D.unforgeableSignatures_toD_iff
  let _ := @AvailableChain.V2.D.partialSynchrony_toD_iff
  let _ := @AvailableChain.V2.D.healthyPrefixDelivery_toD_iff
  let _ := @AvailableChain.V2.D.emitOk_toD_iff
  let _ := @AvailableChain.V2.D.executionValid_toD_iff
  let _ := @AvailableChain.V2.D.selfDelivery_toD_iff
  let _ := @AvailableChain.V2.D.blockInRun_toD_iff
  let _ := @AvailableChain.V2.D.rootInjective_toD_iff
  let _ := @AvailableChain.V2.D.outputAt_toD
  let _ := @AvailableChain.V2.D.holder_of_mem_tick_toD
  let _ := @AvailableChain.V2.D.outputsFactor_toD_iff
  let _ := @AvailableChain.V2.D.hooksSound_toD_iff
  -- AvailableChainEngineV2.Conditions.Duty.Schedule
  let _ := @AvailableChain.V2.D.ScheduleWellFormed
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.mk
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.horizon_nonneg
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.sorted
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.nodup
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.in_horizon
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.honest_only
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.tick_public
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.tick_total
  let _ := @AvailableChain.V2.D.NoRestart
  let _ := @AvailableChain.V2.D.restartFree
  let _ := @AvailableChain.V2.D.DeliveryWellFormed
  let _ := @AvailableChain.V2.D.DeliveryWellFormed.mk
  let _ := @AvailableChain.V2.D.DeliveryWellFormed.wire
  let _ := @AvailableChain.V2.D.DeliveryWellFormed.deps
  let _ := @AvailableChain.V2.D.DeliveryWellFormed.fresh
  let _ := @AvailableChain.V2.D.UnforgeableSignatures
  let _ := @AvailableChain.V2.D.UnforgeableSignatures.mk
  let _ := @AvailableChain.V2.D.UnforgeableSignatures.unforgeable
  let _ := @AvailableChain.V2.D.UnforgeableSignatures.carried
  let _ := @AvailableChain.V2.D.ExecutionValid
  let _ := @AvailableChain.V2.D.ExecutionValid.toDeliveryWellFormed
  let _ := @AvailableChain.V2.D.ExecutionValid.toScheduleWellFormed
  let _ := @AvailableChain.V2.D.ExecutionValid.toUnforgeableSignatures
  let _ := @AvailableChain.V2.D.ExecutionValid.mk
  let _ := @AvailableChain.V2.D.SelfDelivery
  let _ := @AvailableChain.V2.D.ScheduleWellFormed.mem_emittedAt_iff_emits
  let _ := @AvailableChain.V2.D.restartFree_refl
  let _ := @AvailableChain.V2.D.not_restartFree_succ_iff
  let _ := @AvailableChain.V2.D.restartFree.mono
  let _ := @AvailableChain.V2.D.restartFree.append
  let _ := @AvailableChain.V2.D.NoRestart.restartFree
  -- AvailableChainEngineV2.Laws.Duty.Hooks
  let _ := @AvailableChain.V2.D.HooksSound
  let _ := @AvailableChain.V2.D.HooksSound.mk
  let _ := @AvailableChain.V2.D.HooksSound.excludes_inert
  let _ := @AvailableChain.V2.D.HooksSound.excludes_stable
  let _ := @AvailableChain.V2.D.HooksSound.processed_stable
  let _ := @AvailableChain.V2.D.HooksSound.deps_stable
  let _ := @AvailableChain.V2.D.HooksSound.handles_carries
  let _ := @AvailableChain.V2.D.HooksSound.recordOwn_processed
  let _ := @AvailableChain.V2.D.HooksSound.recordOwn_deps
  let _ := @AvailableChain.V2.D.HooksSound.recordOwn_excludes
  let _ := @AvailableChain.V2.D.HooksSound.foldl_recordOwn_processed
  let _ := @AvailableChain.V2.D.HooksSound.foldl_recordOwn_deps
  let _ := @AvailableChain.V2.D.HooksSound.foldl_recordOwn_excludes
  let _ := @AvailableChain.V2.D.HooksSound.processed_tick
  let _ := @AvailableChain.V2.D.HooksSound.deps_tick
  let _ := @AvailableChain.V2.D.HooksSound.excludes_tick
  -- AvailableChainEngineV2.Laws.Duty.Isolation
  let _ := @AvailableChain.V2.D.LabelFamilies.APObject
  let _ := @AvailableChain.V2.D.LabelFamilies.apObject_seat
  let _ := @AvailableChain.V2.D.LabelFamilies.apObject_none
  let _ := @AvailableChain.V2.D.Isolation
  let _ := @AvailableChain.V2.D.Isolation.mk
  let _ := @AvailableChain.V2.D.Isolation.Base
  let _ := @AvailableChain.V2.D.Isolation.base
  let _ := @AvailableChain.V2.D.Isolation.clockB
  let _ := @AvailableChain.V2.D.Isolation.clock_base
  let _ := @AvailableChain.V2.D.Isolation.processB
  let _ := @AvailableChain.V2.D.Isolation.process_base
  let _ := @AvailableChain.V2.D.Isolation.recordOwn_base
  let _ := @AvailableChain.V2.D.Isolation.actB
  let _ := @AvailableChain.V2.D.Isolation.act_base
  let _ := @AvailableChain.V2.D.Isolation.gossipB
  let _ := @AvailableChain.V2.D.Isolation.gossip_base
  let _ := @AvailableChain.V2.D.Isolation.depsB
  let _ := @AvailableChain.V2.D.Isolation.processedB
  let _ := @AvailableChain.V2.D.Isolation.excludesB
  let _ := @AvailableChain.V2.D.Isolation.handlesB
  let _ := @AvailableChain.V2.D.Isolation.hooks_base
  let _ := @AvailableChain.V2.D.Isolation.separation
  let _ := @AvailableChain.V2.D.Isolation.foldl_recordOwn_base
  let _ := @AvailableChain.V2.D.Isolation.base_tick
  let _ := @AvailableChain.V2.D.Isolation.hooks_congr
  let _ := @AvailableChain.V2.D.Isolation.not_ap_of_selfVisible
  -- AvailableChainEngineV2.Laws.Duty.Outputs
  let _ := @AvailableChain.V2.D.OutputsFactor
  let _ := @AvailableChain.V2.D.OutputsFactor.mk
  let _ := @AvailableChain.V2.D.OutputsFactor.confirmedB
  let _ := @AvailableChain.V2.D.OutputsFactor.confirmed_base
  let _ := @AvailableChain.V2.D.OutputsFactor.stableB
  let _ := @AvailableChain.V2.D.OutputsFactor.stable_base
  let _ := @AvailableChain.V2.D.OutputsFactor.confirmed_recordOwn
  let _ := @AvailableChain.V2.D.OutputsFactor.stable_recordOwn
  let _ := @AvailableChain.V2.D.OutputsFactor.confirmed_tick
  let _ := @AvailableChain.V2.D.OutputsFactor.stable_tick
  -- AvailableChainEngineV2.Laws.Duty.SelfDelivery
  let _ := @AvailableChain.V2.D.EmitOk
  let _ := @AvailableChain.V2.D.EmitOk.mk
  let _ := @AvailableChain.V2.D.EmitOk.wire
  let _ := @AvailableChain.V2.D.EmitOk.deps
  let _ := @AvailableChain.V2.D.EmitOk.fresh
  let _ := @AvailableChain.V2.D.EmitOk.noCarried
  let _ := @AvailableChain.V2.D.Run.holder_of_mem_tick
  let _ := @AvailableChain.V2.D.World.step_apply_of_node_ne
  let _ := @AvailableChain.V2.D.Run.stateBefore_eq_of_node_ne
  let _ := @AvailableChain.V2.D.selfDelivery_admissible
  let _ := @AvailableChain.V2.D.Run.getElem?_snoc_of_lt
  let _ := @AvailableChain.V2.D.Run.tick_snoc
  let _ := @AvailableChain.V2.D.Run.stateBefore_snoc_of_le
  let _ := @AvailableChain.V2.D.Run.emitsAt_snoc_of_lt
  let _ := @AvailableChain.V2.D.Run.emits_snoc
  let _ := @AvailableChain.V2.D.EmitOk.snoc
  let _ := @AvailableChain.V2.D.ExecutionValid.snoc_selfDelivery
  -- Sleep migration: retain complete engine API anchor coverage.
  -- AvailableChainEngineV2.Engine.Duty.Run
  let _ := @AvailableChain.V2.D.Run.stateAfterRestartsAt
  -- AvailableChainEngineV2.Engine.Run
  let _ := @AvailableChain.V2.Run.stateAfterRestartsAt
  -- AvailableChainEngineV2.Conditions.Duty.Lift
  let _ := @AvailableChain.V2.D.sleepWellFormed_toD_iff
  let _ := @AvailableChain.V2.D.restartsAtWakes_toD_iff
  let _ := @AvailableChain.V2.D.noRestartOn_toD_iff
  let _ := @AvailableChain.V2.D.noRestartAfter_toD_iff
  let _ := @AvailableChain.V2.D.linkReadyOn_toD_iff
  let _ := @AvailableChain.V2.D.processedByActionCut_toD_iff
  let _ := @AvailableChain.V2.D.handledBetween_toD_iff
  let _ := @AvailableChain.V2.D.deliveryService_toD_iff
  let _ := @AvailableChain.V2.D.deliveryDemand_toD_iff
  -- AvailableChainEngineV2.Conditions.Duty.Schedule
  let _ := @AvailableChain.V2.D.ExecutionValid.toSleepWellFormed
  -- AvailableChainEngineV2.Conditions.Duty.Sleep
  let _ := @AvailableChain.V2.D.AwakeOnClosed
  let _ := @AvailableChain.V2.D.SleepWellFormed.tick_awake
  let _ := @AvailableChain.V2.D.SleepWellFormed.deliver_awake
  let _ := @AvailableChain.V2.D.SleepWellFormed.restart_awake
  let _ := @AvailableChain.V2.D.SleepWellFormed.wake_restart
  let _ := @AvailableChain.V2.D.RestartsAtWakes
  let _ := @AvailableChain.V2.D.NoRestartOn
  let _ := @AvailableChain.V2.D.NoRestartAfter
  -- AvailableChainEngineV2.Conditions.Schedule
  let _ := @AvailableChain.V2.ExecutionValid.toSleepWellFormed
  -- AvailableChainEngineV2.Conditions.Sleep
  let _ := @AvailableChain.V2.AwakeOnClosed
  let _ := @AvailableChain.V2.SleepWellFormed.tick_awake
  let _ := @AvailableChain.V2.SleepWellFormed.deliver_awake
  let _ := @AvailableChain.V2.SleepWellFormed.restart_awake
  let _ := @AvailableChain.V2.SleepWellFormed.wake_restart
  let _ := @AvailableChain.V2.RestartsAtWakes
  let _ := @AvailableChain.V2.NoRestartOn
  let _ := @AvailableChain.V2.NoRestartAfter
  ()

end AvailableChain.Framework.V2
