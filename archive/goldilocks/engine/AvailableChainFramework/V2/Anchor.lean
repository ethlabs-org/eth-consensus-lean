module
public import AvailableChainEngineV2

@[expose] public section

namespace AvailableChain.Framework.V2

/-! The engine v2 anchor (plan 2a, Task 7; design §1, D6). The lock
(`scripts/CatalogLock.lean`) locks every declaration under the module prefix
`AvailableChainFramework.V2`. The value of `anchor` references every engine
declaration of `docs/V2-API.md` at the 2a gate, so its closure contains each
one and its current snapshot line changes when one of them changes.
A `let` chain, not a tuple: a tuple can fail across universes.

Update the anchor references when current engine coverage changes. A new entry
can use an existing anchor. `scripts/V2Manifest.lean --anchor` prints references
for engine entries that no anchor covers yet; `--check` checks that every engine entry
of the manifest is in the closure of some anchor def. The Framework does not
import `AvailableChainKitV2` (L5): the lock does not see the Kit v2 entries;
their manifest hashes do. -/

/-- References every engine declaration of `docs/V2-API.md` at the 2a gate. -/
def anchor : Unit :=
  -- AvailableChainEngineV2.Engine.Objects
  let _ := @AvailableChain.V2.Auth
  let _ := @AvailableChain.V2.Auth.seat
  let _ := @AvailableChain.V2.Auth.none
  let _ := @AvailableChain.V2.instDecidableEqAuth
  let _ := @AvailableChain.V2.instDecidableEqAuth.decEq
  let _ := @AvailableChain.V2.instReprAuth
  let _ := @AvailableChain.V2.instReprAuth.repr
  let _ := @AvailableChain.V2.Signed
  let _ := @AvailableChain.V2.Signed.mk
  let _ := @AvailableChain.V2.Signed.auth
  let _ := @AvailableChain.V2.Signed.payload
  let _ := @AvailableChain.V2.instDecidableEqSigned
  let _ := @AvailableChain.V2.instDecidableEqSigned.decEq
  let _ := @AvailableChain.V2.instReprSigned
  let _ := @AvailableChain.V2.instReprSigned.repr
  -- AvailableChainEngineV2.Engine.Run
  let _ := @AvailableChain.V2.Event
  let _ := @AvailableChain.V2.Event.restart
  let _ := @AvailableChain.V2.Event.tick
  let _ := @AvailableChain.V2.Event.deliver
  let _ := @AvailableChain.V2.instDecidableEqEvent
  let _ := @AvailableChain.V2.instDecidableEqEvent.decEq
  let _ := @AvailableChain.V2.Event.time
  let _ := @AvailableChain.V2.Event.node
  let _ := @AvailableChain.V2.Event.object?
  let _ := @AvailableChain.V2.Event.phase
  let _ := @AvailableChain.V2.Event.key
  let _ := @AvailableChain.V2.World
  let _ := @AvailableChain.V2.World.init
  let _ := @AvailableChain.V2.Run
  let _ := @AvailableChain.V2.Run.mk
  let _ := @AvailableChain.V2.Run.honest
  let _ := @AvailableChain.V2.Run.horizon
  let _ := @AvailableChain.V2.Run.events
  let _ := @AvailableChain.V2.Run.seatOf
  let _ := @AvailableChain.V2.Run.input
  let _ := @AvailableChain.V2.Run.ownSeats
  let _ := @AvailableChain.V2.tick
  let _ := @AvailableChain.V2.World.step
  let _ := @AvailableChain.V2.Run.stateBefore
  let _ := @AvailableChain.V2.Run.stateBeforeTime
  let _ := @AvailableChain.V2.Run.readAt
  let _ := @AvailableChain.V2.Run.final
  let _ := @AvailableChain.V2.Run.emitsAt
  let _ := @AvailableChain.V2.Run.tickIdx?
  let _ := @AvailableChain.V2.Run.emittedAt
  let _ := @AvailableChain.V2.Run.emits
  let _ := @AvailableChain.V2.Run.processes
  let _ := @AvailableChain.V2.Run.handlesAt
  let _ := @AvailableChain.V2.Run.acceptsAt
  let _ := @AvailableChain.V2.Run.holder
  let _ := @AvailableChain.V2.Run.stateBefore_succ
  let _ := @AvailableChain.V2.Run.step_tick_eq
  let _ := @AvailableChain.V2.tick_decomp
  let _ := @AvailableChain.V2.tick_asleep
  let _ := @AvailableChain.V2.Run.tickIdx?_spec
  let _ := @AvailableChain.V2.Run.emittedAt_eq_emitsAt
  let _ := @AvailableChain.V2.Run.mem_emittedAt_iff_emits
  -- AvailableChainEngineV2.Engine.Spec
  let _ := @AvailableChain.V2.ProtocolSpec
  let _ := @AvailableChain.V2.ProtocolSpec.mk
  let _ := @AvailableChain.V2.ProtocolSpec.State
  let _ := @AvailableChain.V2.ProtocolSpec.Label
  let _ := @AvailableChain.V2.ProtocolSpec.seats
  let _ := @AvailableChain.V2.ProtocolSpec.Payload
  let _ := @AvailableChain.V2.ProtocolSpec.Durable
  let _ := @AvailableChain.V2.ProtocolSpec.init
  let _ := @AvailableChain.V2.ProtocolSpec.clock
  let _ := @AvailableChain.V2.ProtocolSpec.actTime
  let _ := @AvailableChain.V2.ProtocolSpec.duties
  let _ := @AvailableChain.V2.ProtocolSpec.duties_spec
  let _ := @AvailableChain.V2.ProtocolSpec.duties_nodup
  let _ := @AvailableChain.V2.ProtocolSpec.act
  let _ := @AvailableChain.V2.ProtocolSpec.gossip
  let _ := @AvailableChain.V2.ProtocolSpec.process
  let _ := @AvailableChain.V2.ProtocolSpec.selfVisible
  let _ := @AvailableChain.V2.ProtocolSpec.recordOwn
  let _ := @AvailableChain.V2.ProtocolSpec.durable
  let _ := @AvailableChain.V2.ProtocolSpec.restore
  let _ := @AvailableChain.V2.ProtocolSpec.wellFormed
  let _ := @AvailableChain.V2.ProtocolSpec.depsPresent
  let _ := @AvailableChain.V2.ProtocolSpec.processed
  let _ := @AvailableChain.V2.ProtocolSpec.excludes
  let _ := @AvailableChain.V2.ProtocolSpec.handles
  let _ := @AvailableChain.V2.ProtocolSpec.carries
  let _ := @AvailableChain.V2.ProtocolSpec.Object
  let _ := @AvailableChain.V2.ProtocolSpec.objSelfVisible
  -- AvailableChainEngineV2.Conditions.Committees
  let _ := @AvailableChain.V2.LabelFamilies
  let _ := @AvailableChain.V2.LabelFamilies.mk
  let _ := @AvailableChain.V2.LabelFamilies.ap
  let _ := @AvailableChain.V2.LabelFamilies.fresh
  let _ := @AvailableChain.V2.LabelFamilies.linked
  let _ := @AvailableChain.V2.CStar
  let _ := @AvailableChain.V2.Linked
  let _ := @AvailableChain.V2.SingleSeat
  let _ := @AvailableChain.V2.Linked.toCStar
  let _ := @AvailableChain.V2.CStar.seats_eq
  -- AvailableChainEngineV2.Conditions.Delivery
  let _ := @AvailableChain.V2.PartialSynchrony
  let _ := @AvailableChain.V2.PartialSynchrony.mk
  let _ := @AvailableChain.V2.PartialSynchrony.broadcast
  let _ := @AvailableChain.V2.PartialSynchrony.relay
  let _ := @AvailableChain.V2.HealthyPrefixDelivery
  let _ := @AvailableChain.V2.HealthyPrefixDelivery.mk
  let _ := @AvailableChain.V2.HealthyPrefixDelivery.broadcast
  let _ := @AvailableChain.V2.HealthyPrefixDelivery.relay
  -- AvailableChainEngineV2.Conditions.Interface
  let _ := @AvailableChain.V2.Interface
  let _ := @AvailableChain.V2.Interface.mk
  let _ := @AvailableChain.V2.Interface.confirmed
  let _ := @AvailableChain.V2.Interface.stable
  let _ := @AvailableChain.V2.Interface.block
  let _ := @AvailableChain.V2.Interface.opening
  let _ := @AvailableChain.V2.Interface.propLabel
  let _ := @AvailableChain.V2.Interface.propLabel_single
  let _ := @AvailableChain.V2.Interface.propLabel_injective
  let _ := @AvailableChain.V2.proposalTime
  let _ := @AvailableChain.V2.propSeat
  let _ := @AvailableChain.V2.proposerOf
  let _ := @AvailableChain.V2.eq_propSeat
  let _ := @AvailableChain.V2.holder_propLabel
  let _ := @AvailableChain.V2.Output
  let _ := @AvailableChain.V2.outputAt
  let _ := @AvailableChain.V2.BlockInRun
  let _ := @AvailableChain.V2.RootInjective
  -- AvailableChainEngineV2.Conditions.Schedule
  let _ := @AvailableChain.V2.PublicTime
  let _ := @AvailableChain.V2.ScheduleWellFormed
  let _ := @AvailableChain.V2.ScheduleWellFormed.mk
  let _ := @AvailableChain.V2.ScheduleWellFormed.horizon_nonneg
  let _ := @AvailableChain.V2.ScheduleWellFormed.sorted
  let _ := @AvailableChain.V2.ScheduleWellFormed.nodup
  let _ := @AvailableChain.V2.ScheduleWellFormed.in_horizon
  let _ := @AvailableChain.V2.ScheduleWellFormed.honest_only
  let _ := @AvailableChain.V2.ScheduleWellFormed.tick_public
  let _ := @AvailableChain.V2.ScheduleWellFormed.tick_total
  let _ := @AvailableChain.V2.NoRestart
  let _ := @AvailableChain.V2.restartFree
  let _ := @AvailableChain.V2.DeliveryWellFormed
  let _ := @AvailableChain.V2.DeliveryWellFormed.mk
  let _ := @AvailableChain.V2.DeliveryWellFormed.wire
  let _ := @AvailableChain.V2.DeliveryWellFormed.deps
  let _ := @AvailableChain.V2.DeliveryWellFormed.fresh
  let _ := @AvailableChain.V2.UnforgeableSignatures
  let _ := @AvailableChain.V2.UnforgeableSignatures.mk
  let _ := @AvailableChain.V2.UnforgeableSignatures.unforgeable
  let _ := @AvailableChain.V2.UnforgeableSignatures.carried
  let _ := @AvailableChain.V2.ExecutionValid
  let _ := @AvailableChain.V2.ExecutionValid.toDeliveryWellFormed
  let _ := @AvailableChain.V2.ExecutionValid.toScheduleWellFormed
  let _ := @AvailableChain.V2.ExecutionValid.toUnforgeableSignatures
  let _ := @AvailableChain.V2.ExecutionValid.mk
  let _ := @AvailableChain.V2.SelfDelivery
  let _ := @AvailableChain.V2.ScheduleWellFormed.mem_emittedAt_iff_emits
  let _ := @AvailableChain.V2.restartFree_refl
  let _ := @AvailableChain.V2.not_restartFree_succ_iff
  let _ := @AvailableChain.V2.restartFree.mono
  let _ := @AvailableChain.V2.restartFree.append
  let _ := @AvailableChain.V2.NoRestart.restartFree
  -- AvailableChainEngineV2.Laws.Hooks
  let _ := @AvailableChain.V2.HooksSound
  let _ := @AvailableChain.V2.HooksSound.mk
  let _ := @AvailableChain.V2.HooksSound.excludes_inert
  let _ := @AvailableChain.V2.HooksSound.excludes_stable
  let _ := @AvailableChain.V2.HooksSound.processed_stable
  let _ := @AvailableChain.V2.HooksSound.deps_stable
  let _ := @AvailableChain.V2.HooksSound.handles_carries
  let _ := @AvailableChain.V2.HooksSound.recordOwn_processed
  let _ := @AvailableChain.V2.HooksSound.recordOwn_deps
  let _ := @AvailableChain.V2.HooksSound.recordOwn_excludes
  let _ := @AvailableChain.V2.HooksSound.foldl_recordOwn_processed
  let _ := @AvailableChain.V2.HooksSound.foldl_recordOwn_deps
  let _ := @AvailableChain.V2.HooksSound.foldl_recordOwn_excludes
  let _ := @AvailableChain.V2.HooksSound.processed_tick
  let _ := @AvailableChain.V2.HooksSound.deps_tick
  let _ := @AvailableChain.V2.HooksSound.excludes_tick
  -- AvailableChainEngineV2.Laws.Isolation
  let _ := @AvailableChain.V2.LabelFamilies.APObject
  let _ := @AvailableChain.V2.LabelFamilies.apObject_seat
  let _ := @AvailableChain.V2.LabelFamilies.apObject_none
  let _ := @AvailableChain.V2.Isolation
  let _ := @AvailableChain.V2.Isolation.mk
  let _ := @AvailableChain.V2.Isolation.Base
  let _ := @AvailableChain.V2.Isolation.base
  let _ := @AvailableChain.V2.Isolation.clockB
  let _ := @AvailableChain.V2.Isolation.clock_base
  let _ := @AvailableChain.V2.Isolation.processB
  let _ := @AvailableChain.V2.Isolation.process_base
  let _ := @AvailableChain.V2.Isolation.recordOwn_base
  let _ := @AvailableChain.V2.Isolation.actB
  let _ := @AvailableChain.V2.Isolation.act_base
  let _ := @AvailableChain.V2.Isolation.gossipB
  let _ := @AvailableChain.V2.Isolation.gossip_base
  let _ := @AvailableChain.V2.Isolation.depsB
  let _ := @AvailableChain.V2.Isolation.processedB
  let _ := @AvailableChain.V2.Isolation.excludesB
  let _ := @AvailableChain.V2.Isolation.handlesB
  let _ := @AvailableChain.V2.Isolation.hooks_base
  let _ := @AvailableChain.V2.Isolation.separation
  let _ := @AvailableChain.V2.Isolation.foldl_recordOwn_base
  let _ := @AvailableChain.V2.Isolation.base_tick
  let _ := @AvailableChain.V2.Isolation.hooks_congr
  let _ := @AvailableChain.V2.Isolation.not_ap_of_selfVisible
  -- AvailableChainEngineV2.Laws.Outputs
  let _ := @AvailableChain.V2.OutputsFactor
  let _ := @AvailableChain.V2.OutputsFactor.mk
  let _ := @AvailableChain.V2.OutputsFactor.confirmedB
  let _ := @AvailableChain.V2.OutputsFactor.confirmed_base
  let _ := @AvailableChain.V2.OutputsFactor.stableB
  let _ := @AvailableChain.V2.OutputsFactor.stable_base
  let _ := @AvailableChain.V2.OutputsFactor.confirmed_recordOwn
  let _ := @AvailableChain.V2.OutputsFactor.stable_recordOwn
  let _ := @AvailableChain.V2.OutputsFactor.confirmed_tick
  let _ := @AvailableChain.V2.OutputsFactor.stable_tick
  -- AvailableChainEngineV2.Laws.SelfDelivery
  let _ := @AvailableChain.V2.EmitOk
  let _ := @AvailableChain.V2.EmitOk.mk
  let _ := @AvailableChain.V2.EmitOk.wire
  let _ := @AvailableChain.V2.EmitOk.deps
  let _ := @AvailableChain.V2.EmitOk.fresh
  let _ := @AvailableChain.V2.EmitOk.noCarried
  let _ := @AvailableChain.V2.Run.holder_of_mem_tick
  let _ := @AvailableChain.V2.World.step_apply_of_node_ne
  let _ := @AvailableChain.V2.Run.stateBefore_eq_of_node_ne
  let _ := @AvailableChain.V2.selfDelivery_admissible
  let _ := @AvailableChain.V2.Run.getElem?_snoc_of_lt
  let _ := @AvailableChain.V2.Run.tick_snoc
  let _ := @AvailableChain.V2.Run.stateBefore_snoc_of_le
  let _ := @AvailableChain.V2.Run.emitsAt_snoc_of_lt
  let _ := @AvailableChain.V2.Run.emits_snoc
  let _ := @AvailableChain.V2.EmitOk.snoc
  let _ := @AvailableChain.V2.ExecutionValid.snoc_selfDelivery
  ()

end AvailableChain.Framework.V2
