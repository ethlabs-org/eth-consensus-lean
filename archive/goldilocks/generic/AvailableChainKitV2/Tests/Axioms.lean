module
public import AvailableChainKitV2.RunCheck -- shake: keep (axioms)
public import AvailableChainKitV2.DutyExecution -- shake: keep (axioms)
public import AvailableChainKitV2.DutySleep -- shake: keep (axioms)
public import AvailableChainKitV2.DutyStable -- shake: keep (axioms)
public import AvailableChainKitV2.Emission -- shake: keep (axioms)
public import AvailableChainKitV2.Execution -- shake: keep (axioms)
public import AvailableChainKitV2.Sleep -- shake: keep (axioms)
public import AvailableChainKitV2.Stable -- shake: keep (axioms)
public import AvailableChainKitV2.DutyEmission -- shake: keep (axioms)
public import AvailableChainKitV2.DutyLinked -- shake: keep (axioms)
public import AvailableChainKitV2.EngineClock -- shake: keep (axioms)
public import AvailableChainKitV2.DutyEngineClock -- shake: keep (axioms)
public import AvailableChainKitV2.DutyRecord -- shake: keep (axioms)

/-! Kernel dependencies of the subset field-origin helper. -/

#print axioms AvailableChain.V2.Engine.clock_field_origin_of_subset

-- Duty engine: every new production theorem.
#print axioms AvailableChain.V2.D.Engine.mem_tick_seat_iff
#print axioms AvailableChain.V2.D.Engine.mem_tick_duty_iff
#print axioms AvailableChain.V2.D.Engine.mem_tick_of_duty
#print axioms AvailableChain.V2.D.Engine.ownSeats_bijSeat
#print axioms AvailableChain.V2.D.Engine.emits_bijSeat
#print axioms AvailableChain.V2.D.Engine.mem_tick_seat_toD_iff
#print axioms AvailableChain.V2.D.Engine.linked_singleton_iff
#print axioms AvailableChain.V2.D.Engine.seat_family_iff_representative_toD
#print axioms AvailableChain.V2.D.Engine.seat_equation_toD_of_family

-- Duty Kit: all new public declarations.
#print axioms AvailableChain.V2.D.Engine.ClockLaws
#print axioms AvailableChain.V2.D.Engine.ClockLaws.now_foldl_recordOwn
#print axioms AvailableChain.V2.D.Engine.ClockLaws.now_tick
#print axioms AvailableChain.V2.D.Engine.eventIndex_lt_of_time_lt
#print axioms AvailableChain.V2.D.Engine.time_le_of_key_le
#print axioms AvailableChain.V2.D.Engine.filter_eq_take
#print axioms AvailableChain.V2.D.Engine.filter_false_of_index_ge
#print axioms AvailableChain.V2.D.Engine.index_lt_read_length_iff
#print axioms AvailableChain.V2.D.Engine.read_length_mono
#print axioms AvailableChain.V2.D.Engine.tick_index_lt_delivery
#print axioms AvailableChain.V2.D.Engine.readAt_eq_stateBefore
#print axioms AvailableChain.V2.D.Engine.stateBefore_other_node
#print axioms AvailableChain.V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
#print axioms AvailableChain.V2.D.Engine.foldl_recordOwn_preserve
#print axioms AvailableChain.V2.D.Engine.tick_preserve
#print axioms AvailableChain.V2.D.Engine.recordOwn_preserve_of_base
#print axioms AvailableChain.V2.D.Engine.stateBefore_step_induction
#print axioms AvailableChain.V2.D.Engine.stateBefore_stable
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_source
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_source_noRestart
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_le_event
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_le_event_noRestart
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_mono
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_mono_noRestart
#print axioms AvailableChain.V2.D.Engine.delivery_now_ge_public
#print axioms AvailableChain.V2.D.Engine.stateBefore_invariant
#print axioms AvailableChain.V2.D.Engine.stateBefore_invariant_noRestart
#print axioms AvailableChain.V2.D.Engine.stateBefore_stable_clock
#print axioms AvailableChain.V2.D.Engine.stateBefore_stable_clock_restore
#print axioms AvailableChain.V2.D.Engine.stateBefore_stable_clock_noRestart
#print axioms AvailableChain.V2.D.Engine.clock_field_origin
#print axioms AvailableChain.V2.D.Engine.clock_field_origin_noRestart
#print axioms AvailableChain.V2.D.Engine.clock_field_origin_of_subset
#print axioms AvailableChain.V2.D.Engine.stateBefore_field_prefix
#print axioms AvailableChain.V2.D.Engine.stateBefore_field_prefix_restore
#print axioms AvailableChain.V2.D.Engine.ownReleasedAt
#print axioms AvailableChain.V2.D.Engine.ownReleased
#print axioms AvailableChain.V2.D.Engine.ownReleased_self
#print axioms AvailableChain.V2.D.Engine.ownReleased_succ
#print axioms AvailableChain.V2.D.Engine.ownRecord_fold_interval
#print axioms AvailableChain.V2.D.Engine.ownRecord_fold
#print axioms AvailableChain.V2.D.Engine.ownRecord_fold_interval_restart
#print axioms AvailableChain.V2.D.Engine.ownRecord_fold_restore
#print axioms AvailableChain.V2.D.Engine.ownReleasedAt_def
#print axioms AvailableChain.V2.D.Engine.ownReleased_def

-- W1b: sleep, exact restore time, demand, and receipt companions.
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_source_atRestart
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_le_event_atRestart
#print axioms AvailableChain.V2.D.Engine.stateBefore_now_mono_atRestart
#print axioms AvailableChain.V2.D.Engine.delivery_now_ge_public_atRestart
#print axioms AvailableChain.V2.D.Engine.stateBefore_stable_clock_atRestart
#print axioms AvailableChain.V2.D.Engine.stateBefore_invariant_atRestart
#print axioms AvailableChain.V2.D.Engine.index_lt_actionCut_iff
#print axioms AvailableChain.V2.D.Engine.stateBefore_tick_eq_stateAfterRestartsAt
#print axioms AvailableChain.V2.D.Engine.restart_index_lt_event
#print axioms AvailableChain.V2.D.Engine.wake_restart_before_event
#print axioms AvailableChain.V2.D.Engine.state_after_restart
#print axioms AvailableChain.V2.D.Engine.asleep_state_frozen
#print axioms AvailableChain.V2.D.Engine.noRestartOn_of_awakeOn
#print axioms AvailableChain.V2.D.Engine.noRestartAfter_of_awakeOnClosed
#print axioms AvailableChain.V2.D.Engine.wake_between
#print axioms AvailableChain.V2.D.Engine.stateBefore_stable_restore
#print axioms AvailableChain.V2.Engine.ownRecord_fold_interval_restart
#print axioms AvailableChain.V2.Engine.ownRecord_fold_restore
#print axioms AvailableChain.V2.Engine.stateBefore_now_source
#print axioms AvailableChain.V2.Engine.stateBefore_now_le_event
#print axioms AvailableChain.V2.Engine.stateBefore_now_mono
#print axioms AvailableChain.V2.Engine.delivery_now_ge_public
#print axioms AvailableChain.V2.Engine.stateBefore_now_source_atRestart
#print axioms AvailableChain.V2.Engine.stateBefore_now_le_event_atRestart
#print axioms AvailableChain.V2.Engine.stateBefore_now_mono_atRestart
#print axioms AvailableChain.V2.Engine.delivery_now_ge_public_atRestart
#print axioms AvailableChain.V2.Engine.stateBefore_stable_clock_atRestart
#print axioms AvailableChain.V2.Engine.stateBefore_invariant_atRestart
#print axioms AvailableChain.V2.Engine.stateBefore_invariant
#print axioms AvailableChain.V2.Engine.stateBefore_stable_clock
#print axioms AvailableChain.V2.Engine.stateBefore_stable_clock_restore
#print axioms AvailableChain.V2.Engine.clock_field_origin
#print axioms AvailableChain.V2.Engine.stateBefore_field_prefix_restore
#print axioms AvailableChain.V2.Engine.stateBefore_tick_eq_stateBeforeTime
#print axioms AvailableChain.V2.Engine.index_lt_actionCut_iff
#print axioms AvailableChain.V2.Engine.stateBefore_tick_eq_stateAfterRestartsAt
#print axioms AvailableChain.V2.Engine.restart_index_lt_event
#print axioms AvailableChain.V2.Engine.wake_restart_before_event
#print axioms AvailableChain.V2.Engine.state_after_restart
#print axioms AvailableChain.V2.Engine.asleep_state_frozen
#print axioms AvailableChain.V2.Engine.noRestartOn_of_awakeOn
#print axioms AvailableChain.V2.Engine.noRestartAfter_of_awakeOnClosed
#print axioms AvailableChain.V2.Engine.wake_between
#print axioms AvailableChain.V2.Engine.stateBefore_stable_restore

-- Exact-time restore, restart-free interval companions.
#print axioms AvailableChain.V2.Engine.stateBefore_stable_clock_restartFree
#print axioms AvailableChain.V2.D.Engine.stateBefore_stable_clock_restartFree
