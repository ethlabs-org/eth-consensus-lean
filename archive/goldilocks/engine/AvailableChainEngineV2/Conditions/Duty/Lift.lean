module
public import AvailableChainEngineV2.Engine.Duty.Lift
public import AvailableChainEngineV2.Conditions.Committees -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Committees -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Schedule -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Schedule -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Delivery
public import AvailableChainEngineV2.Conditions.Duty.Delivery
public import AvailableChainEngineV2.Conditions.Interface -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Interface -- shake: keep (re-export)
public import AvailableChainEngineV2.Laws.Isolation -- shake: keep (re-export)
public import AvailableChainEngineV2.Laws.Duty.Isolation -- shake: keep (re-export)
public import AvailableChainEngineV2.Laws.Hooks -- shake: keep (re-export)
public import AvailableChainEngineV2.Laws.Duty.Hooks -- shake: keep (re-export)
public import AvailableChainEngineV2.Laws.SelfDelivery
public import AvailableChainEngineV2.Laws.Duty.SelfDelivery
public import AvailableChainEngineV2.Laws.Outputs
public import AvailableChainEngineV2.Laws.Duty.Outputs

@[expose] public section

namespace AvailableChain.V2

variable {In V : Type} {P : ProtocolSpec In}

abbrev LabelFamilies.toD (F : LabelFamilies P) : D.LabelFamilies P.toD :=
  ⟨F.ap, F.fresh, F.linked⟩

abbrev Interface.toD (I : Interface P) : D.Interface P.toD where
  confirmed := I.confirmed
  stable := I.stable
  block := I.block
  opening := I.opening
  propLabel := I.propLabel
  propDuty := I.propLabel
  propDuty_label := fun _ => rfl
  propLabel_single := I.propLabel_single
  propLabel_injective := I.propLabel_injective

@[simp] theorem D.apObject_toD_iff (F : V2.LabelFamilies P) (o : P.Object) :
    F.toD.APObject o ↔ F.APObject o := by
  cases o with
  | mk a p => cases a <;> rfl

abbrev Isolation.toD {F : LabelFamilies P} (iso : Isolation P F) :
    D.Isolation P.toD F.toD where
  Base := iso.Base
  base := iso.base
  clockB := iso.clockB
  clock_base := iso.clock_base
  processB := iso.processB
  process_base := iso.process_base
  recordOwn_base := iso.recordOwn_base
  actB := iso.actB
  act_base := iso.act_base
  gossipB := iso.gossipB
  gossip_base := iso.gossip_base
  depsB := iso.depsB
  processedB := iso.processedB
  excludesB := iso.excludesB
  handlesB := iso.handlesB
  hooks_base := by simpa only [D.apObject_toD_iff] using iso.hooks_base
  separation := iso.separation

abbrev D.Isolation.ofD {F : V2.LabelFamilies P} (iso : D.Isolation P.toD F.toD) :
    V2.Isolation P F where
  Base := iso.Base
  base := iso.base
  clockB := iso.clockB
  clock_base := iso.clock_base
  processB := iso.processB
  process_base := iso.process_base
  recordOwn_base := iso.recordOwn_base
  actB := iso.actB
  act_base := iso.act_base
  gossipB := iso.gossipB
  gossip_base := iso.gossip_base
  depsB := iso.depsB
  processedB := iso.processedB
  excludesB := iso.excludesB
  handlesB := iso.handlesB
  hooks_base := by simpa only [D.apObject_toD_iff] using iso.hooks_base
  separation := iso.separation

/-- Forget the redundant proposal duty in the identity lift. -/
abbrev D.Interface.ofD (I : D.Interface P.toD) : V2.Interface P where
  confirmed := I.confirmed
  stable := I.stable
  block := I.block
  opening := I.opening
  propLabel := I.propLabel
  propLabel_single := I.propLabel_single
  propLabel_injective := I.propLabel_injective

namespace D

@[simp] theorem interface_toD_iff : Nonempty (Interface P.toD) ↔ Nonempty (V2.Interface P) :=
  ⟨fun ⟨h⟩ => ⟨h.ofD⟩, fun ⟨h⟩ => ⟨h.toD⟩⟩

@[simp] theorem isolation_toD_iff (F : V2.LabelFamilies P) :
    Nonempty (Isolation P.toD F.toD) ↔ Nonempty (V2.Isolation P F) :=
  ⟨fun ⟨h⟩ => ⟨h.ofD⟩, fun ⟨h⟩ => ⟨h.toD⟩⟩

@[simp] theorem cStar_toD_iff (F : P.Label → Prop) (rho : V2.Run V P) :
    CStar F rho.toD ↔ V2.CStar F rho := Iff.rfl

@[simp] theorem linked_toD_iff (F : P.Label → Prop) (rho : V2.Run V P) :
    Linked F rho.toD ↔ V2.Linked F rho := Iff.rfl

@[simp] theorem singleSeat_toD_iff (F : P.Label → Prop) :
    SingleSeat P.toD F ↔ V2.SingleSeat P F := Iff.rfl

@[simp] theorem noRestart_toD_iff (rho : V2.Run V P) :
    NoRestart rho.toD ↔ V2.NoRestart rho := Iff.rfl

@[simp] theorem restartFree_toD_iff (rho : V2.Run V P) (v : V) (i j : Nat) :
    restartFree rho.toD v i j ↔ V2.restartFree rho v i j := Iff.rfl

@[simp] theorem proposalTime_toD (I : V2.Interface P) (s : Slot) :
    proposalTime I.toD s = V2.proposalTime I s := rfl

@[simp] theorem proposerOf_toD (rho : V2.Run V P) (I : V2.Interface P) (s : Slot) :
    proposerOf rho.toD I.toD s = V2.proposerOf rho I s := rfl

variable [DecidableEq V] (E : Generic.Env V) (rho : V2.Run V P)

omit [DecidableEq V] in
@[simp] theorem sleepWellFormed_toD_iff :
    SleepWellFormed E rho.toD ↔ V2.SleepWellFormed E rho :=
  ⟨fun h => ⟨h.tick_awake, h.deliver_awake, h.restart_awake, h.wake_restart⟩,
    fun h => ⟨h.tick_awake, h.deliver_awake, h.restart_awake, h.wake_restart⟩⟩

omit [DecidableEq V] in
@[simp] theorem restartsAtWakes_toD_iff :
    RestartsAtWakes E rho.toD ↔ V2.RestartsAtWakes E rho := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem noRestartOn_toD_iff (v : V) (a b : Time) :
    NoRestartOn rho.toD v a b ↔ V2.NoRestartOn rho v a b := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem noRestartAfter_toD_iff (v : V) (a : Time) :
    NoRestartAfter rho.toD v a ↔ V2.NoRestartAfter rho v a := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem linkReadyOn_toD_iff (src dst : V) (a d : Time) :
    LinkReadyOn E rho.toD src dst a d ↔ V2.LinkReadyOn E rho src dst a d := Iff.rfl

@[simp] theorem processedByActionCut_toD_iff (w : V) (o : P.Object) (a : Time) :
    ProcessedByActionCut E rho.toD w o a ↔ V2.ProcessedByActionCut E rho w o a := by
  unfold ProcessedByActionCut V2.ProcessedByActionCut
  simp only [stateBefore_toD]
  rfl

@[simp] theorem handledBetween_toD_iff (w : V) (o : P.Object) (a d : Time) :
    HandledBetween E rho.toD w o a d ↔ V2.HandledBetween E rho w o a d := by
  unfold HandledBetween V2.HandledBetween
  simp only [handlesAt_toD]

@[simp] theorem deliveryService_toD_iff (w : V) (o : P.Object) (a d : Time) :
    DeliveryService E rho.toD w o a d ↔ V2.DeliveryService E rho w o a d := by
  unfold DeliveryService V2.DeliveryService
  simp only [processedByActionCut_toD_iff, handledBetween_toD_iff]

@[simp] theorem deliveryDemand_toD_iff (src dst : V) (o : P.Object) (send : Time)
    (dl : Time → Time) (cut : Time) :
    DeliveryDemand E rho.toD src dst o send dl cut ↔
      V2.DeliveryDemand E rho src dst o send dl cut := by
  unfold DeliveryDemand V2.DeliveryDemand
  simp only [linkReadyOn_toD_iff, stateBeforeTime_toD, deliveryService_toD_iff]

omit [DecidableEq V] in
@[simp] theorem scheduleWellFormed_toD_iff :
    ScheduleWellFormed E rho.toD ↔ V2.ScheduleWellFormed E rho :=
  ⟨fun h => ⟨h.horizon_nonneg, h.sorted, h.nodup, h.in_horizon,
      h.honest_only, h.tick_public, h.tick_total⟩,
    fun h => ⟨h.horizon_nonneg, h.sorted, h.nodup, h.in_horizon,
      h.honest_only, h.tick_public, h.tick_total⟩⟩

@[simp] theorem deliveryWellFormed_toD_iff :
    DeliveryWellFormed E rho.toD ↔ V2.DeliveryWellFormed E rho :=
  ⟨fun h => ⟨by simpa only [stateBefore_toD] using h.wire,
      by simpa only [stateBefore_toD] using h.deps,
      by simpa only [stateBefore_toD] using h.fresh⟩,
    fun h => ⟨by simpa only [stateBefore_toD] using h.wire,
      by simpa only [stateBefore_toD] using h.deps,
      by simpa only [stateBefore_toD] using h.fresh⟩⟩

@[simp] theorem unforgeableSignatures_toD_iff :
    UnforgeableSignatures E rho.toD ↔ V2.UnforgeableSignatures E rho :=
  ⟨fun h => ⟨by simpa only [processes_toD, holder_toD, emits_toD] using h.unforgeable,
      by simpa only [processes_toD, holder_toD, emits_toD] using h.carried⟩,
    fun h => ⟨by simpa only [processes_toD, holder_toD, emits_toD] using h.unforgeable,
      by simpa only [processes_toD, holder_toD, emits_toD] using h.carried⟩⟩

@[simp] theorem partialSynchrony_toD_iff :
    PartialSynchrony E rho.toD ↔ V2.PartialSynchrony E rho :=
  ⟨fun h => ⟨by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff]
        using h.broadcast_emitted,
      by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff] using h.relay_accepted⟩,
    fun h => ⟨by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff] using h.broadcast,
      by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff] using h.relay⟩⟩

@[simp] theorem healthyPrefixDelivery_toD_iff (cut : Time) :
    HealthyPrefixDelivery E rho.toD cut ↔ V2.HealthyPrefixDelivery E rho cut :=
  ⟨fun h => ⟨by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff]
        using h.broadcast_emitted,
      by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff] using h.relay_accepted⟩,
    fun h => ⟨by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff] using h.broadcast,
      by simpa only [emits_toD, acceptsAt_toD, deliveryDemand_toD_iff] using h.relay⟩⟩

@[simp] theorem emitOk_toD_iff (st : P.State) (v : V) (t : Time) (o : P.Object) :
    EmitOk E rho.toD st v t o ↔ V2.EmitOk E rho st v t o :=
  ⟨fun h => ⟨by simpa only [tick_toD] using h.wire,
      by simpa only [tick_toD] using h.deps,
      by simpa only [tick_toD] using h.fresh,
      by simpa only [tick_toD] using h.noCarried⟩,
    fun h => ⟨by simpa only [tick_toD] using h.wire,
      by simpa only [tick_toD] using h.deps,
      by simpa only [tick_toD] using h.fresh,
      by simpa only [tick_toD] using h.noCarried⟩⟩

@[simp] theorem executionValid_toD_iff :
    ExecutionValid E rho.toD ↔ V2.ExecutionValid E rho := by
  constructor
  · intro h
    exact ⟨(scheduleWellFormed_toD_iff E rho).mp h.toScheduleWellFormed,
      (deliveryWellFormed_toD_iff E rho).mp h.toDeliveryWellFormed,
      (unforgeableSignatures_toD_iff E rho).mp h.toUnforgeableSignatures,
      (sleepWellFormed_toD_iff E rho).mp h.toSleepWellFormed⟩
  · intro h
    exact ⟨(scheduleWellFormed_toD_iff E rho).mpr h.toScheduleWellFormed,
      (deliveryWellFormed_toD_iff E rho).mpr h.toDeliveryWellFormed,
      (unforgeableSignatures_toD_iff E rho).mpr h.toUnforgeableSignatures,
      (sleepWellFormed_toD_iff E rho).mpr h.toSleepWellFormed⟩

@[simp] theorem selfDelivery_toD_iff :
    SelfDelivery E rho.toD ↔ V2.SelfDelivery E rho := by
  unfold SelfDelivery V2.SelfDelivery
  simp only [emitsAt_toD, objSelfVisible_toD]

@[simp] theorem blockInRun_toD_iff (I : V2.Interface P) (B : Block) :
    BlockInRun E I.toD rho.toD B ↔ V2.BlockInRun E I rho B := by
  unfold BlockInRun V2.BlockInRun
  simp only [processes_toD, emits_toD]

@[simp] theorem rootInjective_toD_iff (I : V2.Interface P) :
    RootInjective E I.toD rho.toD ↔ V2.RootInjective E I rho := by
  unfold RootInjective V2.RootInjective
  simp only [blockInRun_toD_iff]

@[simp] theorem outputAt_toD (g : P.State → Block) (v : V) (t : Time) :
    outputAt E rho.toD g v t = V2.outputAt E rho g v t := by
  unfold outputAt V2.outputAt
  rw [readAt_toD]

/-- The holder law has the same premises and conclusion after the lift. -/
theorem holder_of_mem_tick_toD {st : P.State} {v u : V} {t : Time} {o : P.Object}
    (ho : o ∈ (V2.tick E rho st v t).2) (hu : V2.Run.holder rho o.auth = some u) :
    u = v :=
  Run.holder_of_mem_tick (E := E) (rho := rho.toD)
    (by simpa only [tick_toD] using ho) (by simpa only [holder_toD] using hu)

omit [DecidableEq V] in
/-- Output factor data also survives the lift in both directions. -/
theorem outputsFactor_toD_iff (I : V2.Interface P) (F : V2.LabelFamilies P)
    (iso : V2.Isolation P F) :
    Nonempty (OutputsFactor I.toD iso.toD) ↔ Nonempty (V2.OutputsFactor I iso) :=
  ⟨fun ⟨h⟩ => ⟨⟨h.confirmedB, h.confirmed_base, h.stableB, h.stable_base⟩⟩,
    fun ⟨h⟩ => ⟨⟨h.confirmedB, h.confirmed_base, h.stableB, h.stable_base⟩⟩⟩

omit [DecidableEq V] in
/-- All run-level hook conditions are preserved. -/
theorem hooksSound_toD_iff : HooksSound P.toD ↔ V2.HooksSound P := by
  constructor
  · intro h
    refine ⟨h.excludes_inert, ?_, ?_, ?_, h.handles_carries,
      h.recordOwn_processed, h.recordOwn_deps, h.recordOwn_excludes⟩
    · intro V _ E rho hs v o i j hij hr hx
      have h' := h.excludes_stable E rho.toD
        ((scheduleWellFormed_toD_iff E rho).mpr hs) v o i j hij hr
        (by simpa only [stateBefore_toD] using hx)
      simpa only [stateBefore_toD] using h'
    · intro V _ E rho hs v o i j hij hr hx
      have h' := h.processed_stable E rho.toD
        ((scheduleWellFormed_toD_iff E rho).mpr hs) v o i j hij hr
        (by simpa only [stateBefore_toD] using hx)
      simpa only [stateBefore_toD] using h'
    · intro V _ E rho hs v o i j hij hr hx
      have h' := h.deps_stable E rho.toD
        ((scheduleWellFormed_toD_iff E rho).mpr hs) v o i j hij hr
        (by simpa only [stateBefore_toD] using hx)
      simpa only [stateBefore_toD] using h'
  · intro h
    refine ⟨h.excludes_inert, ?_, ?_, ?_, h.handles_carries,
      h.recordOwn_processed, h.recordOwn_deps, h.recordOwn_excludes⟩
    · intro V _ E rho hs v o i j hij hr hx
      have h' := h.excludes_stable E rho.ofD
        ((scheduleWellFormed_toD_iff E rho.ofD).mp hs) v o i j hij hr
        (by simpa only [← stateBefore_toD, Run.toD_ofD] using hx)
      simpa only [← stateBefore_toD, Run.toD_ofD] using h'
    · intro V _ E rho hs v o i j hij hr hx
      have h' := h.processed_stable E rho.ofD
        ((scheduleWellFormed_toD_iff E rho.ofD).mp hs) v o i j hij hr
        (by simpa only [← stateBefore_toD, Run.toD_ofD] using hx)
      simpa only [← stateBefore_toD, Run.toD_ofD] using h'
    · intro V _ E rho hs v o i j hij hr hx
      have h' := h.deps_stable E rho.ofD
        ((scheduleWellFormed_toD_iff E rho.ofD).mp hs) v o i j hij hr
        (by simpa only [← stateBefore_toD, Run.toD_ofD] using hx)
      simpa only [← stateBefore_toD, Run.toD_ofD] using h'

end D
end AvailableChain.V2
