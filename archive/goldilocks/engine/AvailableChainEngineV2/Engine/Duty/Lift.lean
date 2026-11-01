module
public import AvailableChainEngineV2.Engine.Duty.Run
public import AvailableChainEngineV2.Conditions.Duty.Duties

@[expose] public section

namespace AvailableChain.V2

/-- The identity lift keeps all old protocol fields. -/
abbrev ProtocolSpec.toD {In : Type} (P : ProtocolSpec In) : ProtocolSpecD In where
  Duty := P.Label
  signLabel := id
  State := P.State
  Label := P.Label
  seats := P.seats
  Payload := P.Payload
  Durable := P.Durable
  init := P.init
  clock := P.clock
  actTime := P.actTime
  duties := P.duties
  duties_spec := P.duties_spec
  duties_nodup := P.duties_nodup
  act := P.act
  gossip := P.gossip
  process := P.process
  selfVisible := P.selfVisible
  recordOwn := P.recordOwn
  durable := P.durable
  restore := P.restore
  wellFormed := P.wellFormed
  depsPresent := P.depsPresent
  processed := P.processed
  excludes := P.excludes
  handles := P.handles
  carries := P.carries

/-- Run data is unchanged by the identity lift. -/
abbrev Run.toD {V In : Type} {P : ProtocolSpec In} (rho : Run V P) : D.Run V P.toD where
  honest := rho.honest
  horizon := rho.horizon
  events := rho.events
  seatOf := rho.seatOf
  input := rho.input

/-- Every run of an identity-lifted protocol has an old run. -/
abbrev D.Run.ofD {V In : Type} {P : ProtocolSpec In} (rho : D.Run V P.toD) : V2.Run V P where
  honest := rho.honest
  horizon := rho.horizon
  events := rho.events
  seatOf := rho.seatOf
  input := rho.input

namespace D

variable {V In : Type} {P : ProtocolSpec In}

@[simp] theorem Run.toD_ofD (rho : Run V P.toD) : rho.ofD.toD = rho := rfl
@[simp] theorem Run.ofD_toD (rho : V2.Run V P) : rho.toD.ofD = rho := rfl

theorem dutiesInjectiveAt_toD (t : Time) : DutiesInjectiveAt P.toD t :=
  fun _ _ _ _ h => h

@[simp] theorem objSelfVisible_toD : P.toD.objSelfVisible = P.objSelfVisible := by
  funext o
  cases o with
  | mk a p => cases a <;> rfl

variable [DecidableEq V] (E : Generic.Env V) (rho : V2.Run V P)

@[simp] theorem tick_toD (st : P.State) (v : V) (t : Time) :
    tick E rho.toD st v t = V2.tick E rho st v t := by
  unfold tick V2.tick
  rw [objSelfVisible_toD]
  rfl

omit [DecidableEq V] in
@[simp] theorem world_init_toD : (World.init : World V P.toD) = V2.World.init := rfl

@[simp] theorem world_step_toD :
    World.step E rho.toD = V2.World.step E rho := by
  funext w e
  cases e with
  | restart => rfl
  | deliver => rfl
  | tick v t => simp only [World.step, V2.World.step, tick_toD]

@[simp] theorem stateBefore_toD (j : Nat) :
    Run.stateBefore E rho.toD j = V2.Run.stateBefore E rho j := by
  unfold Run.stateBefore V2.Run.stateBefore
  rw [world_step_toD]
  rfl

@[simp] theorem stateBeforeTime_toD (t : Time) :
    Run.stateBeforeTime E rho.toD t = V2.Run.stateBeforeTime E rho t := by
  unfold Run.stateBeforeTime V2.Run.stateBeforeTime
  rw [world_step_toD]
  rfl

@[simp] theorem readAt_toD (t : Time) :
    Run.readAt E rho.toD t = V2.Run.readAt E rho t := by
  unfold Run.readAt V2.Run.readAt
  rw [world_step_toD]
  rfl

@[simp] theorem final_toD : Run.final E rho.toD = V2.Run.final E rho := by
  unfold Run.final V2.Run.final
  rw [world_step_toD]
  rfl

@[simp] theorem emitsAt_toD (j : Nat) :
    Run.emitsAt E rho.toD j = V2.Run.emitsAt E rho j := by
  unfold Run.emitsAt V2.Run.emitsAt
  simp only [stateBefore_toD, tick_toD]
  cases he : rho.events[j]? with
  | none => rfl
  | some e => cases e <;> rfl

@[simp] theorem tickIdx_toD (v : V) (t : Time) :
    Run.tickIdx? rho.toD v t = V2.Run.tickIdx? rho v t := by
  unfold Run.tickIdx? V2.Run.tickIdx?
  congr 1
  funext e
  cases e <;> rfl

@[simp] theorem emittedAt_toD (v : V) (t : Time) :
    Run.emittedAt E rho.toD v t = V2.Run.emittedAt E rho v t := by
  unfold Run.emittedAt V2.Run.emittedAt
  rw [tickIdx_toD]
  cases rho.tickIdx? v t <;> simp only [emitsAt_toD]

@[simp] theorem emits_toD (v : V) (o : P.Object) (t : Time) :
    Run.emits E rho.toD v o t ↔ V2.Run.emits E rho v o t := by
  unfold Run.emits V2.Run.emits
  simp only [emitsAt_toD]

omit [DecidableEq V] in
@[simp] theorem processes_toD (v : V) (o : P.Object) (t : Time) :
    Run.processes rho.toD v o t ↔ V2.Run.processes rho v o t := Iff.rfl

@[simp] theorem handlesAt_toD (j : Nat) (v : V) (o : P.Object) (t : Time) :
    Run.handlesAt E rho.toD j v o t ↔ V2.Run.handlesAt E rho j v o t := by
  unfold Run.handlesAt V2.Run.handlesAt
  rw [stateBefore_toD]

@[simp] theorem acceptsAt_toD (j : Nat) (v : V) (o : P.Object) (t : Time) :
    Run.acceptsAt E rho.toD j v o t ↔ V2.Run.acceptsAt E rho j v o t := by
  unfold Run.acceptsAt V2.Run.acceptsAt
  rw [handlesAt_toD, stateBefore_toD, stateBefore_toD]

omit [DecidableEq V] in
@[simp] theorem holder_toD (a : Auth P.Label P.seats) :
    Run.holder rho.toD a = V2.Run.holder rho a := by
  cases a <;> rfl

end D
end AvailableChain.V2
