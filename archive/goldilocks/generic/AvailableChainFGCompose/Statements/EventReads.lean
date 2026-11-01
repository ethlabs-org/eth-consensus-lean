module
public import AvailableChainGeneric.Statements.V2.Duty.Reads -- shake: keep (Compose import policy)

@[expose] public section
namespace AvailableChain.FGCompose
variable {V In : Type} {P : V2.ProtocolSpecD In}
def cutPred (t : Time) (e : V2.Event V P.Object) : Bool := decide (e.key ≤ toLex (t, 1))
theorem cutPred_def (t : Time) (e : V2.Event V P.Object) :
    cutPred t e = decide (e.key ≤ toLex (t, 1)) := rfl
def afterTicksIdx (rho : V2.D.Run V P) (t : Time) : Nat := (rho.events.filter (cutPred t)).length
theorem afterTicksIdx_def (rho : V2.D.Run V P) (t : Time) :
    afterTicksIdx rho t = (rho.events.filter (cutPred t)).length := rfl
def timeIdx (rho : V2.D.Run V P) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).length
theorem timeIdx_def (rho : V2.D.Run V P) (t : Time) :
    timeIdx rho t = (rho.events.filter (fun e => decide (e.time ≤ t))).length := rfl
variable [DecidableEq V]
def afterTicks (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) : V2.D.World V P :=
  (rho.events.filter (cutPred t)).foldl (V2.D.World.step E rho) V2.D.World.init
theorem afterTicks_def (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) :
    afterTicks E rho t =
      (rho.events.filter (cutPred t)).foldl (V2.D.World.step E rho) V2.D.World.init := rfl
def preTick (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) : Option P.State :=
  (V2.D.Run.tickIdx? rho x t).map (fun i => V2.D.Run.stateBefore E rho i x)
theorem preTick_def (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) :
    preTick E rho x t =
      (V2.D.Run.tickIdx? rho x t).map (fun i => V2.D.Run.stateBefore E rho i x) := rfl
def postClock (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) : Option P.State :=
  (preTick E rho x t).map (fun nd => P.clock nd t)
theorem postClock_def (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) :
    postClock E rho x t = (preTick E rho x t).map (fun nd => P.clock nd t) := rfl
def postTick (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) : Option P.State :=
  (V2.D.Run.tickIdx? rho x t).map (fun i => V2.D.Run.stateBefore E rho (i + 1) x)
theorem postTick_def (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) :
    postTick E rho x t =
      (V2.D.Run.tickIdx? rho x t).map (fun i => V2.D.Run.stateBefore E rho (i + 1) x) := rfl

end AvailableChain.FGCompose
end
