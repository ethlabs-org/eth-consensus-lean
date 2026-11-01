module
public import AvailableChainFGCompose.Statements.EventReads
public import AvailableChainGeneric.Statements.V2.Duty.Reads -- shake: keep (Claims import policy)
public import AvailableChainPCSARun.Model.Protocol

@[expose] public section

/-! [PC-SA claims; FG-SA Claims/Statements/Reads.lean, mech copy] Generic reads
over the real v2 engine, and the PC-SA store reads. -/

namespace AvailableChain.PCSA.Run

variable {V : Type} {In : Type} {P : V2.ProtocolSpecD In}

/-- Include earlier events and the restarts and ticks at `t`, before deliveries. -/
def cutPred (t : Time) (e : V2.Event V P.Object) : Bool :=
  FGCompose.cutPred (P := P) t e

/-- The event index after all ticks at `t`. -/
def afterTicksIdx (rho : V2.D.Run V P) (t : Time) : Nat :=
  FGCompose.afterTicksIdx (P := P) rho t

variable [DecidableEq V]

/-- The world after all ticks at `t`, before its deliveries. -/
def afterTicks (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) : V2.D.World V P :=
  FGCompose.afterTicks (P := P) E rho t

/-- The local state before the node's tick, if that tick exists. -/
def pcsa_preTick (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) : Option P.State :=
  FGCompose.preTick (P := P) E rho v t

theorem pcsa_preTick_def (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) :
    pcsa_preTick E rho v t =
      (V2.D.Run.tickIdx? rho v t).map (fun i => V2.D.Run.stateBefore E rho i v) := rfl

/-- The local state after the clock, before the own record. -/
def pcsa_postClock (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) : Option P.State :=
  FGCompose.postClock (P := P) E rho v t

theorem pcsa_postClock_def (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) :
    pcsa_postClock E rho v t = (pcsa_preTick E rho v t).map (fun nd => P.clock nd t) := rfl

variable (p : Params) {In : Type} (c : AppCodec In) {m : FGMode}

/-- [PC-SA claims] The store of node `x` after the events up to `t` inclusive. -/
def storeAt (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) :
    State p.n :=
  (V2.D.Run.readAt E rho t x).st

theorem storeAt_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) :
    storeAt p c E rho x t = (V2.D.Run.readAt E rho t x).st := by
  rw [storeAt]

/-- [PC-SA claims] The store of node `x` after the ticks at `t`, before the
deliveries of `t` (the state the snapshot and the duties at `t` read). -/
def storeAfterTicks (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) :
    State p.n :=
  (afterTicks E rho t x).st

theorem storeAfterTicks_def (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c)) (x : V)
    (t : Time) : storeAfterTicks p c E rho x t = (afterTicks E rho t x).st := by
  rw [storeAfterTicks]

/-- [PC-SA claims] The v2 ack object of seat `i` at slot `s` on the root `r`. -/
def ackObj (s : Slot) (i : Fin p.n) (r : BlockId) : Obj p :=
  ⟨.seat (.base (.ack s)) i, .ack r⟩

theorem ackObj_def (s : Slot) (i : Fin p.n) (r : BlockId) :
    ackObj p s i r = ⟨.seat (.base (.ack s)) i, .ack r⟩ := rfl

end AvailableChain.PCSA.Run
end
