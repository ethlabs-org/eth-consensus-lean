module
public import AvailableChainGeneric.Statements.V2.Duty.Reads -- shake: keep (Claims import policy)
public import AvailableChainFGSARun.Model.Protocol

@[expose] public section

/-! Generic reads over the real v2 engine (P3 F0.1). -/

namespace AvailableChain.FGSA.Run

variable {V : Type} {In : Type} {P : V2.ProtocolSpecD In}

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Include earlier events and the restarts and ticks at `t`, before deliveries. -/
def cutPred (t : Time) (e : V2.Event V P.Object) : Bool :=
  decide (e.key ≤ toLex (t, 1))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The event index after all ticks at `t`. -/
def afterTicksIdx (rho : V2.D.Run V P) (t : Time) : Nat :=
  (rho.events.filter (cutPred t)).length

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Event states in the suffix that starts at the post-gate cut. -/
def SuffixIdx (rho : V2.D.Run V P) (t : Time) (i : Nat) : Prop :=
  afterTicksIdx rho t ≤ i ∧ i ≤ rho.events.length

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The inclusive event index at `t`. -/
def timeIdx (rho : V2.D.Run V P) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).length

variable [DecidableEq V]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The world after all ticks at `t`, before its deliveries. -/
def afterTicks (E : Generic.Env V) (rho : V2.D.Run V P) (t : Time) : V2.D.World V P :=
  (rho.events.filter (cutPred t)).foldl (V2.D.World.step E rho) V2.D.World.init

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The local state before the node's tick, if that tick exists. -/
def preTick (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) : Option P.State :=
  (V2.D.Run.tickIdx? rho v t).map (fun i => V2.D.Run.stateBefore E rho i v)

-- equation export required by BUILD §7.2 B3a
theorem preTick_def (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) :
    preTick E rho v t =
      (V2.D.Run.tickIdx? rho v t).map (fun i => V2.D.Run.stateBefore E rho i v) := by
  rw [preTick]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The local state after the clock, before the own record. -/
def postClock (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) : Option P.State :=
  (preTick E rho v t).map (fun nd => P.clock nd t)

-- equation export required by BUILD §7.2 B3a
theorem postClock_def (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) :
    postClock E rho v t = (preTick E rho v t).map (fun nd => P.clock nd t) := by
  rw [postClock]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The local state after the node's complete tick, if that tick exists. -/
def postTick (E : Generic.Env V) (rho : V2.D.Run V P) (v : V) (t : Time) : Option P.State :=
  (V2.D.Run.tickIdx? rho v t).map (fun i => V2.D.Run.stateBefore E rho (i + 1) v)

end AvailableChain.FGSA.Run


namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
local instance (w : Option Time) (cut : Time) :
    Decidable (match w with | none => True | some t => t ≤ cut) := by
  cases w <;> dsimp <;> infer_instance

variable (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The store before event `i`. -/
def storeAt (i : Nat) (x : V) : FGSA.State p.n :=
  (V2.D.Run.stateBefore E rho i x).st

def S_at (i : Nat) (x : V) : Block := (storeAt p c E rho i x).base.stableRecord
def F_at (i : Nat) (x : V) : Block := eraseFG (storeAt p c E rho i x).fg.F
def J_at (i : Nat) (x : V) : Block := eraseFG (storeAt p c E rho i x).fg.J

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The gate input includes the clock steps before the gate. -/
def gateIn (x : V) (s : Slot) : Option (FGSA.State p.n) :=
  (preTick E rho x (SA.gateTime p.toParams s)).map
    (fun nd => FGSA.clockPre p nd.st (SA.gateTime p.toParams s))

-- equation export required by BUILD §7.2 B3a
theorem gateIn_def (x : V) (s : Slot) :
    gateIn p c E rho x s =
      (preTick E rho x (SA.gateTime p.toParams s)).map
        (fun nd => FGSA.clockPre p nd.st (SA.gateTime p.toParams s)) := by
  rw [gateIn]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The raw genuine result, before the guard, with the walk anchored at F. -/
def gateResult (x : V) (s : Slot) : Option (Option Block) :=
  (gateIn p c E rho x s).map (fun st =>
    if (match st.restartTime with
        | none => True
        | some w => w ≤ (4 * p.Δ * (s : Int))) then
      SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s
    else none)

-- equation export required by BUILD §7.2 B3a
theorem gateResult_def (x : V) (s : Slot) :
    gateResult p c E rho x s =
  ((gateIn p c E rho x s).map (fun st =>
    if (match st.restartTime with
        | none => True
        | some w => w ≤ (4 * p.Δ * (s : Int))) then
      SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s
    else none)) := by
  rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The clock's decidable gate-time test. -/
def isGateTime (p : Params) (t : Time) : Bool :=
  decide (0 ≤ t - 6 * p.Δ) &&
    t == SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat

-- equation export required by BUILD §7.2 B3a
theorem isGateTime_def (p : Params) (t : Time) :
    isGateTime p t =
      (decide (0 ≤ t - 6 * p.Δ) &&
        t == SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat) := by
  rw [isGateTime]

def IsGateTick (j : Nat) (x : V) (s : Slot) : Prop :=
  rho.events[j]? = some (.tick x (SA.gateTime p.toParams s))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The raw gate result at a tick index. -/
def gateResultAt (j : Nat) : Option (Option Block) :=
  match rho.events[j]? with
  | some (.tick x t) =>
      if isGateTime p t then
        let st := FGSA.clockPre p (V2.D.Run.stateBefore E rho j x).st t
        some (if (match st.restartTime with
          | none => True
          | some w => w ≤ (4 * p.Δ * (((t - 6 * p.Δ) / (4 * p.Δ)).toNat : Int)))
        then SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st)
          ((t - 6 * p.Δ) / (4 * p.Δ)).toNat else none)
      else none
  | _ => none

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The fast test on the active view before the gate. -/
def fastAt (x : V) (s : Slot) (B : Block) : Prop :=
  ∃ st, gateIn p c E rho x s = some st ∧
    SA.releaseThreshold p.toParams ≤ SA.Root.prefixSupport p.toParams (FGSA.actView st) s B

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The HEAD computation on the post-clock state of event `k`. -/
def headAtIdx (k : Nat) (s : Slot) : Block :=
  match rho.events[k]? with
  | some (.tick y t) => FGSA.headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y) t).st s
  | _ => .genesis

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The deterministic HEAD read at the next vote time, also for asleep nodes. -/
def vHead (y : V) (s : Slot) : Option Block :=
  (postClock E rho y (SA.voteTime p.toParams (s + 1))).map
    (fun nd => FGSA.headVote p nd.st (s + 1))

-- equation export required by BUILD §7.2 B3a
theorem vHead_def (y : V) (s : Slot) :
    vHead p c E rho y s =
      (postClock E rho y (SA.voteTime p.toParams (s + 1))).map
        (fun nd => FGSA.headVote p nd.st (s + 1)) := by
  rw [vHead]

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The FG-typed source of the action at round `r`. -/
def actionSourceFG (x : V) (r : Nat) : Option (Option (FGBlock (Fin p.n))) :=
  (postClock E rho x (p.actionTime r)).map (fun nd => FGSA.fgSource p nd.st)

-- equation export required by BUILD §7.2 B3a
theorem actionSourceFG_def (x : V) (r : Nat) :
    actionSourceFG p c E rho x r =
      (postClock E rho x (p.actionTime r)).map (fun nd => FGSA.fgSource p nd.st) := by
  rw [actionSourceFG]

def actionSource (x : V) (r : Nat) : Option (Option Block) :=
  (actionSourceFG p c E rho x r).map (Option.map eraseFG)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The largest gate label at the event time, or at the horizon past the list. -/
def labelBoundAt (i : Nat) : Slot :=
  match rho.events[i]? with
  | some e => ((e.time - 6 * p.Δ) / (4 * p.Δ)).toNat
  | none => ((rho.horizon - 6 * p.Δ) / (4 * p.Δ)).toNat

def DeliveredAt (j : Nat) (o : (fgsa p c).Object) : Prop :=
  ∃ v t, rho.events[j]? = some (.deliver v o t)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Direct and carried handler calls for the signed row, through `ofRow`. -/
def HandlesRowAt (k : Nat) (x : V) (a : RowWire p.n) : Prop :=
  ∃ t, V2.D.Run.handlesAt E rho k x (ofRow p a) t

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Finalization in the strict-before state; the definition also permits restarts. -/
def AcceptsFinalBefore (x : V) (X : FGBlock (Fin p.n)) (d : Time) : Prop :=
  Gen.V2.Duty.HoldsBefore E rho (fun nd => FGBlock.Preceq X nd.st.fg.F) d x

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Labelled raw results of gate ticks before index `i` (P3 §8.2). -/
def cleanResults (i : Nat) : Set (Slot × Block) :=
  {sB | ∃ j < i, ∃ x, IsGateTick p c rho j x sB.1 ∧
    (match (storeAt p c E rho j x).restartTime with
     | none => True
     | some w => w ≤ 4 * p.Δ * (sB.1 : Int)) ∧
    gateResultAt p c E rho j = some (some sB.2)}

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
An ancestor of a Clean result whose label is at most `r`, or genesis. -/
def BelowLabel (i : Nat) (r : Slot) (X : Block) : Prop :=
  X = .genesis ∨ ∃ s B, (s, B) ∈ cleanResults p c E rho i ∧ s ≤ r ∧ Block.Preceq X B

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem S_at_def (i : Nat) (x : V) :
    S_at p c E rho i x = (storeAt p c E rho i x).base.stableRecord := rfl

def diagnosticGateResult (x : V) (s : Slot) : Option (Option Block) :=
  (gateIn p c E rho x s).map (fun st =>
    SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st) s)

end AvailableChain.FGSA.Run

end
