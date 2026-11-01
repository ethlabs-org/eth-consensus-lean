module
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainGeneric.Statements.V2.Duty.Counts

@[expose] public section

/-! [PC-SA claims, W0] The run reads of the lane claims (pcsa-proof-plan §3).
Each read is a deterministic function of the run: a duty read is taken on the
post-clock state of the node's tick (`pcsa_postClock`), so it is defined also
for a node that is asleep at the duty time; a claim that is about a sent object
adds the awake premise. The copied generic reads stay in `Reads.lean` (the FG
lift replaces them there). -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type} [DecidableEq V]
    {m : FGMode} (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- [PC-SA claims, W0] The store of node `x` before event `i` (every event
state, also inside one time). -/
def storeBefore (i : Nat) (x : V) : State p.n :=
  (V2.D.Run.stateBefore E rho i x).st

theorem pcsa_storeBefore_def (i : Nat) (x : V) :
    storeBefore p c E rho i x = (V2.D.Run.stateBefore E rho i x).st := rfl

/-- [PC-SA claims, W0; pcsa34-r4 1.2, 3.10] The HEAD of node `x` at `v_s`:
`goldfish_vote` on the post-clock state of the tick at `v_s`. -/
def voteHeadAt (x : V) (s : Slot) : Option Block :=
  (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map (fun nd => headVote p nd.st s)

theorem pcsa_voteHeadAt_def (x : V) (s : Slot) :
    voteHeadAt p c E rho x s =
      (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
        (fun nd => headVote p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.3] `view(Σ, s)` of node `x`, read at `v_s`. -/
def viewAt (x : V) (s : Slot) : Option (Option (PC p.n)) :=
  (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map (fun nd => voterPC p nd.st s)

theorem pcsa_viewAt_def (x : V) (s : Slot) :
    viewAt p c E rho x s =
      (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
        (fun nd => voterPC p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.3 live_root] `live_root(Σ, s)` of node `x`,
read at `v_s` with the slot-`s` view. -/
def liveRootAt (x : V) (s : Slot) : Option Block :=
  (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
    (fun nd => liveRoot p nd.st (voterPC p nd.st s))

theorem pcsa_liveRootAt_def (x : V) (s : Slot) :
    liveRootAt p c E rho x s =
      (pcsa_postClock E rho x (SA.voteTime p.toParams s)).map
        (fun nd => liveRoot p nd.st (voterPC p nd.st s)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.4 A1] The N target of slot `s` at node `x`,
read at `e_s`. -/
def nTargetAt (x : V) (s : Slot) : Option (Option Block) :=
  (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map (fun nd => nTarget? p nd.st s)

theorem pcsa_nTargetAt_def (x : V) (s : Slot) :
    nTargetAt p c E rho x s =
      (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map
        (fun nd => nTarget? p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.4, 3.8] The ack decision of node `x` at
`e_s` (A1 and A2; A6 is the duty schedule). The tick at `e_s` runs the gate of
`s − 1` first, so the read is after that gate. -/
def ackAt (x : V) (s : Slot) : Option (Option Block) :=
  (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map (fun nd => ackFor p nd.st s)

theorem pcsa_ackAt_def (x : V) (s : Slot) :
    ackAt p c E rho x s =
      (pcsa_postClock E rho x (SA.earlyTime p.toParams s)).map
        (fun nd => ackFor p nd.st s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.8] An honest ack `(s, B)`: node `x` is
honest, awake at `e_s`, and its ack decision is `B` (the ack duty then sends
`(i, s, B)` for its seat `i`). -/
def HonestAckAt (x : V) (s : Slot) (B : Block) : Prop :=
  x ∈ rho.honest ∧ E.awake x (SA.earlyTime p.toParams s) = true ∧
    ackAt p c E rho x s = some (some B)

theorem pcsa_HonestAckAt_def (x : V) (s : Slot) (B : Block) :
    HonestAckAt p c E rho x s B =
      (x ∈ rho.honest ∧ E.awake x (SA.earlyTime p.toParams s) = true ∧
        ackAt p c E rho x s = some (some B)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 1.2] An honest HEAD of label `s`: node `x` is
honest, awake at `v_s`, and its HEAD at `v_s` is `H`. -/
def HonestHeadAt (x : V) (s : Slot) (H : Block) : Prop :=
  x ∈ rho.honest ∧ E.awake x (SA.voteTime p.toParams s) = true ∧
    voteHeadAt p c E rho x s = some H

theorem pcsa_HonestHeadAt_def (x : V) (s : Slot) (H : Block) :
    HonestHeadAt p c E rho x s H =
      (x ∈ rho.honest ∧ E.awake x (SA.voteTime p.toParams s) = true ∧
        voteHeadAt p c E rho x s = some H) := rfl

/-- [PC-SA claims, W0; FG-SA gateIn] The gate input of label `s` at node `x`:
the clock steps before the gate at `d_s`. -/
def gateInAt (x : V) (s : Slot) : Option (State p.n) :=
  (pcsa_preTick E rho x (SA.gateTime p.toParams s)).map
    (fun nd => clockPre p nd.st (SA.gateTime p.toParams s))

theorem pcsa_gateInAt_def (x : V) (s : Slot) :
    gateInAt p c E rho x s =
      (pcsa_preTick E rho x (SA.gateTime p.toParams s)).map
        (fun nd => clockPre p nd.st (SA.gateTime p.toParams s)) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.7, 5.0 R_u(j); FG-SA gateResult] The raw
gate result `R_x(s)` of label `s` at node `x`, before the guard: the walk from
`F` over the active view. `some none` is an empty result. -/
def gateResultAt (x : V) (s : Slot) : Option (Option Block) :=
  (gateInAt p c E rho x s).map (fun st =>
    SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s)

theorem pcsa_gateResultAt_def (x : V) (s : Slot) :
    gateResultAt p c E rho x s =
      (gateInAt p c E rho x s).map (fun st =>
        SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 1.4, 3.3] `PC(s, B)` is stamped before the
tick time `t` at node `y`: it is held after the ticks at `t`, before the
deliveries at `t` (an object accepted strictly before a tick time has a stamp
below it; the freeze at `t` reads exactly these PCs). -/
def PCStampedBefore (y : V) (t : Time) (s : Slot) (B : Block) : Prop :=
  ∃ c' ∈ (storeAfterTicks p c E rho y t).pcs, c'.slot = s ∧ c'.target = B

theorem pcsa_PCStampedBefore_def (y : V) (t : Time) (s : Slot) (B : Block) :
    PCStampedBefore p c E rho y t s B =
      (∃ c' ∈ (storeAfterTicks p c E rho y t).pcs, c'.slot = s ∧ c'.target = B) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 3.9, R8′] The FG source `C_fg` of node `x` at
the action time `a_r` of round `r`. -/
def actionSourceAt (x : V) (r : Nat) : Option (Option (FGBlock (Fin p.n))) :=
  (pcsa_postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st)

theorem pcsa_actionSourceAt_def (x : V) (r : Nat) :
    actionSourceAt p c E rho x r =
      (pcsa_postClock E rho x (p.actionTime r)).map (fun nd => fgSource p nd.st) := rfl

/-- [PC-SA claims, W0; pcsa34-r4 5.4.1] Every honest event state from time
`t`: the store of each honest node after every event `i` whose time is at
least `t` (also the intermediate states inside one time). -/
def HonestStatesFrom (t : Time) (P : State p.n → Prop) : Prop :=
  ∀ x ∈ rho.honest, ∀ (i : Nat) e, rho.events[i]? = some e → t ≤ e.time →
    P (storeBefore p c E rho (i + 1) x)

theorem pcsa_HonestStatesFrom_def (t : Time) (P : State p.n → Prop) :
    HonestStatesFrom p c E rho t P =
      (∀ x ∈ rho.honest, ∀ (i : Nat) e, rho.events[i]? = some e → t ≤ e.time →
        P (storeBefore p c E rho (i + 1) x)) := rfl

/-- [PC-SA claims, W0; q0-pc.md §2 "through a_r"] Every honest event state up
to time `t`: the initial store and the store of each honest node after every
event whose time is at most `t`. -/
def HonestStatesThrough (t : Time) (P : State p.n → Prop) : Prop :=
  ∀ x ∈ rho.honest, ∀ i : Nat,
    (i = 0 ∨ ∃ e, rho.events[i - 1]? = some e ∧ e.time ≤ t) →
    P (storeBefore p c E rho i x)

theorem pcsa_HonestStatesThrough_def (t : Time) (P : State p.n → Prop) :
    HonestStatesThrough p c E rho t P =
      (∀ x ∈ rho.honest, ∀ i : Nat,
        (i = 0 ∨ ∃ e, rho.events[i - 1]? = some e ∧ e.time ≤ t) →
        P (storeBefore p c E rho i x)) := rfl

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [PC-SA claims, W0; pcsa34-r4 5.4.1 "justified at an honest node";
FG-SA Window.Entry "a retained justification"] The justification evidence of
a store: `X` is justified at height `h` when it is the stored pair
`(h_j, J)`, or the justification pair or a retained window entry of the
window state of a held FG block.
QC set read (also by `Q0PCPackage.ff2` for FF2's "QCs name E_h"): a QC at
height `h` on `X` is a justification `(h, X)` that the store holds in one of
these three places. Window entries are justifications by construction
(FG-SA `Window.Entry`: "a retained justification"); a row set below the
quorum is not a QC and is not read. -/
def HeldJustification (p : Params) (st : State p.n) (h : Nat) (X : FGBlock (Fin p.n)) :
    Prop :=
  (st.fg.h_j = h ∧ st.fg.J = X) ∨
    ∃ B ∈ st.fg.TF,
      ((FGSA.Window.derive p p.K_W B).h_j = h ∧ (FGSA.Window.derive p p.K_W B).J = X) ∨
        ∃ en ∈ (FGSA.Window.derive p p.K_W B).W, en.j = h ∧ en.X = X

theorem pcsa_HeldJustification_def (p : Params) (st : State p.n) (h : Nat)
    (X : FGBlock (Fin p.n)) :
    HeldJustification p st h X =
      ((st.fg.h_j = h ∧ st.fg.J = X) ∨
        ∃ B ∈ st.fg.TF,
          ((FGSA.Window.derive p p.K_W B).h_j = h ∧ (FGSA.Window.derive p p.K_W B).J = X) ∨
            ∃ en ∈ (FGSA.Window.derive p p.K_W B).W, en.j = h ∧ en.X = X) := rfl

end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA

/-- [PC-SA claims, W0; pcsa34-r4 3.1, 3.7] A live lease on `B` in the store:
a lease row on `B` whose deadline is after the store time. -/
def LiveLease {n : Nat} (st : State n) (B : Block) : Prop :=
  ∃ row ∈ st.base.obligations, row.1 = B ∧ st.base.now < row.2.2

theorem pcsa_LiveLease_def {n : Nat} (st : State n) (B : Block) :
    LiveLease st B = (∃ row ∈ st.base.obligations, row.1 = B ∧ st.base.now < row.2.2) := rfl

end AvailableChain.PCSA

end
