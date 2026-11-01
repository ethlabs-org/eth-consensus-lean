module
public import Mathlib.Data.Fintype.Card
public import AvailableChainModel.Generic.Env
public import AvailableChainStatements.Generic.Constants
public import AvailableChainStatements.Generic.Properties

@[expose] public section

namespace AvailableChain.Statements.Generic

open AvailableChain

variable {V : Type} {n : Nat} {P : AvailableChain.Generic.ProtocolSpec n}
  [DecidableEq V] [_root_.Fintype V]

/-- Genesis and every ancestor (including the tip itself) of a block
named by `I.block` in a delivered or emitted payload. -/
def BlockInRun (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) (B : Block) : Prop :=
  B = .genesis ∨ ∃ v o t tip,
    (AvailableChain.Generic.Run.processes P rho v o t ∨
      AvailableChain.Generic.Run.emits P E rho v o t) ∧
    I.block o.payload = some tip ∧ Block.Preceq B tip

/-- Injectivity of block roots on genesis and the ancestors of all blocks
named by this run. Roots are computed from block content, and
ROOT-DIGEST W1 keeps this as an explicit DC-style run premise
proves it. -/
def RootInjective (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) : Prop :=
  ∀ B C, BlockInRun E I rho B → BlockInRun E I rho C →
    B.root = C.root → B = C

/-- A public time is an integer multiple of the environment's time unit. -/
def PublicTime (E : AvailableChain.Generic.Env V) (t : Time) : Prop :=
  ∃ k : Nat, t = (k : Time) * E.Δ

/-- The event schedule is sorted, finite, honest-only, and total on public times. -/
structure ScheduleWellFormed
    (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_public : ∀ v t,
    AvailableChain.Generic.Event.tick v t ∈ rho.events → PublicTime E t
  tick_total : ∀ v ∈ rho.honest, ∀ t, PublicTime E t → 0 ≤ t → t ≤ rho.horizon →
    AvailableChain.Generic.Event.tick v t ∈ rho.events

/-- Delivered objects satisfy the wire, dependency, and freshness checks. -/
structure DeliveryWellFormed
    (P : AvailableChain.Generic.ProtocolSpec n)
    (rho : AvailableChain.Generic.Run V P) : Prop where
  wire : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (AvailableChain.Generic.Event.deliver v o t) →
      P.wellFormed o = true
  deps : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (AvailableChain.Generic.Event.deliver v o t) →
      P.depsPresent (AvailableChain.Generic.Run.stateBefore P rho i v) o = true
  fresh : ∀ (i : Nat) (v : V) (o : P.Object) (t : Time),
    rho.events[i]? = some (AvailableChain.Generic.Event.deliver v o t) →
      P.processed (AvailableChain.Generic.Run.stateBefore P rho i v) o = false

/-- Signatures are unforgeable: an object whose authentication an honest
validator holds (a seat assigned to it, or its proposer key), delivered
directly or carried by a delivered object, was emitted by that validator.
Faulty holders are unconstrained: they can sign any number of objects at any
time. Unsigned objects are unconstrained. -/
structure UnforgeableSignatures
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) : Prop where
  unforgeable : ∀ v o t,
    AvailableChain.Generic.Run.processes P rho v o t →
      ∀ u ∈ rho.honest, AvailableChain.Generic.Run.holder P rho o.auth = some u →
        ∃ t', t' ≤ t ∧ AvailableChain.Generic.Run.emits P E rho u o t'
  carried : ∀ v o t,
    AvailableChain.Generic.Run.processes P rho v o t →
      ∀ o', P.carries o o' → ∀ u ∈ rho.honest,
        AvailableChain.Generic.Run.holder P rho o'.auth = some u →
        ∃ t', t' ≤ t ∧ AvailableChain.Generic.Run.emits P E rho u o' t'

/-- Valid execution. Asleep nodes need no extra field: the engine gates
emission on `awake`, and a tick changes the state only through `clock`. -/
structure ExecutionValid
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) : Prop extends
  ScheduleWellFormed E rho, DeliveryWellFormed P rho, UnforgeableSignatures P E rho

omit [_root_.Fintype V] in
/-- The initial state at time zero follows from nonnegative event times. -/
theorem ExecutionValid.cleanStart {E : AvailableChain.Generic.Env V}
    {rho : AvailableChain.Generic.Run V P} (h : ExecutionValid P E rho)
    (v : V) : AvailableChain.Generic.Run.stateBeforeTime P rho 0 v = P.init := by
  unfold AvailableChain.Generic.Run.stateBeforeTime
  have hempty : rho.events.filter (fun e => decide (e.time < 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simpa using (not_lt.mpr (h.in_horizon e he).1)
  simp [hempty, AvailableChain.Generic.World.init]

/-- Broadcast and accepted-object relay complete after GST,
except for objects excluded by the receiver at the deadline. -/
structure PartialSynchrony
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    AvailableChain.Generic.Run.emits P E rho v o t → ∀ w ∈ rho.honest,
      max t E.t_GST + E.Δ ≤ rho.horizon →
        P.excludes
            (AvailableChain.Generic.Run.stateBeforeTime P rho
              (max t E.t_GST + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < max t E.t_GST + E.Δ ∧
          ∃ j, AvailableChain.Generic.Run.handlesAt P rho j w o t'
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    AvailableChain.Generic.Run.acceptsAt P rho i v o t → ∀ w ∈ rho.honest,
      P.processed
          (AvailableChain.Generic.Run.stateBefore P rho (i + 1) w) o = false →
        max t E.t_GST + E.Δ ≤ rho.horizon →
        P.excludes
            (AvailableChain.Generic.Run.stateBeforeTime P rho
              (max t E.t_GST + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < max t E.t_GST + E.Δ ∧
            ∃ j, AvailableChain.Generic.Run.handlesAt P rho j w o t'

/-- The same broadcast and relay guarantees on a finite healthy prefix, with the same exclusion. -/
structure HealthyPrefixDelivery
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    AvailableChain.Generic.Run.emits P E rho v o t → ∀ w ∈ rho.honest,
      t + E.Δ ≤ cut →
        P.excludes
            (AvailableChain.Generic.Run.stateBeforeTime P rho
              (t + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧
          ∃ j, AvailableChain.Generic.Run.handlesAt P rho j w o t'
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    AvailableChain.Generic.Run.acceptsAt P rho i v o t → ∀ w ∈ rho.honest,
      P.processed
          (AvailableChain.Generic.Run.stateBefore P rho (i + 1) w) o = false →
        t + E.Δ ≤ cut →
        P.excludes
            (AvailableChain.Generic.Run.stateBeforeTime P rho
              (t + E.Δ) w) o = false →
        ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧
            ∃ j, AvailableChain.Generic.Run.handlesAt P rho j w o t'

/-- Relay of an accepted object to acceptance at every honest reader. -/
def AcceptedObjectRelay (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) : Prop :=
  ∀ v ∈ rho.honest, ∀ i o t,
    AvailableChain.Generic.Run.acceptsAt P rho i v o t →
    ∀ w ∈ rho.honest,
      P.processed (AvailableChain.Generic.Run.stateBefore P rho (i + 1) w) o = false →
      max t E.t_GST + E.Δ ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < max t E.t_GST + E.Δ ∧
        ∃ j, AvailableChain.Generic.Run.acceptsAt P rho j w o t'

/-- Accepted-object relay on a healthy finite prefix. -/
def HealthyAcceptedObjectRelay (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) (cut : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ i o t,
    AvailableChain.Generic.Run.acceptsAt P rho i v o t →
    ∀ w ∈ rho.honest,
      P.processed (AvailableChain.Generic.Run.stateBefore P rho (i + 1) w) o = false →
      t + E.Δ ≤ cut →
      ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧
        ∃ j, AvailableChain.Generic.Run.acceptsAt P rho j w o t'

/-- Honest validators awake at `t`. -/
def awakeAt (E : AvailableChain.Generic.Env V) (H : Finset V)
    (t : Time) : Finset V :=
  H.filter (fun v => E.awake v t = true)

/-- Honest validators awake at some time in the closed window `[a,b]`. -/
noncomputable def awakeInClosed (E : AvailableChain.Generic.Env V) (H : Finset V)
    (a b : Time) : Finset V := by
  classical
  exact H.filter (fun v => ∃ u, a ≤ u ∧ u ≤ b ∧ E.awake v u = true)

/-- Faulty membership is the complement of the run's fixed honest set. -/
def faulty (rho : AvailableChain.Generic.Run V P) : Finset V :=
  Finset.univ \ rho.honest

/-- More honest validators are awake than there are faulty validators. -/
def AwakeMajority (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) (t : Time) : Prop :=
  (faulty rho).card < (awakeAt E rho.honest t).card

/-- `|H_t| > θ · |H_[t−η,t] ∪ A|`. -/
def EtaSleepy (E : AvailableChain.Generic.Env V)
    (C : Constants) (rho : AvailableChain.Generic.Run V P)
    (t : Time) : Prop :=
  C.θ * ((awakeInClosed E rho.honest (t - C.η) t ∪ faulty rho).card : ℚ) <
  ((awakeAt E rho.honest t).card : ℚ)

/-- Honest validators remain awake over the stated interval. -/
def FullParticipation (E : AvailableChain.Generic.Env V)
    (rho : AvailableChain.Generic.Run V P) (start : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, start ≤ t → t ≤ rho.horizon → E.awake v t = true

/-- Fewer than a quarter of the validators are faulty. -/
def BelowQuarter (rho : AvailableChain.Generic.Run V P) : Prop :=
  4 * (faulty rho).card < Fintype.card V

/-- Every bounded window after `start` contains an opening slot whose proposer
is honest and awake. -/
def HonestProposerRecurrence (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P)
    (start gap : Time) : Prop :=
  ∀ t, start ≤ t → t + gap ≤ rho.horizon →
    ∃ s, t < P.proposalTime s ∧ P.proposalTime s ≤ t + gap ∧
      I.opening s ∧ HonestAwakeProposer E rho s

end AvailableChain.Statements.Generic
end
