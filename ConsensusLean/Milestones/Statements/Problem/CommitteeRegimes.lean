module
public import ConsensusLean.Spec.Problem.Regimes
public import ConsensusLean.Spec.Problem.Basic

/-! # Committee-qualified AC participation regimes

These growing-fault predicates are additional untrusted vocabulary. They change no existing
regime or FG population clause. The full-set bridge definitions below are intended theorem
types, not proved facts. Publicity, PKI binding and instance sample coverage are separate. -/

@[expose] public section

namespace Consensus

/-- Environment-only data for one committee outage count, with closed time windows. -/
structure OutageSample where
  committeeSlot : Nat
  anchor : Time
  windowStart : Time
  windowEnd : Time
  chargeEnd : Time
  deriving DecidableEq

/-- The sample's anchor, observation window and fault-charge time are ordered. -/
def OutageSample.WellFormed (d : OutageSample) : Prop :=
  0 ≤ d.anchor ∧ d.anchor ≤ d.windowStart ∧ d.windowStart ≤ d.windowEnd ∧
    d.windowEnd ≤ d.chargeEnd

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V]

/-- At every time, including slot zero, ready committee members retained through the clamped
look-ahead exceed fraction `θ` of ready plus faulty committee members. Readiness uses the
existing `c + 1` tick. Duration admissibility is not part of this predicate. -/
def CommitteeSleepyOn (p : EnvPoint V) (K : Nat → Finset V) (slot : Time → Nat)
    (θ : ℚ) (c W : Time) : Prop :=
  ∀ t, 0 ≤ t → t ≤ p.horizon →
    let q := p.retain (min (t + W) p.horizon)
    θ * (((q.readyAt c t ∩ K (slot t)).card +
      (q.faultyAt t ∩ K (slot t)).card : Nat) : ℚ) <
      ((q.readyAt c t ∩ K (slot t)).card : ℚ)

/-- Committee members honest at the clamped charge time and continuously awake from the
anchor through the end of the observation window. -/
noncomputable def OutageGood (p : EnvPoint V) (K : Nat → Finset V)
    (d : OutageSample) : Finset V := by
  classical
  exact (K d.committeeSlot).filter (fun v =>
    v ∉ p.faultyAt (min d.chargeEnd p.horizon) ∧
      p.AwakeOnClosed v d.anchor d.windowEnd)

/-- Faulty committee members together with honest window participants not in the good set.
This records identities rather than adding potentially overlapping population counts. -/
noncomputable def OutageBad (p : EnvPoint V) (K : Nat → Finset V)
    (d : OutageSample) : Finset V := by
  classical
  exact (K d.committeeSlot ∩ p.faultyAt (min d.chargeEnd p.horizon)) ∪
    ((K d.committeeSlot).filter (fun v =>
      v ∉ p.faultyAt (min d.chargeEnd p.horizon) ∧
        (∃ u, d.windowStart ≤ u ∧ u ≤ d.windowEnd ∧ p.env.awake v u = true) ∧
        v ∉ OutageGood p K d))

/-- A strict good-over-bad committee majority at one sample. -/
def CommitteeOutageAt (p : EnvPoint V) (K : Nat → Finset V) (d : OutageSample) : Prop :=
  (OutageBad p K d).card < (OutageGood p K d).card

/-- Every sample is well formed; samples whose observation ends within the horizon satisfy
the committee majority. An empty family supplies no instance coverage. -/
def CommitteeOutageOn (p : EnvPoint V) (K : Nat → Finset V)
    (samples : Finset OutageSample) : Prop :=
  (∀ d ∈ samples, d.WellFormed) ∧
    ∀ d ∈ samples, d.windowEnd ≤ p.horizon → CommitteeOutageAt p K d

/-- UNPROVED intended theorem type: full-set sleepy participation is exactly the existing
growing `SleepyOn`, for arbitrary threshold, catch-up, look-ahead and slot reader. -/
def SleepyFullSetIff : Prop :=
  ∀ (p : EnvPoint V) (slot : Time → Nat) (θ : ℚ) (c W : Time),
    CommitteeSleepyOn p (fun _ => Finset.univ) slot θ c W ↔
      p.SleepyOn θ c W 0 p.horizon

/-- UNPROVED intended theorem type: the old retained outage premises imply the full-set
sample predicate under explicit descriptor bounds. Deriving these bounds and sample coverage
from old instance premises remains separate; this is no unchanged-premise corollary. -/
def OldOutageImpliesFullSet : Prop :=
  ∀ (p : EnvPoint V) (samples : Finset OutageSample) (a z C : Time),
    0 ≤ a → a ≤ z → z ≤ C → C ≤ p.horizon →
    (∀ d ∈ samples, d.WellFormed) →
    (∀ d ∈ samples, d.windowEnd ≤ p.horizon →
      d.anchor = a ∧ d.windowEnd ≤ z ∧ min d.chargeEnd p.horizon ≤ C) →
    (p.retain C).NoSleepOn a z → (p.retain C).CohortOn a z →
      CommitteeOutageOn p (fun _ => Finset.univ) samples

end EnvPoint

end Consensus

end
