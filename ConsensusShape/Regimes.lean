module
public import ConsensusShape.Properties
@[expose] public section

/-! # Regimes
The premises of the claims. A regime mentions only the environment, the run
data, the constants and generic execution facts (`ExecutionValid`, delivery):
never a protocol-supplied word. Participation counts ready nodes (awake through
the catch-up window). -/
namespace Consensus.Shape
open Model

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family} {E : Env V}

namespace Run

variable (rho : Model.Run (compiled F) E) (A : Assumptions) (C : Constants)

/-- Synchronous from time 0, with the published ready-to-ready-plus-faulty
threshold at every time. -/
structure Sleepy : Prop where
  valid : rho.ExecutionValid
  sync : rho.PartialSynchrony
  gst_zero : E.gst = 0
  participation : ∀ t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.ReadyAbove A.sleepyReadyAbove ((A.catchUp : Time) * E.Δ) t

/-- Sleepy, and η-sleepy at every time. -/
structure StableSleepy : Prop extends Sleepy rho A where
  etaSleepy : ∀ t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.EtaSleepy A.stableEtaAbove ((A.eta : Time) * E.Δ) ((A.catchUp : Time) * E.Δ) t

/-- Sleepy, every honest validator awake, and the published fast fault cap. -/
structure Fast : Prop extends Sleepy rho A where
  full : rho.point.FullParticipation 0
  belowQuarter : rho.point.FaultsBelow A.fastFaultsBelow

/-- Sleepy, with a ready proposer in every window of `k` slots. -/
structure LiveSleepy (k : Nat) : Prop extends Sleepy rho A where
  recurrence : Recurrence rho ((A.catchUp : Time) * E.Δ) 0 k

/-- A healthy prefix up to `b₀`, then arbitrary delivery on `[b₀, b₁)`, with
lag `lag` (in units of `Δ`) between the protected read `T` and `b₀`. -/
structure OutageWith (lag : Nat) (T b₀ b₁ : Time) : Prop where
  valid : rho.ExecutionValid
  healthy : rho.HealthyPrefixDelivery b₀
  interval : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  armed : T + (lag : Time) * E.Δ ≤ b₀
  withinBudget : b₁ - b₀ ≤ (A.outageBudget : Time) * E.Δ
  readyBefore : ∀ t, 0 ≤ t → t < b₀ → rho.point.ReadyAbove A.sleepyReadyAbove ((A.catchUp : Time) * E.Δ) t
  etaSleepyBefore : ∀ t, 0 ≤ t → t < b₀ →
    rho.point.EtaSleepy A.stableEtaAbove ((A.eta : Time) * E.Δ) ((A.catchUp : Time) * E.Δ) t

/-- The outage regime. -/
abbrev Outage (T b₀ b₁ : Time) : Prop := OutageWith rho A A.armingLag T b₀ b₁

/-- The fast outage regime: the fast lag and the published inclusive
ready-of-all threshold before the outage. -/
structure FastOutage (T b₀ b₁ : Time) : Prop extends
    OutageWith rho A A.fastArmingLag T b₀ b₁ where
  highParticipation : ∀ t, 0 ≤ t → t < b₀ →
    rho.point.ReadyOfAllAtLeast A.fastOutageReadyAtLeast ((A.catchUp : Time) * E.Δ) t

/-- Arbitrary delivery before GST; after GST, synchrony, ready participation
above `θrec`, no honest wake, recurrence with gap `k`, and a horizon past the
recovery bound. -/
structure Recovery (k : Nat) : Prop where
  valid : rho.ExecutionValid
  sync : rho.PartialSynchrony
  participation : ∀ t, E.gst ≤ t → t ≤ rho.horizon →
    A.recovery.readyAbove * ((rho.point.readyAt ((A.catchUp : Time) * E.Δ) t).card + rho.point.faulty.card : ℚ) <
      ((rho.point.readyAt ((A.catchUp : Time) * E.Δ) t).card : ℚ)
  full : A.recovery.requireFull = true → rho.point.FullParticipation E.gst
  /-- No honest validator wakes at or after GST (plan Q13: the default until decided;
  the alternative is recovery for ready readers with wakes allowed). -/
  noWakeAfterGST : A.recovery.noWakeAfterGST = true → ∀ v ∈ rho.honest, ∀ t, E.gst ≤ t → t ≤ rho.horizon → ¬ Wakes E v t
  recurrence : Recurrence rho ((A.catchUp : Time) * E.Δ) E.gst k
  horizon : E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ ≤ rho.horizon

/-- Finality adds parameterized ready-of-all participation to recovery. -/
structure Finality (k : Nat) : Prop extends Recovery rho A C k where
  finParticipation : ∀ t, E.gst ≤ t → t ≤ rho.horizon →
    rho.point.ReadyOfAll A.finalityReadyOfAll ((A.catchUp : Time) * E.Δ) t

/-- What holds after recovery, from `t₀`: safety for ready readers (a node
asleep since before GST may keep a pre-GST fork) and inclusion. -/
structure RecoveredAt (t₀ : Time) : Prop where
  confirmedSafe : (chainTrace rho).ReadySafe ((A.catchUp : Time) * E.Δ) .confirmed t₀
  stableSafe : (chainTrace rho).ReadySafe ((A.catchUp : Time) * E.Δ) .stable t₀
  confirmedIncluded : IncludedFrom rho A (protoOf F E).confirmed t₀ C.D_c
  stableIncluded : IncludedFrom rho A (protoOf F E).stable t₀ C.D_s

end Run

end Consensus.Shape
end
