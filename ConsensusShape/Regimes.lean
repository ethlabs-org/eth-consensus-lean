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

variable (rho : Model.Run (compiled F) E) (C : Constants)

/-- Synchronous from time 0, with more ready honest validators than faulty
ones at every time. -/
structure Sleepy : Prop where
  valid : rho.ExecutionValid
  sync : rho.PartialSynchrony
  gst_zero : E.gst = 0
  participation : ∀ t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.ReadyMajority ((C.catchUp : Time) * E.Δ) t

/-- Sleepy, and η-sleepy at every time. -/
structure StableSleepy : Prop extends Sleepy rho C where
  etaSleepy : ∀ t, 0 ≤ t → t ≤ rho.horizon →
    rho.point.EtaSleepy ((C.catchUp : Time) * E.Δ) C.θ ((C.η : Time) * E.Δ) t

/-- Sleepy, every honest validator awake, fewer than a quarter faulty. -/
structure Fast : Prop extends Sleepy rho C where
  full : rho.point.FullParticipation 0
  belowQuarter : rho.point.BelowQuarter

/-- Sleepy, with a ready proposer in every window of `k` slots. -/
structure LiveSleepy (k : Nat) : Prop extends Sleepy rho C where
  recurrence : Recurrence rho ((C.catchUp : Time) * E.Δ) 0 k

/-- A healthy prefix up to `b₀`, then arbitrary delivery on `[b₀, b₁)`, with
lag `lag` (in units of `Δ`) between the protected read `T` and `b₀`. -/
structure OutageWith (lag : Nat) (T b₀ b₁ : Time) : Prop where
  valid : rho.ExecutionValid
  healthy : rho.HealthyPrefixDelivery b₀
  interval : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  armed : T + (lag : Time) * E.Δ ≤ b₀
  withinBudget : b₁ - b₀ ≤ (C.budget : Time) * E.Δ
  readyBefore : ∀ t, 0 ≤ t → t < b₀ → rho.point.ReadyMajority ((C.catchUp : Time) * E.Δ) t
  etaSleepyBefore : ∀ t, 0 ≤ t → t < b₀ →
    rho.point.EtaSleepy ((C.catchUp : Time) * E.Δ) C.θ ((C.η : Time) * E.Δ) t

/-- The outage regime. -/
abbrev Outage (T b₀ b₁ : Time) : Prop := OutageWith rho C C.armingLag T b₀ b₁

/-- The fast outage regime: the fast lag, and at least half the seats ready
before the outage. -/
structure FastOutage (T b₀ b₁ : Time) : Prop extends
    OutageWith rho C C.fastArmingLag T b₀ b₁ where
  highParticipation : ∀ t, 0 ≤ t → t < b₀ →
    (Fintype.card V + 1) / 2 ≤ (rho.point.readyAt ((C.catchUp : Time) * E.Δ) t).card

/-- Arbitrary delivery before GST; after GST, synchrony, ready participation
above `θrec`, no honest wake, recurrence with gap `k`, and a horizon past the
recovery bound. -/
structure Recovery (k : Nat) : Prop where
  valid : rho.ExecutionValid
  sync : rho.PartialSynchrony
  participation : ∀ t, E.gst ≤ t → t ≤ rho.horizon →
    C.θrec * ((rho.point.readyAt ((C.catchUp : Time) * E.Δ) t).card + rho.point.faulty.card : ℚ) <
      ((rho.point.readyAt ((C.catchUp : Time) * E.Δ) t).card : ℚ)
  full : C.recoveryFull = true → rho.point.FullParticipation E.gst
  /-- No honest validator wakes at or after GST (plan Q13: the default until decided;
  the alternative is recovery for ready readers with wakes allowed). -/
  noWakeAfterGST : ∀ v ∈ rho.honest, ∀ t, E.gst ≤ t → t ≤ rho.horizon → ¬ Wakes E v t
  recurrence : Recurrence rho ((C.catchUp : Time) * E.Δ) E.gst k
  horizon : E.gst + ((C.recovery.eval k : Nat) : Time) * E.Δ ≤ rho.horizon
  belowOneThird : rho.point.BelowOneThird

/-- Finality: the recovery regime, fewer than a third faulty, and after GST
more than two thirds of the validators ready. -/
structure Finality (k : Nat) : Prop extends Recovery rho C k where
  finParticipation : ∀ t, E.gst ≤ t → t ≤ rho.horizon →
    2 * Fintype.card V < 3 * (rho.point.readyAt ((C.catchUp : Time) * E.Δ) t).card

/-- What holds after recovery, from `t₀`: safety for ready readers (a node
asleep since before GST may keep a pre-GST fork) and inclusion. -/
structure RecoveredAt (t₀ : Time) : Prop where
  confirmedSafe : (chainTrace rho).ReadySafe ((C.catchUp : Time) * E.Δ) .confirmed t₀
  stableSafe : (chainTrace rho).ReadySafe ((C.catchUp : Time) * E.Δ) .stable t₀
  confirmedIncluded : IncludedFrom rho C (protoOf F E).confirmed t₀ C.D_c
  stableIncluded : IncludedFrom rho C (protoOf F E).stable t₀ C.D_s

end Run

end Consensus.Shape
end
