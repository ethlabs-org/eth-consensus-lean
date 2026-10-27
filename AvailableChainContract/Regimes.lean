module
public import AvailableChainContract.Evidence

@[expose] public section

/-! # Regimes

The premises of the claims. A regime mentions only the environment, the run
data, the constants and generic execution facts (`ExecutionValid`, delivery):
never a protocol-supplied word. Participation counts ready nodes (awake through
the catch-up window). -/

namespace AvailableChain.Contract

open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

variable (rho : Run F E) (C : Constants)

/-- Synchronous from time 0, with more ready honest validators than faulty
ones at every time. -/
structure Sleepy (t₀ : Time) : Prop where
  valid : rho.ExecutionValid
  sync : rho.PartialSynchrony
  gst_zero : E.t_GST = 0
  start_zero : t₀ = 0
  participation : ∀ t, t₀ ≤ t → t ≤ rho.horizon → rho.ReadyMajority C t

/-- Sleepy, and η-sleepy at every time. -/
structure StableSleepy (t₀ : Time) : Prop extends Sleepy rho C t₀ where
  etaSleepy : ∀ t, t₀ ≤ t → t ≤ rho.horizon → rho.EtaSleepy C t

/-- Sleepy, every honest validator awake, fewer than a quarter faulty. -/
structure Fast (t₀ : Time) : Prop extends Sleepy rho C t₀ where
  full : rho.FullParticipation t₀
  belowQuarter : rho.BelowQuarter

/-- Sleepy, with a ready proposer in every window of `k` slots. -/
structure LiveSleepy (t₀ : Time) (k : Nat) : Prop extends Sleepy rho C t₀ where
  recurrence : rho.Recurrence C t₀ k

/-- A healthy prefix up to `b₀`, then arbitrary delivery on `[b₀, b₁)`, with
lag `lag` (in units of `Δ`) between the protected read `T` and `b₀`. -/
structure OutageWith (lag : Nat) (T b₀ b₁ : Time) : Prop where
  valid : rho.ExecutionValid
  healthy : rho.HealthyPrefixDelivery b₀
  interval : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  armed : T + (lag : Time) * E.Δ ≤ b₀
  withinBudget : b₁ - b₀ ≤ (C.budget : Time) * E.Δ
  readyBefore : ∀ t, 0 ≤ t → t < b₀ → rho.ReadyMajority C t
  etaSleepyBefore : ∀ t, 0 ≤ t → t < b₀ → rho.EtaSleepy C t

/-- The outage regime. -/
abbrev Outage (T b₀ b₁ : Time) : Prop := rho.OutageWith C C.armingLag T b₀ b₁

/-- The fast outage regime: the fast lag, and at least half the seats ready
before the outage. -/
structure FastOutage (T b₀ b₁ : Time) : Prop extends
    rho.OutageWith C C.fastArmingLag T b₀ b₁ where
  highParticipation : ∀ t, 0 ≤ t → t < b₀ →
    (Fintype.card V + 1) / 2 ≤ (rho.readyAt C t).card

/-- Arbitrary delivery before GST; after GST, synchrony, ready participation
above `θrec`, no honest wake, recurrence with gap `k`, and a horizon past the
recovery bound. -/
structure Recovery (k : Nat) : Prop where
  valid : rho.ExecutionValid
  sync : rho.PartialSynchrony
  participation : ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
    C.θrec * ((rho.readyAt C t).card + rho.faulty.card : ℚ) < ((rho.readyAt C t).card : ℚ)
  full : C.recoveryFull = true → rho.FullParticipation E.t_GST
  /-- No honest validator wakes at or after GST (plan Q13: the default until decided;
  the alternative is recovery for ready readers with wakes allowed). -/
  noWakeAfterGST : ∀ v ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → ¬ Wakes E v t
  recurrence : rho.Recurrence C E.t_GST k
  horizon : E.t_GST + ((C.recovery.eval k : Nat) : Time) * E.Δ ≤ rho.horizon

/-- Finality: the recovery regime, fewer than a third faulty, and after GST
more than two thirds of the validators ready. -/
structure Finality (k : Nat) : Prop extends Recovery rho C k where
  belowOneThird : rho.BelowOneThird
  finParticipation : ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
    2 * Fintype.card V < 3 * (rho.readyAt C t).card

/-- What holds after recovery, from `t₀`: safety for ready readers (a node
asleep since before GST may keep a pre-GST fork) and inclusion. -/
structure RecoveredAt (t₀ : Time) : Prop where
  confirmedSafe : rho.ReadySafeFrom C (protoOf F E).confirmed t₀
  stableSafe : rho.ReadySafeFrom C (protoOf F E).stable t₀
  confirmedIncluded : rho.IncludedFrom C (protoOf F E).confirmed t₀ C.D_c
  stableIncluded : rho.IncludedFrom C (protoOf F E).stable t₀ C.D_s

end Run

end AvailableChain.Contract

end
