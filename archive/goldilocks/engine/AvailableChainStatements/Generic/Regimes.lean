module
public import AvailableChainStatements.Generic.Conditions

@[expose] public section

namespace AvailableChain.Statements.Generic

open AvailableChain

variable {V : Type} {n : Nat} {P : AvailableChain.Generic.ProtocolSpec n}
  [DecidableEq V] [_root_.Fintype V]

/-- Synchronous from `t₀`, with honest awake weight above faulty weight. -/
structure SleepyRegime
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) (t₀ : Time) : Prop where
  execution : ExecutionValid P E rho
  rootInjective : RootInjective E I rho
  partialSynchrony : PartialSynchrony P E rho
  gst_zero : E.t_GST = 0
  start_zero : t₀ = 0
  participation : ∀ t, t₀ ≤ t → t ≤ rho.horizon → AwakeMajority E rho t

/-- Sleepy, with the η-sleepy inequality on the same interval. -/
structure StableSleepyRegime
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : AvailableChain.Generic.Run V P) (t₀ : Time) : Prop
    extends SleepyRegime P E I rho t₀ where
  etaSleepy : ∀ t, t₀ ≤ t → t ≤ rho.horizon → EtaSleepy E C rho t

/-- Sleepy with full honest participation and less than one-quarter faulty weight. -/
structure FastRegime
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P)
    (rho : AvailableChain.Generic.Run V P) (t₀ : Time) : Prop
    extends SleepyRegime P E I rho t₀ where
  fullParticipation : FullParticipation E rho t₀
  belowQuarter : BelowQuarter rho

/-- A healthy prefix followed by arbitrary delivery during `[b₀,b₁)`. -/
structure OutageRegime
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : AvailableChain.Generic.Run V P)
    (T b₀ b₁ : Time) : Prop where
  execution : ExecutionValid P E rho
  rootInjective : RootInjective E I rho
  healthy : HealthyPrefixDelivery P E rho b₀
  interval : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon
  armed : T + C.armingLag ≤ b₀
  withinBudget : b₁ - b₀ ≤ C.budget
  sleepyBefore : ∀ t, 0 ≤ t → t < b₀ → AwakeMajority E rho t
  etaSleepyBefore : ∀ t, 0 ≤ t → t < b₀ → EtaSleepy E C rho t

/-- The fast lag replaces the general lag. The high count holds on the
whole healthy prefix, including times before the protected read. -/
structure FastOutageRegime
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : AvailableChain.Generic.Run V P)
    (T b₀ b₁ : Time) : Prop
    extends OutageRegime P E I { C with armingLag := C.fastArmingLag } rho T b₀ b₁ where
  highParticipation : ∀ t, 0 ≤ t → t < b₀ →
    (n + 1) / 2 ≤ (awakeAt E rho.honest t).card

/-- Delivery is arbitrary before GST. After GST, current participation
exceeds θrec and honest opening proposers recur. -/
structure RecoveryRegime
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : AvailableChain.Generic.Run V P) : Prop where
  execution : ExecutionValid P E rho
  rootInjective : RootInjective E I rho
  partialSynchrony : PartialSynchrony P E rho
  participation : ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
    C.θrec * ((awakeAt E rho.honest t).card + (faulty rho).card : ℚ) <
      ((awakeAt E rho.honest t).card : ℚ)
  full : C.recoveryFull = true → FullParticipation E rho E.t_GST
  recurrence : HonestProposerRecurrence E I rho E.t_GST C.proposerGap
  horizon : E.t_GST + C.recoveryBound ≤ rho.horizon

end AvailableChain.Statements.Generic
end
