module
public import AvailableChainStatements.Strong.Constants
public import AvailableChainStatements.Strong.Regimes
public import AvailableChainStatements.Generic.Claims

@[expose] public section
namespace AvailableChain.Statements.Generic

open AvailableChain

variable {V : Type} {n : Nat} [DecidableEq V] [Fintype V]

/-- Additive strong claims, with a fault cap on each run. This does not
replace or restrict any field of the base `AvailableChain` bundle. -/
structure StrongClaims
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : StrongInterface P)
    (C : Constants) (SC : StrongConstants) : Prop where
  constants : SC.Valid
  strongSafe : ∀ rho t₀,
    SleepyRegime P E I.toInterface rho t₀ →
    FaultBound P SC.faultCap rho → SafeFrom P rho I.strong t₀
  strongIncluded : ∀ rho t₀,
    SleepyRegime P E I.toInterface rho t₀ →
    FaultBound P SC.faultCap rho → FullParticipation E rho t₀ →
    IncludedFrom P E I.toInterface rho I.strong t₀ SC.strongDelay
  strongResilient : ∀ rho T b₀,
    StrongArmedRegime P E I SC.faultCap rho T b₀ →
    PersistsFrom P rho I.strong T b₀
  strongRecoveredSafe : ∀ rho,
    RecoveryRegime P E I.toInterface C rho → FaultBound P SC.faultCap rho →
    SafeFrom P rho I.strong (E.t_GST + C.recoveryBound)
  strongRecoveredIncluded : ∀ rho,
    RecoveryRegime P E I.toInterface C rho → FaultBound P SC.faultCap rho →
    IncludedFrom P E I.toInterface rho I.strong
      (E.t_GST + C.recoveryBound) SC.strongDelay

end AvailableChain.Statements.Generic
end
