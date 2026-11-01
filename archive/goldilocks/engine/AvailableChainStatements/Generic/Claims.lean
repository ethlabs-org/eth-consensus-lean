module
public import AvailableChainStatements.Generic.Properties
public import AvailableChainStatements.Generic.Regimes

@[expose] public section

namespace AvailableChain.Statements.Generic

open AvailableChain

variable {V : Type} {n : Nat} [DecidableEq V] [_root_.Fintype V]

/-- The sleepy conclusions that hold after recovery. -/
structure RecoveredAt (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P) (C : Constants)
    (rho : AvailableChain.Generic.Run V P) (t₀ : Time) : Prop where
  confirmedSafe : SafeFrom P rho I.confirmed t₀
  stableSafe : SafeFrom P rho I.stable t₀
  confirmedIncluded : IncludedFrom P E I rho I.confirmed t₀ C.D_c
  stableIncluded : IncludedFrom P E I rho I.stable t₀ C.D_s

set_option linter.dupNamespace false in
/-- The fixed available-chain contract for a protocol instance. -/
structure AvailableChain
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : Interface P) (C : Constants) : Prop where
  constants : C.Valid
  confirmedSafe : ∀ rho t₀, SleepyRegime P E I rho t₀ →
    SafeFrom P rho I.confirmed t₀
  stableSafe : ∀ rho t₀, SleepyRegime P E I rho t₀ →
    SafeFrom P rho I.stable t₀
  monotone : ∀ rho t₀, SleepyRegime P E I rho t₀ →
    MonotoneFrom P rho I.confirmed t₀ ∧ MonotoneFrom P rho I.stable t₀
  nested : ∀ rho : AvailableChain.Generic.Run V P, OutputOrder P I rho
  confirmedIncluded : ∀ rho t₀, SleepyRegime P E I rho t₀ →
    IncludedFrom P E I rho I.confirmed t₀ C.D_c
  stableIncluded : ∀ rho t₀, StableSleepyRegime P E I C rho t₀ →
    IncludedFrom P E I rho I.stable t₀ C.D_s
  stableIncludedFast : ∀ rho t₀, FastRegime P E I rho t₀ →
    IncludedFrom P E I rho I.stable t₀ C.D_f
  stableResilient : ∀ rho T b₀ b₁, OutageRegime P E I C rho T b₀ b₁ →
    PersistsThrough P rho I.stable T b₀ b₁
  stableResilientFast : ∀ rho T b₀ b₁, FastOutageRegime P E I C rho T b₀ b₁ →
    PersistsThrough P rho I.stable T b₀ b₁
  recovered : ∀ rho, RecoveryRegime P E I C rho →
    RecoveredAt P E I C rho (E.t_GST + C.recoveryBound)

end AvailableChain.Statements.Generic
end
