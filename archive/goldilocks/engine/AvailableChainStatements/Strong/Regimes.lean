module
public import AvailableChainStatements.Strong.Interface
public import AvailableChainStatements.Generic.Regimes

@[expose] public section
namespace AvailableChain.Statements.Generic

open AvailableChain

variable {V : Type} {n : Nat} [DecidableEq V] [Fintype V]

def FaultBound (P : AvailableChain.Generic.ProtocolSpec n)
    (f : Nat) (rho : AvailableChain.Generic.Run V P) : Prop :=
  (faulty rho).card ≤ f

/-- Sound arming from healthy genesis, followed by arbitrary delivery.
The instance must derive common installation from these fields. The
regime has no certificate, budget, or post-`b₀` premise. -/
structure StrongArmedRegime
    (P : AvailableChain.Generic.ProtocolSpec n)
    (E : AvailableChain.Generic.Env V) (I : StrongInterface P)
    (f : Nat) (rho : AvailableChain.Generic.Run V P)
    (T b₀ : Time) : Prop where
  execution : ExecutionValid P E rho
  rootInjective : RootInjective E I.toInterface rho
  healthy : HealthyPrefixDelivery P E rho b₀
  faultBound : FaultBound P f rho
  interval : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ rho.horizon
  armed : T + E.Δ ≤ b₀
  sleepyBefore : ∀ t, 0 ≤ t → t < b₀ → AwakeMajority E rho t

end AvailableChain.Statements.Generic
end
