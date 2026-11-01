module
public import AvailableChainFramework.ClaimDomain
public import AvailableChainFramework.Hooks
public import AvailableChainStatements.Generic.Interface

@[expose] public section

namespace AvailableChain.Framework

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A protocol instance (design §3): the protocol, bound once. Claim constants
are not here; they belong to certificates. The v1 `Interface` is the one field
facet. Another facet is a structure that extends `Instance`, with its own claim
domain. -/
structure Instance where
  n : Nat
  P : ProtocolSpec n
  /-- Every certified environment has this Δ. -/
  Δ : Time
  /-- Without it, no environment has the instance's Δ, and every claim holds
  vacuously. -/
  Δ_pos : 0 < Δ
  iface : Interface P
  hooks : HooksSound P

/-- A v1 run context: an environment and a run of the instance's protocol. -/
structure V1Ctx (I : Instance) (W : Validators) where
  E : Env W.V
  rho : Run W.V I.P

/-- The v1 claim domain: today's instances with an environment and a v1 run. -/
@[reducible] def ClaimDomain.v1 : ClaimDomain where
  id := `v1
  Inst := Instance
  Ctx := V1Ctx
  admissible := fun I _ x => x.E.Δ = I.Δ
  horizon := fun _ _ x => x.rho.horizon

end AvailableChain.Framework

end
