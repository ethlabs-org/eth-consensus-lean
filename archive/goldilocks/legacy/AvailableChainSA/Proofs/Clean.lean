module
public import AvailableChainSA.Proofs.Basic
public import AvailableChainGridCO.Proofs.CleanInclusion

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic

local instance saCleanLeasePolicy : GridCO.LeasePolicy := GridCO.slowLeasePolicy

/-- Shared genuine-history safety applies to both exposed SA outputs. -/
theorem clean_safety_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sa p) E (saInterface p) rho t₀) :
    SafeFrom (sa p) rho (saInterface p).stable t₀ ∧
      SafeFrom (sa p) rho (saInterface p).confirmed t₀ :=
  GridCO.clean_safety_from_engine p.engine E rho hΔ t₀ hs

/-- Neither exposed SA output retreats in a clean Sleepy run. -/
theorem monotone_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sa p) E (saInterface p) rho t₀) :
    MonotoneFrom (sa p) rho (saInterface p).confirmed t₀ ∧
      MonotoneFrom (sa p) rho (saInterface p).stable t₀ :=
  GridCO.monotone_from_engine p.engine E rho hΔ t₀ hs

/-- Honest awake proposals enter both records within 6Δ. Lease admission
is not a premise of this theorem. -/
theorem included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sa p) E (saInterface p) rho t₀) :
    IncludedFrom (sa p) E (saInterface p) rho (saInterface p).stable t₀ (6 * p.Δ) :=
  GridCO.included_from_engine p.engine E rho hΔ t₀ hs

end AvailableChain.SA
end
