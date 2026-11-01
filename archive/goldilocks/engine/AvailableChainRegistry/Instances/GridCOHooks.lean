module
public import AvailableChainFramework
public import AvailableChainGridCO.Proofs.Hooks

@[expose] public section

namespace AvailableChain.Registry.GridCO

open AvailableChain.Framework AvailableChain.GridCO

/-- Grid CO meets the E4 hook obligations with its permanent HEAD refusals
as `excludes`. The facts are in `AvailableChainGridCO/Proofs/Hooks.lean`.
SA is `@gridCO slowLeasePolicy p.engine`, so `@gridHooks slowLeasePolicy
p.engine` covers it. -/
theorem gridHooks [LeasePolicy] (p : Params) : HooksSound (gridCO p) :=
  ⟨excludes_inert p, excludes_stable p, processed_stable p, deps_stable p,
    handles_carries p⟩

end AvailableChain.Registry.GridCO

end
