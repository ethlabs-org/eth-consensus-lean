module
public import AvailableChainRegistry.Instances.GridCOHooks
public import AvailableChainGridCO.Proofs.Contract

@[expose] public section

namespace AvailableChain.Registry.GridCO

open AvailableChain.Framework AvailableChain.Framework.Catalog AvailableChain.GridCO

/-- Grid CO at the default lease policy. An instance with hooks. It is not an
eligible candidate: eligibility and certificates are plan 1c. -/
def gridInst (p : Params) : Instance :=
  ⟨p.n, gridCO p, p.Δ, p.deltaPos, gridInterface p, gridHooks p⟩

theorem grid_holds_of_pos (p : Params) (G : Time) (hG : 0 < G) :
    ac43.holdsAt (gridInst p) (gridConstants p G) :=
  (ac43_iff _ _).1 fun _ E hΔ => (gridContract_from_engine p E G hG hΔ).2

/-- The registry row: every parameter record, at the proposer gap `G = 1`. -/
theorem grid_holds (p : Params) : ac43.holdsAt (gridInst p) (gridConstants p 1) :=
  grid_holds_of_pos p 1 one_pos

theorem grid_holds_core_of_pos (p : Params) (G : Time) (hG : 0 < G) :
    core.holdsAt (gridInst p) (gridConstants p G).D_c :=
  core_holdsAt_of_ac43 (grid_holds_of_pos p G hG)

/-- The core row at the proposer gap `G = 1`. -/
theorem grid_holds_core (p : Params) : core.holdsAt (gridInst p) (gridConstants p 1).D_c :=
  grid_holds_core_of_pos p 1 one_pos

end AvailableChain.Registry.GridCO

end
