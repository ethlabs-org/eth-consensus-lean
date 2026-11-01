module
public import AvailableChainRegistry.Instances.GridCOHooks
public import AvailableChainSA.Proofs.Contract

@[expose] public section

namespace AvailableChain.Registry.SA

open AvailableChain.Framework AvailableChain.Framework.Catalog AvailableChain.SA

/-- SA is `@gridCO slowLeasePolicy p.engine`, so its hooks are the Grid CO
hooks at the slow lease policy. An instance with hooks. It is not an eligible
candidate: eligibility and certificates are plan 1c. -/
def saInst (p : Params) : Instance :=
  ⟨p.n, sa p, p.Δ, p.deltaPos, saInterface p,
    @GridCO.gridHooks GridCO.slowLeasePolicy p.engine⟩

theorem sa_holds_of_pos (p : Params) (G : Time) (hG : 0 < G) :
    ac43.holdsAt (saInst p) (saConstants p G) :=
  (ac43_iff _ _).1 fun _ E hΔ => (saContract_from_engine p E G hG hΔ).2

/-- The registry row: every parameter record, at the proposer gap `G = 1`. -/
theorem sa_holds (p : Params) : ac43.holdsAt (saInst p) (saConstants p 1) :=
  sa_holds_of_pos p 1 one_pos

theorem sa_holds_core_of_pos (p : Params) (G : Time) (hG : 0 < G) :
    core.holdsAt (saInst p) (saConstants p G).D_c :=
  core_holdsAt_of_ac43 (sa_holds_of_pos p G hG)

/-- The core row at the proposer gap `G = 1`. -/
theorem sa_holds_core (p : Params) : core.holdsAt (saInst p) (saConstants p 1).D_c :=
  sa_holds_core_of_pos p 1 one_pos

end AvailableChain.Registry.SA

end
