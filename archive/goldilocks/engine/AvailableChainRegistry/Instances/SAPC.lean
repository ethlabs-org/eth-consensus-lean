module
public import AvailableChainFramework
public import AvailableChainSAPC.Proofs.Hooks
public import AvailableChainSAPC.Proofs.Contract
public import AvailableChainSAPC.Proofs.StrongContract

@[expose] public section

namespace AvailableChain.Registry.SAPC

open AvailableChain.Framework AvailableChain.Framework.Catalog AvailableChain.SAPC

/-- SA-PC meets the E4 hook obligations with `excludes = false`. The facts are
in `AvailableChainSAPC/Proofs/Hooks.lean`. -/
theorem sapcHooks (p : Params) : HooksSound (sapc p) :=
  ⟨SAPC.excludes_inert p, SAPC.excludes_stable p, SAPC.processed_stable p,
    SAPC.deps_stable p, SAPC.handles_carries p⟩

/-- SA-PC with its strong output. An instance with hooks. It is not an eligible
candidate: eligibility and certificates are plan 1c. -/
def sapcInst (p : Params) : StrongInstance :=
  { n := p.n, P := sapc p, Δ := p.Δ, Δ_pos := p.deltaPos,
    iface := (sapcInterface p).toInterface, hooks := sapcHooks p,
    strong := (sapcInterface p).strong }

theorem sapc_holds_ac43_of_pos (p : Params) (G : Time) (hG : 0 < G) :
    ac43.holdsAt (sapcInst p).toInstance (sapcConstants p G) :=
  (ac43_iff _ _).1 fun _ E hΔ => (sapcContract_from_engine p E G hG hΔ).2

/-- The registry row: every parameter record, at the proposer gap `G = 1`. -/
theorem sapc_holds_ac43 (p : Params) :
    ac43.holdsAt (sapcInst p).toInstance (sapcConstants p 1) :=
  sapc_holds_ac43_of_pos p 1 one_pos

/-- The strong row for every `0 < G`. -/
theorem sapc_holds_strong1_of_pos (p : Params) (G : Time) (hG : 0 < G) :
    strong1.holdsAt (sapcInst p) (sapcConstants p G, sapcStrongConstants p) :=
  -- `(sapcInst p).sface` is `sapcInterface p` by structure eta.
  (strong1_iff _ _ _).1 fun _ E hΔ => (sapcStrong_from_engine p E G hG hΔ).2

/-- The strong row at the proposer gap `G = 1`. -/
theorem sapc_holds_strong1 (p : Params) :
    strong1.holdsAt (sapcInst p) (sapcConstants p 1, sapcStrongConstants p) :=
  sapc_holds_strong1_of_pos p 1 one_pos

/-- Both SA-PC profiles at one `C := sapcConstants p G` (PHASE1A-REPORT, plan
1b input 2, at the `holds` level; the certificate pair is plan 1c). -/
theorem sapc_holds_shared (p : Params) (G : Time) (hG : 0 < G) :
    ac43.holdsAt (sapcInst p).toInstance (sapcConstants p G) ∧
      strong1.holdsAt (sapcInst p) (sapcConstants p G, sapcStrongConstants p) :=
  ⟨sapc_holds_ac43_of_pos p G hG, sapc_holds_strong1_of_pos p G hG⟩

theorem sapc_holds_core_of_pos (p : Params) (G : Time) (hG : 0 < G) :
    core.holdsAt (sapcInst p).toInstance (sapcConstants p G).D_c :=
  core_holdsAt_of_ac43 (sapc_holds_ac43_of_pos p G hG)

/-- The core row at the proposer gap `G = 1`. -/
theorem sapc_holds_core (p : Params) :
    core.holdsAt (sapcInst p).toInstance (sapcConstants p 1).D_c :=
  sapc_holds_core_of_pos p 1 one_pos

end AvailableChain.Registry.SAPC

end
