module
public import AvailableChainGridCO.Proofs.RowOrigins

@[expose] public section

namespace AvailableChain.GridCO

set_option linter.unusedSectionVars false
variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A stronger row whose target is already covered by the current honest
HEAD batch cannot conflict with that label's genuine result. This applies
to a row first installed by the pending preceding gate. -/
theorem supported_stronger_rows_compatible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho (r + 1))
    (source : V) (hs : source ∈ rho.honest) (B C : Block)
    (hc : confirmation p (gateInput p rho (r + 1) source) (r + 1) = some C)
    (hp : Block.Preceq B C)
    (hstrong : ∀ reader ∈ rho.honest, ∀ K g deadline,
      (K, g, deadline) ∈ (nextHeadState p rho (r + 1) reader).obligations →
      prefixSupport p (gateInput p rho (r + 1) source) (r + 1) B < g →
      ∀ voter ∈ rho.honest, Block.Preceq K (nextHead p (nextHeadState p rho r voter) r)) :
    ∀ reader ∈ rho.honest, ∀ K g deadline,
      (K, g, deadline) ∈ (nextHeadState p rho (r + 1) reader).obligations →
      prefixSupport p (gateInput p rho (r + 1) source) (r + 1) B < g → Block.Compatible K B := by
  intro reader hr K g deadline hm hg
  obtain ⟨D, hD, hKD, _⟩ := preserve_from_engine p E rho hΔ r hsync hsync.2.1 K
    (hstrong reader hr K g deadline hm hg) source hs
  have he : D = C := Option.some.inj (hD.symm.trans hc)
  subst D
  exact ancestors_compatible K B C hKD hp

end AvailableChain.GridCO
end
