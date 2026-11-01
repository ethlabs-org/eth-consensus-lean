module
public import AvailableChainFGSA.Statements.FinalityView
public import AvailableChainFGSA.Proofs.FrameViews
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainFGSA.Proofs.WindowStore

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The active height view equals the simplex height view through the bridge. -/
theorem heightView_eq_simplex (p : Params) :
    heightView p = simplexHeightView p.E p.cfg := funext (heightView_bridge p)

/-- Certificate laws for the active window views. -/
theorem fgCertificateLaws (p : Params) :
    FGCertificateLaws p.E (heightView p) (finalityView p) :=
  Window.windowCertificateLaws p p.K_W p.kWLarge

/-- Justification laws for the active height view. -/
theorem fgJustificationLaws (p : Params) : FGJustificationLaws (heightView p) :=
  FGJustificationLaws.of_bridge (heightView_bridge p)

/-- Store safety uses the generic invariant itself as the good-state predicate. -/
theorem fgStoreSafety (p : Params) :
    FGStoreSafety p.E (heightView p) (finalityView p)
      (id : Store (Fin p.n) → Store (Fin p.n))
      (fun _ B => (heightView p B, finalityView p B))
      Store.init (Window.on_block p p.K_W) (FGStoreInvariant (heightView p) (finalityView p))
        StoreStepRoots :=
  Window.windowStoreSafety p p.K_W p.kWLarge

end AvailableChain.FGSA
end
