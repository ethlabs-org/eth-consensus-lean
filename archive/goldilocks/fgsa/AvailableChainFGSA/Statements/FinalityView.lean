module
public import AvailableChainFGSA.Model.WindowViews -- shake: keep (re-export)
public import AvailableChainFGSA.Statements.WindowCertificate
public import AvailableChainKitFG.CertificateCoreDef -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGSA

/-- The active finality view reads the window certificate. -/
def finalityView (p : Params) : KitFG.FGFinalityView (Fin p.n) :=
  Window.certificateFinality p p.K_W

theorem finalityView_def (p : Params) :
    finalityView p = Window.certificateFinality p p.K_W := rfl

end AvailableChain.FGSA
end
