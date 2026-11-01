module
public import AvailableChainFGSA.Model.WindowViews
public import AvailableChainPCSA.Statements.WindowCertificate
public import AvailableChainKitFG.CertificateCoreDef

@[expose] public section

namespace AvailableChain.PCSA

/-- [PC-SA M1; FG-SA Statements/FinalityView.lean] The active finality view
reads the window certificate. -/
def pcsa_finalityView (p : Params) : KitFG.FGFinalityView (Fin p.n) :=
  Window.pcsa_certificateFinality p p.K_W

theorem pcsa_finalityView_def (p : Params) :
    pcsa_finalityView p = Window.pcsa_certificateFinality p p.K_W := rfl

end AvailableChain.PCSA
end
