module
public import AvailableChainPCSAClaims.Claims.AcFrame
public import AvailableChainPCSAProofs.Proofs.AcFrame.Run

public section

/-! The AC-only frame claim export (pcsa34-r4.3 §5.0). -/

namespace AvailableChain.PCSA.Run

/-- AC-only runs have no honest FG rows and keep the initial frame. -/
theorem pcsa_acOnlyFrame (p : Params) : AcOnlyFrameClaim p := by
  intro V _ _ In c E rho h hf
  exact pcsa_ac_frame E rho h hf

end AvailableChain.PCSA.Run
end
