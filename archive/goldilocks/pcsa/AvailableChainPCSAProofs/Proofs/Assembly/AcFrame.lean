module
public import AvailableChainPCSAProofs.Proofs.AcFrame.Export

public section

/-! Assembly entry for the AC-only frame (pcsa34-r4.3 §5.0). -/

namespace AvailableChain.PCSA.Run

/-- The frame proof is available independently of the unfinished claim record. -/
theorem pcsa_acFrameClaim (p : Params) : AcOnlyFrameClaim p := pcsa_acOnlyFrame p

end AvailableChain.PCSA.Run
end
