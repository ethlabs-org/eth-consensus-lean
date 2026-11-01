module
public import AvailableChainFGSAProofs.Proofs.Foundations.HonestNeverSlashed -- shake: keep (example)

public section

namespace AvailableChain.FGSA.Run.Tests.HonestNeverSlashed

-- Apply the proof with exactly the two premises of HonestNeverSlashedClaim.
example (p : Params) {In : Type} (c : AppCodec In) (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    Gen.V2.Duty.HonestNeverSlashed (fgsaSlashing p c E) rho :=
  fgsa_honestNeverSlashed p c E rho hU hL

end AvailableChain.FGSA.Run.Tests.HonestNeverSlashed
end
