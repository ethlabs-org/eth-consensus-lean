module
public import AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge
public import AvailableChainFGSAProofs.Proofs.Foundations.ClientOrigin -- shake: keep (axiom audit)

public section

namespace AvailableChain.FGSA.Run

/-- DC `ReviewTheorem.lean:298`, honestNeverSlashed; `Generic/Claims.lean:63`.
Port of the d35bac1 proof to W. Unforgeability traces stored rows to emissions;
Linked attributes each fixed FG seat to its holder (F-H). Client safety
excludes a slashable pair emitted by an honest holder. -/
theorem fgsa_honestNeverSlashed (p : Params) {In : Type} (c : AppCodec In)
    (E : Generic.Env (Fin p.n)) (rho : V2.D.Run (Fin p.n) (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    Gen.V2.Duty.HonestNeverSlashed (fgsaSlashing p c E) rho :=
  fgsa_bridge_honestNeverSlashed p c E rho hU hL

end AvailableChain.FGSA.Run
end
