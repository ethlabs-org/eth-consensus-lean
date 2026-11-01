module
public import AvailableChainPCSAProofs.Proofs.Finality.Export

public section

/-! The finality field of PCSAClaims: all eight safety claims are closed. -/

namespace AvailableChain.PCSA.Run

/-- The complete PC-SA finality safety package, for both FG modes. -/
theorem pcsaSafetyFinalityClaims (p : Params) : PCSAFinalitySafetyClaims p where
  accountable := pcsa_safety_pureAccountableClaim p
  agreement := pcsa_safety_pureAgreementClaim p
  runAccountable := pcsa_safety_wholeRunAccountableClaim p
  runAgreement := pcsa_safety_wholeRunAgreementClaim p
  eventPrefixAgreement := pcsa_safety_eventPrefixAgreementClaim p
  finalizedMonotone := pcsa_safety_finalizedMonotoneClaim p
  faultCountSlashableBound := pcsa_safety_faultCountSlashableBoundClaim p
  honestNeverSlashed := pcsa_safety_honestNeverSlashedClaim p

end AvailableChain.PCSA.Run
end
