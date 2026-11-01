module
public import AvailableChainPCSAClaims.Claims.Finality
public import AvailableChainPCSAProofs.Proofs.Foundations.FinalitySafety
public import AvailableChainKitFG.AccountableCore

public section

/-! Closed exports of the eight frozen PC-SA finality safety claims. -/

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG

/-- Pure certificate accountability. -/
theorem pcsa_safety_pureAccountableClaim (p : Params) : PCSAPureAccountableClaim p := by
  rw [PCSAPureAccountableClaim_def]
  intro K W T₁ T₂ h₁ h₂ hr hK hW
  exact (KitFG.slashableWeight_or_finalized_compatible_of_certificate
    p.E (FGSA.heightView p) (pcsa_finalityView p) (pcsaSafetyCertificateLaws p) K W hr).imp id
    (fun h => hK.1 ▸ hW.1 ▸ h)

/-- Pure certificate agreement under the slashable bound. -/
theorem pcsa_safety_pureAgreementClaim (p : Params) : PCSAPureAgreementClaim p := by
  rw [PCSAPureAgreementClaim_def]
  intro K W T₁ T₂ h₁ h₂ hr hK hW hb
  exact (pcsa_safety_pureAccountableClaim p K W T₁ T₂ h₁ h₂ hr hK hW).resolve_left hb

/-- Whole-run accountability in either FG mode. -/
theorem pcsa_safety_wholeRunAccountableClaim (p : Params) : PCSAWholeRunAccountableClaim p := by
  rw [PCSAWholeRunAccountableClaim_def]
  intro V _ In c m E rho hr _
  exact pcsa_safety_wholeRunAccountable_body m p c E rho hr

/-- Whole-run agreement in either FG mode. -/
theorem pcsa_safety_wholeRunAgreementClaim (p : Params) : PCSAWholeRunAgreementClaim p := by
  rw [PCSAWholeRunAgreementClaim_def]
  intro V _ In c m E rho hr _ hb
  exact pcsa_safety_wholeRunAgreement_body m p c E rho hr hb

/-- Honest event prefixes agree in either FG mode. -/
theorem pcsa_safety_eventPrefixAgreementClaim (p : Params) : PCSAEventPrefixAgreementClaim p := by
  rw [PCSAEventPrefixAgreementClaim_def]
  intro V _ In c m E rho hr _ hb
  exact pcsa_safety_eventPrefixAgreement_body m p c E rho hr hb

/-- Finalized output is monotone on sorted runs without restart. -/
theorem pcsa_safety_finalizedMonotoneClaim (p : Params) : PCSAFinalizedMonotoneClaim p := by
  rw [PCSAFinalizedMonotoneClaim_def]
  intro V _ In c m E rho hs hnr
  exact pcsa_safety_finalizedMonotone_body m p c E rho hs hnr

/-- Fault counting supplies the all-run slashable bound under the frozen premises. -/
theorem pcsa_safety_faultCountSlashableBoundClaim (p : Params) :
    PCSAFaultCountSlashableBoundClaim p := by
  rw [PCSAFaultCountSlashableBoundClaim_def]
  intro V _ _ In c m E rho hl hc he hf
  exact pcsa_safety_faultCountSlashableBound_body m p c E rho hl hc he hf

/-- Honest holders are never slashed in either FG mode. -/
theorem pcsa_safety_honestNeverSlashedClaim (p : Params) : PCSAHonestNeverSlashedClaim p := by
  rw [PCSAHonestNeverSlashedClaim_def]
  intro In c m E rho hu hl
  exact pcsa_safety_honestNeverSlashed_body m p c E rho hu hl

end AvailableChain.PCSA.Run
end
