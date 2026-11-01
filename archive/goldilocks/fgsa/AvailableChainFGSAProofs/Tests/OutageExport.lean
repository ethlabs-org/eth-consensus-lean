module
public import AvailableChainFGSAProofs.Proofs.Assembly.Outage
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean

public section

namespace AvailableChain.FGSA.Run.Tests.OutageExport

variable (p : Params)

/-- The actual finite Clean and foundation suppliers close the unchanged outage claim. -/
theorem compat_of_sleep_cut : OutageCompatClaim p :=
  fgsa_outageCompatClaim_of_clean p (fgsa_cleanCutClaim p)

/-- The fast projection uses the same public confirmed-reader and duty scopes. -/
example : FastP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact (compat_of_sleep_cut p c E rho true pt ΔF h).1

/-- The slow projection keeps its covered-receiver lease guarantee. -/
example : SlowP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact compat_of_sleep_cut p c E rho false pt ΔF h

/-- The amended companion uses the exact Root exporter call and named suppliers. -/
theorem continuation_of_sleep_cut : OutageContinuationClaim p :=
  outageContinuation_claim_of p
    (fgsa_fgFoundationClaim p) (fgsa_srcFrameAboveClaim p)
    (fgsa_sourceDisciplineClaim p) (assembly_outage_clean_cut_supplier p)

#print axioms compat_of_sleep_cut
#print axioms continuation_of_sleep_cut
#print axioms assembly_outage_clean_cut_supplier
#print axioms fgsa_fastP1Claim_of_clean
#print axioms fgsa_slowP1Claim_of_clean

end AvailableChain.FGSA.Run.Tests.OutageExport
end
