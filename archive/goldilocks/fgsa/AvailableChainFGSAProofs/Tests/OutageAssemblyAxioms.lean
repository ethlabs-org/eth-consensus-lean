module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel
public import AvailableChainFGSAProofs.Proofs.Outage.RestoredBatch

public section

namespace AvailableChain.FGSA.Run.Tests.OutageAssemblyAxioms

/-- The actual continuation regime supplies both prefix and restored receipts. -/
theorem continuation_receipt_consumer
    {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ :=
  outage_continuation_receipt_of_prefix h (arming_continuation_prefix_receipt h)

#print axioms continuation_receipt_consumer

end AvailableChain.FGSA.Run.Tests.OutageAssemblyAxioms
