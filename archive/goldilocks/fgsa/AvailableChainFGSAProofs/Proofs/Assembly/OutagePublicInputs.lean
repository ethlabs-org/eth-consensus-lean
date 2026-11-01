module
public import AvailableChainFGSAProofs.Proofs.Outage.Export
public import AvailableChainFGSAProofs.Proofs.OutageContinuation.Export
public import AvailableChainFGSAProofs.Proofs.Foundations.Export
public import AvailableChainFGSAProofs.Proofs.Clean.Export -- shake: keep (source declarations)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure
variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
  (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
/-- The actual finite Clean producers supply every field of the outage input record. -/
theorem outage_clean_cut_supplier {b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF)
    (hq : FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho) :
    OutageCleanCutInputs (p := p) (c := c) E rho b₀ := by
  have hh := clean_invariant p c E rho h hq hf hsrc
  refine ⟨?_, hh _ le_rfl, ?_, ?_, ?_⟩
  · intro i hi
    exact cleanState_of_hist h hq hf hsrc
      (clean_actionStep p c E rho) hi (hh i hi)
  · intro j y s hj hG
    have hy := h.base.valid.toScheduleWellFormed.honest_only _ (List.mem_of_getElem? hG.1)
    obtain ⟨C, hC, _, hS⟩ := clean_gateOutput_body p c E rho b₀ h hq hf hsrc
      _ le_rfl (hh _ le_rfl) j y s hj hy hG
    exact ⟨C, hC, hS⟩
  · intro y z s C H hy hz hJ hs hC hH
    exact (cleanHistoryAt_body p c E rho h hq hf hsrc).2.2.1 y z s C H
      hy hz hs hC hJ hH
  · exact clean_epoch_saved_row h hq hf hsrc

/-- All named suppliers produce the unchanged public outage claim in ordinary sleep runs. -/
theorem outage_public_suppliers : OutageCompatClaim p :=
  outage_outageCompatClaim_of p (fgsa_fgFoundationClaim p) (fgsa_srcFrameAboveClaim p)
    (fgsa_sourceDisciplineClaim p) (outage_clean_cut_supplier p)

/-- Named foundation and finite Clean producers discharge the amended companion. -/
theorem outage_continuation_public_suppliers : OutageContinuationClaim p :=
  outageContinuation_claim_of p (fgsa_fgFoundationClaim p) (fgsa_srcFrameAboveClaim p)
    (fgsa_sourceDisciplineClaim p) (outage_clean_cut_supplier p)

#print axioms outage_continuation_public_suppliers
#print axioms outage_clean_cut_supplier
#print axioms outage_public_suppliers

end AvailableChain.FGSA.Run
