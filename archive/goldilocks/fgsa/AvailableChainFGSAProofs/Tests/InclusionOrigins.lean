module
public import AvailableChainFGSAProofs.Proofs.Outage.Suppliers
public import AvailableChainFGSAProofs.Proofs.Clean.Safety
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

public section

namespace AvailableChain.FGSA.Run.Tests.InclusionOrigins

open AvailableChain.SimplexFG Gen.Pure

/-- The real Clean producers discharge the later-reader assembly boundary.
This is a theorem-instantiation test; the reader may have restarted. -/
theorem later_origin_consumer {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (h : CleanCutSet p c E rho rho.horizon ΔF)
    (hq : FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {s : Slot} {t : Time} {x : V} (hst : SA.gateTime p.toParams s ≤ t)
    (hhor : t ≤ rho.horizon) (hx : confirmedReader p c E rho x t) :
    ∃ q i B, s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
      enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
      Block.Preceq B (S_at p c E rho (timeIdx rho t) x) := by
  have hGate : ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
      enabledGateAt p c E rho i x q →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧
        Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x) := by
    intro q i x hx hqhor hG
    have hs := h.base.valid.toScheduleWellFormed
    have hi := (V2.D.Engine.index_lt_read_length_iff hs rho.horizon hG.1).mpr hqhor
    obtain ⟨C, hC, _, hCS⟩ := clean_gateOutput_body p c E rho rho.horizon h hq hf hsrc
      (timeIdx rho rho.horizon) le_rfl (clean_invariant p c E rho h hq hf hsrc _ le_rfl)
      i x q hi hx hG
    refine ⟨C, hC, block_preceq_trans hCS ?_⟩
    exact sExtends p c E rho h hq hf hsrc x _ _
      (Nat.succ_le_of_lt ((V2.D.Engine.index_lt_read_length_iff hs _ hG.1).mpr le_rfl))
      (V2.D.Engine.read_length_mono _ _ hqhor)
  have hMono : ScopedMono (confirmedReader p c E rho)
      (fun t x => S_at p c E rho (timeIdx rho t) x)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon) := by
    intro t u x ht hu htu hx _
    have hg : (fgsaInterface p c).stable ∈
        [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] := by simp
    have hM := (clean_outputsAt p c E rho h hq hf hsrc _ hg).2 t u x ht hu htu hx.1
    simpa only [fgsa_outputAt_eq_S_at E rho h.base.valid.toScheduleWellFormed _ hg] using hM
  exact outage_supplier_later_origins E rho h.base hGate hMono s t x hst hhor hx

#print axioms AvailableChain.FGSA.Run.Tests.InclusionOrigins.later_origin_consumer

end AvailableChain.FGSA.Run.Tests.InclusionOrigins
end
