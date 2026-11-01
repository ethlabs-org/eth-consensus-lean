module
public import AvailableChainFGSAProofs.Proofs.Outage.GrowthSuppliers
public import AvailableChainFGSAProofs.Proofs.Outage.Suppliers
public import AvailableChainFGSAProofs.Proofs.Clean.Safety
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Foundations.Certificates
public import AvailableChainFGSAProofs.Proofs.Foundations.Reconcile
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources

public section

namespace AvailableChain.FGSA.Run.Tests.OutageGrowthSuppliers

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The real supplier composition consumes the actual Clean sleep regime only. -/
theorem growth_suppliers_from_clean {ΔF : Time}
    (hset : CleanSet p c E rho ΔF) (pt : PtSP)
    (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon) :
    (∃ y, confirmedReader p c E rho y (SA.gateTime p.toParams pt.s) ∧
      Block.Preceq pt.P (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams pt.s)) y)) ∧
    (∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) pt.s →
      confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Compatible (V2.D.outputAt E rho g x u) pt.P) ∧
    (∀ u x g, SA.gateTime p.toParams pt.s ≤ u → u ≤ rho.horizon →
      confirmedReader p c E rho x u →
      g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
      Block.Preceq pt.P (V2.D.outputAt E rho g x u)) := by
  have hpos : 0 < rho.horizon := lt_of_lt_of_le (by
    rw [arming_gate_eq]; have := p.deltaPos; positivity) hhor
  have hq := hset.pre.toCleanCut.faultQ_of_pos hpos
  have hPrem : SourceDisciplinePrem p c E rho () := ⟨hset.pre.base, hq⟩
  have hf : FGFoundation p c E rho :=
    ⟨fgsa_rStore p c E rho, ⟨fgsa_rStoreDurable p c E rho, fgsa_rStoreEpoch p c E rho⟩,
      fgsa_rMonoAll p c E rho, ⟨fgsa_rFrameExactNext p c E rho, fgsa_rFrameNextEpoch p c E rho⟩,
      fgsa_rGeo p c E rho, sourceDiscipline_strat p c E rho hPrem (fgsa_rStore p c E rho),
      fgsa_rRec p c E rho⟩
  have hsrc := sourceDiscipline_srcFrameAbove p c E rho hPrem (fgsa_rStore p c E rho)
  have hcut := hset.sleepPre.sleepPre
  have hHist := cleanHistoryAt_body p c E rho hcut hq hf hsrc
  have hTrunc := cleanTruncAt_body p c E rho hcut hq hf hsrc
  have hBase := hset.pre.base
  have hs := hBase.valid.toScheduleWellFormed
  have hOrdered := inclusion_ordered_of_scoped E rho hBase.valid hHist.1
  have hNonempty := hHist.2.1
  have hTransfer := hHist.2.2.1
  have hRows := hHist.2.2.2.2.2.1
  have hLeases := fun i v hi hv row hr => (hHist.2.2.2.1 i v hi hv).2.2.2.1 row hr |>.1
  have hBounds : InclusionHistoryBounds E rho := ⟨by
    intro i v hi hv
    have hb := hHist.2.2.2.1 i v hi hv
    exact ⟨hb.1, hb.2.1, hb.2.2.1, fun row hr => (hb.2.2.2.1 row hr).1,
      fun s C hC => (hb.2.2.2.2.1 s C hC).1⟩⟩
  have hOutputs := fun g hg => (hTrunc.2.2.1 g hg).1
  have hReaderGate : ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
      enabledGateAt p c E rho i x q →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧
        Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x) := by
    intro q i x hx hqhor hG
    have hi := (V2.D.Engine.index_lt_read_length_iff hs rho.horizon hG.1).mpr hqhor
    obtain ⟨C, hC, _, hCS⟩ := clean_gateOutput_body p c E rho rho.horizon hcut hq hf hsrc
      (timeIdx rho rho.horizon) le_rfl
      (clean_invariant p c E rho hcut hq hf hsrc _ le_rfl) i x q hi hx hG
    refine ⟨C, hC, block_preceq_trans hCS ?_⟩
    exact sExtends p c E rho hcut hq hf hsrc x _ _
      (Nat.succ_le_of_lt ((V2.D.Engine.index_lt_read_length_iff hs _ hG.1).mpr le_rfl))
      (V2.D.Engine.read_length_mono _ _ hqhor)
  have hReaderMono : ScopedMono (confirmedReader p c E rho)
      (fun t x => S_at p c E rho (timeIdx rho t) x)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon) := by
    have hg : (fgsaInterface p c).stable ∈
        [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] := by simp
    intro t u x ht hu htu hx hy
    simpa only [fgsa_outputAt_eq_S_at E rho hs _ hg] using
      (hTrunc.2.2.1 _ hg).2 t u x ht hu htu hx hy
  exact clean_growth_suppliers E rho ΔF hset hBounds hf.store hf.frame.1 hsrc
    hOrdered hNonempty hTransfer hLeases hRows pt hprop hhor hOutputs
    (outage_supplier_later_origins E rho hBase hReaderGate hReaderMono pt.s) hf.strat

/-- The real P20 consumer takes no compatibility, inclusion, or receiver-service callback. -/
theorem growth_claim_from_producers (p : Params) :
    ∀ (G ΔF : Time) {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (t : Time),
      CleanSet p c E rho ΔF → AwakeProposerRecurrenceFrom p c E rho 0 G →
      4 * p.Δ ≤ G → 0 ≤ t → t + G + 6 * p.Δ ≤ rho.horizon →
      ∃ s B, t < V2.D.proposalTime (fgsaInterface p c) s ∧
        HonestProposal E rho (fgsaInterface p c) s B ∧
        ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
          (∀ x, confirmedReader p c E rho x t →
            Block.Prec (V2.D.outputAt E rho g x t) B) ∧
          (∀ x, confirmedReader p c E rho x (t + G + 6 * p.Δ) →
            Block.Preceq B (V2.D.outputAt E rho g x (t + G + 6 * p.Δ))) := by
  apply clean_growth_claim_body p
  · intro V _ _ In c E rho ΔF hset s B hprop hhor
    exact (growth_suppliers_from_clean hset ⟨s, B⟩ hprop hhor).2.1
  · intro V _ _ In c E rho ΔF hset s B hprop hhor
    exact (growth_suppliers_from_clean hset ⟨s, B⟩ hprop hhor).2.2

end AvailableChain.FGSA.Run.Tests.OutageGrowthSuppliers

#print axioms AvailableChain.FGSA.Run.clean_growth_suppliers
#print axioms AvailableChain.FGSA.Run.Tests.OutageGrowthSuppliers.growth_suppliers_from_clean
#print axioms AvailableChain.FGSA.Run.Tests.OutageGrowthSuppliers.growth_claim_from_producers
end
