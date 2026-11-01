module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.OutageContinuation.Export -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Outage.Export -- shake: keep (Outage claim boundary)
public import AvailableChainFGSAProofs.Proofs.Clean.Export -- shake: keep (Clean supplier boundary)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export
-- shake: keep (foundation supplier boundary)

public section

namespace AvailableChain.FGSA.Run

variable (p : Params)

/-- The actual finite Clean producers supply every field of the outage input record. -/
theorem assembly_outage_clean_cut_supplier
    {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
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


private theorem clean_history_supplier (hcut : CleanCutClaim p)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀)
    (h : CleanCutPrem p c E rho pt ΔF) : CleanHistoryAt p c E rho pt.b₀ :=
  (hcut c E rho pt h).1

/-- Clean's enabled result extends to the inclusive public gate read. -/
private theorem clean_reader_gate_supplier
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (h : CleanPrem p c E rho () ΔF) :
    ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
      enabledGateAt p c E rho i x q →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧
        Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x) := by
  have hc := h.set.sleepPre.sleepPre
  have hq := h.set.pre.faultQ
  have hp : SourceDisciplinePrem p c E rho () := ⟨hc.base, hq⟩
  have hf := fgsa_fgFoundationClaim p c E rho () hp
  have hsrc := fgsa_srcFrameAboveClaim p c E rho () hp
  have hs := hc.base.valid.toScheduleWellFormed
  intro q i x hx hqhor hG
  have hi := (V2.D.Engine.index_lt_read_length_iff hs rho.horizon hG.1).mpr hqhor
  obtain ⟨C, hC, _, hCS⟩ := clean_gateOutput_body p c E rho rho.horizon hc hq
    ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩ hsrc
    (timeIdx rho rho.horizon) le_rfl
    (clean_invariant p c E rho hc hq
      ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩ hsrc _ le_rfl)
    i x q hi hx hG
  refine ⟨C, hC, block_preceq_trans hCS ?_⟩
  exact sExtends p c E rho hc hq
    ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩ hsrc x _ _
    (Nat.succ_le_of_lt ((V2.D.Engine.index_lt_read_length_iff hs _ hG.1).mpr le_rfl))
    (V2.D.Engine.read_length_mono _ _ hqhor)

/-- The cut claim supplies monotonicity at bounded confirmed public readers. -/
private theorem clean_reader_mono_supplier (hcut : CleanCutClaim p)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time}
    (h : CleanPrem p c E rho () ΔF) :
    ScopedMono (confirmedReader p c E rho)
      (fun t x => S_at p c E rho (timeIdx rho t) x)
      (fun t => 0 ≤ t ∧ t ≤ rho.horizon) := by
  have hg : (fgsaInterface p c).stable ∈
      [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] := by simp
  have hm := ((hcut c E rho ⟨rho.horizon⟩ ⟨h.set.sleepPre.sleepPre⟩).2.2.2.1 _ hg).2
  intro t u x ht hu htu hx hy
  simpa only [fgsa_outputAt_eq_S_at E rho h.set.pre.base.valid.toScheduleWellFormed _ hg]
    using hm t u x ht hu htu hx hy

/-- ROOT-DIGEST W2b. Blueprint 03 §4. The Clean claims supply the history projections.
Foundation Exports supply store, frame, and source discipline. -/
theorem fgsa_exactProposalClaim_of_clean
    (hcut : CleanCutClaim p) : ExactProposalClaim p := by
  exact outage_exactProposalClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hstrat := fun c E rho pt hb => (fgsa_fgFoundationClaim p c E rho pt hb).strat)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.2.2.1)

/-- ROOT-DIGEST W2b. Blueprint 03 §5. The Clean claims supply history and monotonicity.
The E1 Export proves the frozen post-gate inclusion claim. -/
theorem fgsa_cleanInclusionPostGateClaim_of_clean
    (hcut : CleanCutClaim p) :
    CleanInclusionPostGateClaim p := by
  exact outage_cleanInclusionPostGateClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hstrat := fun c E rho pt hb => (fgsa_fgFoundationClaim p c E rho pt hb).strat)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.2.2.1)
    (hmono := by
      intro V _ _ In c E rho ΔF pt hc
      exact (cleanSafety_of_cut p hcut (by
        intro V _ _ In c E rho ΔF h
        have hc := h.sleepPre.sleepPre
        have hq := h.pre.faultQ
        have hp : SourceDisciplinePrem p c E rho () := ⟨hc.base, hq⟩
        have hf := fgsa_fgFoundationClaim p c E rho () hp
        have hf' : FGFoundation p c E rho :=
          ⟨hf.store, hf.cumul, hf.mono, hf.frame, hf.geo, hf.strat, hf.reconcile⟩
        have hsrc := fgsa_srcFrameAboveClaim p c E rho () hp
        refine ⟨clean_sCompatible p c E rho hc hq hf' hsrc, ?_⟩
        intro i j x _ hj hij _
        exact sExtends p c E rho hc hq hf' hsrc x i j hij hj) c E rho (ΔF := ΔF) pt hc).2.1)

/-- ROOT-DIGEST W2b. Blueprint 03 §5. The Clean claims supply history and monotonicity.
The E1 Export proves the frozen inclusion claim. -/
theorem fgsa_cleanInclusionClaim_of_clean
    (hcut : CleanCutClaim p) : CleanInclusionClaim p := by
  exact outage_cleanInclusionClaim_of p
    (hstore := fun c E rho => (fgsa_activeViewAt p c E rho).1)
    (hframe := fun c E rho => (fgsa_frameAt p c E rho).1)
    (hsrc := fgsa_srcFrameAboveClaim p)
    (hstrat := fun c E rho pt hb => (fgsa_fgFoundationClaim p c E rho pt hb).strat)
    (hordered := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).1)
    (hnonempty := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.1)
    (htransfer := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.1)
    (hleases := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.1)
    (hrows := by
      intro V _ _ In c E rho ΔF pt hc
      exact (clean_history_supplier p hcut c E rho (ΔF := ΔF) pt hc).2.2.2.2.2.1)
    (hReaderGate := by
      intro V _ _ In c E rho ΔF pt hc
      exact clean_reader_gate_supplier p c E rho hc)
    (hReaderMono := by
      intro V _ _ In c E rho ΔF pt hc
      exact clean_reader_mono_supplier p hcut c E rho hc)

/-- The real supplier composition consumes the actual Clean sleep regime only. -/
private theorem assembly_clean_growth_suppliers {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hcutClaim : CleanCutClaim p) {ΔF : Time}
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
  have hFacts := hcutClaim c E rho ⟨rho.horizon⟩ ⟨hcut⟩
  have hHist := hFacts.1
  have hTrunc := hFacts.2
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

/-- ROOT-DIGEST W2b. Blueprint 03 §5. Clean and P-Ou produce both growth callbacks. -/
theorem fgsa_cleanGrowthClaim_of_clean
    (hcut : CleanCutClaim p) : CleanGrowthClaim p := by
  apply outage_cleanGrowthClaim_of p
  · intro V _ _ In c E rho ΔF hs s B hprop hgate u x g hu hup hx hg
    exact (assembly_clean_growth_suppliers hcut hs ⟨s, B⟩ hprop hgate).2.1 u x g hu hup hx hg
  · intro V _ _ In c E rho ΔF hs s B hprop hgate
    exact (assembly_clean_growth_suppliers hcut hs ⟨s, B⟩ hprop hgate).2.2

/-- P15-CUT: P-Ar derives every in-cut prefix receipt from OutageSleep₂.
The earlyTime(q) <= b₀ guard stays in the public per-label predicate. -/
theorem fgsa_outagePrefixReceiptClaim : OutagePrefixReceiptDerivedClaim p :=
  arming_prefix_batch_receipt p

/-- Blueprint 03 §9. Named foundation and finite Clean producers supply the outage claim. -/
theorem fgsa_outageCompatClaim_of_clean
    (_hcut : CleanCutClaim p) : OutageCompatClaim p :=
  outage_outageCompatClaim_of p
    (fgsa_fgFoundationClaim p) (fgsa_srcFrameAboveClaim p)
    (fgsa_sourceDisciplineClaim p) (assembly_outage_clean_cut_supplier p)

/-- Blueprint 03 §9.1. The true-mode P1 projection supplies the fast claim. -/
theorem fgsa_fastP1Claim_of_clean
    (hcut : CleanCutClaim p) : FastP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact (fgsa_outageCompatClaim_of_clean p hcut c E rho true pt ΔF h).1

/-- Blueprint 03 §9.2. The false-mode claim keeps the pending-gate lease clause. -/
theorem fgsa_slowP1Claim_of_clean
    (hcut : CleanCutClaim p) : SlowP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  exact fgsa_outageCompatClaim_of_clean p hcut c E rho false pt ΔF h

end AvailableChain.FGSA.Run
end
