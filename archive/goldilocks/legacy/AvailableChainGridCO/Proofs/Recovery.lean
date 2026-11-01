module
public import AvailableChainGridCO.Proofs.RecoverySuffix

@[expose] public section

namespace AvailableChain.GridCO

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Proposal times have the same order as their labels. -/
theorem proposalTime_le_iff (p : Params) (r s : Slot) :
    proposalTime p r ≤ proposalTime p s ↔ r ≤ s := by
  have he := gateTime_le_iff p r s
  simpa only [gateTime, add_le_add_iff_right] using he

/-- A positive proposal label starts no more than 4Δ after GST. Taking
the strictly later proposal also handles GST zero and a boundary HEAD
whose own proposal was before GST. -/
theorem exists_recovery_start (p : Params) (τ : Time) (hτ : 0 ≤ τ) :
    ∃ b : Slot, 0 < b ∧ τ < proposalTime p b ∧ proposalTime p b ≤ τ + 4 * p.Δ := by
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hk : 0 ≤ τ / (4 * p.Δ) := Int.ediv_nonneg hτ hd.le
  refine ⟨(τ / (4 * p.Δ)).toNat + 1, Nat.succ_pos _, ?_, ?_⟩
  all_goals
    have hcast := Int.toNat_of_nonneg hk
    have hmod := Int.emod_nonneg τ (ne_of_gt hd)
    have hlt := Int.emod_lt_of_pos τ hd
    have heq := Int.mul_ediv_add_emod τ (4 * p.Δ)
    simp only [proposalTime, Nat.cast_add, Nat.cast_one, hcast]
    nlinarith

/-- Grid source support implies the shared admission-based invariant. -/
theorem admittedSources_of_gridSources {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (boundary : Slot)
    (hs : SourcesSupportedOutside p rho boundary ∅) : AdmittedSourcesSupported p rho boundary := by
  intro s hh source hsource B C g hd hc hp ha
  have hg : g ∈ p.grid ∧ g ≤ prefixSupport p (gateInput p rho s source) s B := by
    simpa using (List.mem_filter.mp ha).2
  exact hs s hh source hsource B C g hg.1 (by simp) hd hc hp hg.2

/-- Shared proposal repair once all admitted sources are supported. -/
theorem recovery_proposal_after_sources [LeasePolicy]
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (hexec : ExecutionValid (gridCO p) E rho)
    (hroot : RootInjective E (gridInterface p) rho)
    (hrelay : PartialSynchrony (gridCO p) E rho)
    (boundary : Slot) (hpos : 0 < boundary) (hstart : E.t_GST ≤ proposalTime p boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hsources : AdmittedSourcesSupported p rho boundary)
    (s : Slot) (hafter : proposalTime p boundary < proposalTime p s)
    (hawake : HonestAwakeProposer E rho s) (hh : gateTime p s ≤ rho.horizon) :
    ∃ B, HonestProposalAt E (gridInterface p) rho s B ∧
      (∀ reader ∈ rho.honest, stable (Run.readAt (gridCO p) rho (gateTime p s) reader) = B) ∧
      (∀ reader ∈ rho.honest, confirmation p (gateInput p rho s reader) s = some B) := by
  have hbs : boundary < s := by
    by_contra hn
    exact (not_lt.mpr ((proposalTime_le_iff p s boundary).mpr (Nat.le_of_not_gt hn))) hafter
  have hspos : 0 < s := hpos.trans hbs
  have htime : proposalTime p s ≤ rho.horizon := by
    dsimp [gateTime] at hh; linarith [p.deltaPos]
  obtain ⟨B, hB⟩ := honest_proposal_exists hexec hΔ s hspos hawake htime
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hspos)
  have hbr : boundary ≤ r := Nat.le_of_lt_succ hbs
  have hprev := hseq r hbr
    (((gateTime_le_iff p r (r + 1)).mpr (Nat.le_succ r)).trans hh)
  have hsync := hseq (r + 1) hbs.le hh
  have hb : voteTime p boundary ≤ proposalTime p (r + 1) := by
    have ht := (proposalTime_le_iff p boundary r).mpr hbr
    dsimp [voteTime, proposalTime] at *
    nlinarith [p.deltaPos]
  have hready : ProposalRelayReady p E rho (r + 1) := Or.inl ⟨by
    rw [hΔ]
    have := hstart
    dsimp [voteTime] at hb
    linarith, hrelay⟩
  exact ⟨B, hB, stage_honest_proposal_repair p E rho hΔ boundary r
    hsources hprev hsync hroot hready hb B hB⟩

theorem recovery_proposal_after_stages {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (hrec : RecoveryRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho)
    (boundary : Slot) (hpos : 0 < boundary) (hstart : E.t_GST ≤ proposalTime p boundary)
    (hsources : SourcesSupportedOutside p rho boundary ∅)
    (s : Slot) (hafter : proposalTime p boundary < proposalTime p s)
    (hawake : HonestAwakeProposer E rho s) (hh : gateTime p s ≤ rho.horizon) :
    ∃ B, HonestProposalAt E (gridInterface p) rho s B ∧
      (∀ reader ∈ rho.honest, stable (Run.readAt (gridCO p) rho (gateTime p s) reader) = B) ∧
      (∀ reader ∈ rho.honest, confirmation p (gateInput p rho s reader) s = some B) := by
  apply recovery_proposal_after_sources p E rho hΔ
    hrec.execution hrec.rootInjective
    hrec.partialSynchrony boundary hpos hstart _
    (admittedSources_of_gridSources p rho boundary hsources) s hafter hawake hh
  intro t hbt hhor
  exact synchronousLabel_of_recovery G hrec t
    (hstart.trans ((proposalTime_le_iff p boundary t).mpr hbt)) hhor

/-- Shared contract recovery from a supported boundary, proposer recurrence,
and a time bound. Admission policies supply the source and row invariants. -/
theorem recovered_of_source_boundary [LeasePolicy]
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (C : Constants) (hDc : 6 * p.Δ = C.D_c) (hDs : 6 * p.Δ = C.D_s)
    (hrec : RecoveryRegime (gridCO p) E (gridInterface p) C rho)
    (boundary : Slot) (hpos : 0 < boundary) (hstart : E.t_GST ≤ proposalTime p boundary)
    (hseq : ∀ t, boundary ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t)
    (hrows : RowsSupportedOutside p rho boundary ∅)
    (hsources : AdmittedSourcesSupported p rho boundary)
    (hbound : proposalTime p boundary + C.proposerGap + 6 * p.Δ ≤ E.t_GST + C.recoveryBound) :
    RecoveredAt (gridCO p) E (gridInterface p) C rho (E.t_GST + C.recoveryBound) := by
  let U := proposalTime p boundary
  let T := E.t_GST + C.recoveryBound
  have hUstart : E.t_GST ≤ U := hstart
  have hUhor : U + C.proposerGap ≤ rho.horizon := by
    have hh := hrec.horizon
    change T ≤ rho.horizon at hh
    linarith [p.deltaPos]
  obtain ⟨s, hslo, hshi, _, hawake⟩ := hrec.recurrence U hUstart hUhor
  change U < proposalTime p s at hslo
  change proposalTime p s ≤ U + C.proposerGap at hshi
  have hrepairTime : gateTime p s ≤ T := by
    dsimp [gateTime]; linarith
  have hh : gateTime p s ≤ rho.horizon := hrepairTime.trans hrec.horizon
  obtain ⟨B, _, hrepair, hconf⟩ := recovery_proposal_after_sources p E rho hΔ
    hrec.execution hrec.rootInjective
    hrec.partialSynchrony boundary hpos hUstart hseq hsources s hslo hawake hh
  have hfs : boundary ≤ s := (proposalTime_le_iff p boundary s).mp hslo.le
  have hsafe := safe_from_repaired_gate p E rho hΔ hrec.execution boundary hpos hseq hrows
    s hfs B hrepair hconf
  have hsafeT : SafeFrom (gridCO p) rho (gridInterface p).stable T := by
    refine ⟨?_, ?_⟩
    · intro u hu v hv t t' ht hht ht' hht'
      exact hsafe.agree u hu v hv t t' (hrepairTime.trans ht) hht (hrepairTime.trans ht') hht'
    · intro v hv t t' ht htt' hht'
      exact hsafe.monotone v hv t t' (hrepairTime.trans ht) htt' hht'
  have hincluded : IncludedFrom (gridCO p) E (gridInterface p) rho (gridInterface p).stable T
      (6 * p.Δ) := by
    intro slot htime hawake hhor
    change T < proposalTime p slot at htime
    change gateTime p slot ≤ rho.horizon at hhor
    have hafter : U < proposalTime p slot := by linarith [p.deltaPos]
    obtain ⟨D, hD, hrecords, _⟩ := recovery_proposal_after_sources p E rho hΔ
      hrec.execution hrec.rootInjective
      hrec.partialSynchrony boundary hpos hUstart hseq hsources slot hafter hawake hhor
    refine ⟨D, hD, ?_⟩
    intro reader hr
    change Block.Preceq D (stable (Run.readAt (gridCO p) rho (gateTime p slot) reader))
    rw [hrecords reader hr]
    exact block_preceq_self _
  exact ⟨hsafeT, hsafeT, hDc ▸ hincluded, hDs ▸ hincluded⟩

theorem recovered_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (_hG : 0 < G)
    (hrec : RecoveryRegime (gridCO p) E (gridInterface p) (gridConstants p G) rho) :
    RecoveredAt (gridCO p) E (gridInterface p) (gridConstants p G) rho
      (E.t_GST + (gridConstants p G).recoveryBound) := by
  obtain ⟨b, hbpos, hbstart, hbtime⟩ := exists_recovery_start p E.t_GST E.t_GST_nonneg
  let finish := b + p.grid.card * p.m
  let U := proposalTime p finish
  let T := E.t_GST + (gridConstants p G).recoveryBound
  have hbfinish : b ≤ finish := Nat.le_add_right _ _
  have hfpos : 0 < finish := hbpos.trans_le hbfinish
  have hseq : ∀ t, b ≤ t → gateTime p t ≤ rho.horizon → SynchronousLabel p E rho t := by
    intro t hbt hh
    exact synchronousLabel_of_recovery G hrec t
      (hbstart.le.trans ((proposalTime_le_iff p b t).mpr hbt)) hh
  obtain ⟨hrows, hsources⟩ := grid_sources_and_rows_from_engine p E rho hΔ
    hrec.execution b hbpos hseq
  have hUeq : U = proposalTime p b + (p.grid.card : Time) * (lifetime p + p.Δ) := by
    have he := healing_stage_time p b p.grid.card
    dsimp [voteTime] at he
    dsimp [U, finish]; linarith
  apply recovered_of_source_boundary p E rho hΔ (gridConstants p G) rfl rfl hrec
    finish hfpos (hbstart.le.trans ((proposalTime_le_iff p b finish).mpr hbfinish))
    (fun t hft hhor => hseq t (hbfinish.trans hft) hhor) hrows
    (admittedSources_of_gridSources p rho finish hsources)
  change U + G + 6 * p.Δ ≤ T
  rw [hUeq]
  dsimp [T, gridConstants]
  linarith

end AvailableChain.GridCO
end
