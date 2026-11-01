module
public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (L42 export boundary)

public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (B34 lane join)

public section

/-! Frozen Finality claims, exposed through the L42 assembly boundary (ruling B30). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

private structure FinalitySuppliers (p : Params) : Prop where
  hsel : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → TRowsSelect p c E rho
  horigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.ExecutionValid E rho → ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t
  hBatch : ∀ ΔF, BatchCoverage p ΔF .target

  hQC : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RQCOrigin p c E rho
  hXing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      RXing p c E rho
  hI3 : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true
  hStrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root)
  hEmittedSource : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C
  hcapBefore : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      ∀ (G ΔF : Time), Recovery₂ p c E rho G ΔF →
      ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2

private theorem finality_closed_suppliers (p : Params) : FinalitySuppliers p := by
  constructor
  · intro V _ _ In c E rho hv
    exact fgsa_tRowsSelect p c E rho hv
  · intro V _ _ In c E rho hv
    exact held_chain_row_origin_before p c E rho
      hv.toUnforgeableSignatures hv.toScheduleWellFormed
  · intro ΔF
    exact fgsa_batchCoverage p ΔF .target
  · intro V _ _ In c E rho G ΔF hR
    exact sourceDiscipline_qcOrigin p c E rho
      (pt := ()) ⟨hR.base, hR.faultQ⟩ (fgsa_rStore p c E rho)
  · intro V _ _ In c E rho G ΔF hR
    exact fgsa_rXing (hroots := hR.base.idealization) p c E rho hR.base.linked
      hR.faultX_count_rec hR.base.valid.toUnforgeableSignatures
  · intro V _ _ In c E rho G ΔF _ hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement (hroots := hp.set.idealization) p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · intro V _ _ In c E rho G ΔF hR
    have hs := sourceDiscipline_strat p c E rho
      (pt := ()) ⟨hR.base, hR.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro V _ _ In c E rho G ΔF hR j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := ()) ⟨hR.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro V _ _ In c E rho G ΔF hR cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hR.base.linked hR.base.valid
        hR.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hR.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

/-- ROOT-DIGEST W2b. Paper 22:1171–1305 (F1–F9), lead ruling B34: close the W kernel suppliers.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention, exact signed
rows and actual receipt guards. Recovery₂ supplies every Foundations premise. -/
theorem fgsa_finalityKernel_W (p : Params) : FinalityKernelClaim_W p := by
  apply fgsa_finalityKernel_W_of p (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
  · intro V _ _ In c E rho hv
    exact fgsa_tRowsSelect p c E rho hv
  · intro V _ _ In c E rho hv
    exact held_chain_row_origin_before p c E rho
      hv.toUnforgeableSignatures hv.toScheduleWellFormed
  · intro ΔF
    exact fgsa_batchCoverage p ΔF .target
  · intro V _ _ In c E rho G ΔF pt hK
    exact sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
  · intro V _ _ In c E rho G ΔF pt hK
    exact fgsa_rXing (hroots := hK.set.base.idealization) p c E rho hK.set.base.linked
      hK.set.faultX_count_rec hK.set.base.valid.toUnforgeableSignatures
  · intro V _ _ In c E rho G ΔF pt _ hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement (hroots := hp.set.idealization) p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · intro V _ _ In c E rho G ΔF pt hK
    have hs := sourceDiscipline_strat p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro V _ _ In c E rho G ΔF pt hK j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hK.set.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro V _ _ In c E rho G ΔF pt hK cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hK.set.base.linked hK.set.base.valid
        hK.set.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hK.set.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

/-- ROOT-DIGEST W2b. Paper 00:1119–1134, 22:1171–1305; plan §4: close the joined W kernel.
DC-CS/W4FKChainSecondCheckpoint.lean:43: INTENTIONAL W retention and receipt.
Recovery₂ supplies every Foundations premise and the cutoff-scoped TVote receipts. -/
theorem fgsa_finalityKernelJoined_W (p : Params) :
    FinalityKernelJoinedClaim_W p := by
  apply fgsa_finalityKernelJoined_W_of p
    (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
  · intro V _ _ In c E rho hv
    exact fgsa_tRowsSelect p c E rho hv
  · intro V _ _ In c E rho hv
    exact held_chain_row_origin_before p c E rho
      hv.toUnforgeableSignatures hv.toScheduleWellFormed
  · intro ΔF
    exact fgsa_batchCoverage p ΔF .target
  · intro V _ _ In c E rho G ΔF pt hK
    exact sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
  · intro V _ _ In c E rho G ΔF pt hK
    exact fgsa_rXing (hroots := hK.set.base.idealization) p c E rho hK.set.base.linked
      hK.set.faultX_count_rec hK.set.base.valid.toUnforgeableSignatures
  · intro V _ _ In c E rho G ΔF pt _ hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement (hroots := hp.set.idealization) p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · intro V _ _ In c E rho G ΔF pt hK
    have hs := sourceDiscipline_strat p c E rho
      (pt := pt) ⟨hK.set.base, hK.set.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro V _ _ In c E rho G ΔF pt hK j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hK.set.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro V _ _ In c E rho G ΔF pt hK cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hK.set.base.linked hK.set.base.valid
        hK.set.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hK.set.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)

/-- ROOT-DIGEST W2b. Paper 22:1985–2009 (FT-Tail-W): close every tail supplier from Recovery₂
and HealingInput. DC: INTENTIONAL W Tail, with local receipt guards. -/
theorem fgsa_tailKernel_W (p : Params) : TailKernelClaim_W p := by
  apply fgsa_tailKernel_W_of p (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
  · intro V _ _ In c E rho G ΔF pt hT
    exact held_chain_row_origin_before p c E rho
      hT.set.base.valid.toUnforgeableSignatures hT.set.base.valid.toScheduleWellFormed
  · intro V _ _ In c E rho G ΔF pt hT
    exact fgsa_batchCoverage p ΔF .target
  · intro V _ _ In c E rho G ΔF pt hT
    have hqc := sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hT.set.base, hT.set.faultQ⟩ (fgsa_rStore p c E rho)
    have hnames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
          e = ((heightView p C).h, (heightView p C).T_h.root) := by
      intro j x r a e ha he
      have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hT.set.base⟩
      obtain ⟨e', C, _, hn, hsrc, hentry, _, _⟩ := hb.2.2 j x r a ha
      exact ⟨C, hsrc, (Option.some.inj (he.symm.trans hn)).trans hentry⟩
    exact high_target_row_covered p c E rho pt.w hT.input.t.h1 hqc hnames
      hT.set.base.linked hT.set.base.valid.toScheduleWellFormed
  · intro V _ _ In c E rho G ΔF pt hT
    exact sourceDiscipline_qcOrigin p c E rho
      (pt := pt) ⟨hT.set.base, hT.set.faultQ⟩ (fgsa_rStore p c E rho)
  · intro V _ _ In c E rho G ΔF pt hT hp
    simpa only [FinalityBlock_def, FinalityRunBlock_def,
      FinalityFinalizedAt_def, FGFinalizedAt_def] using
      (fgsa_wholeRunAgreement (hroots := hT.set.base.idealization) p c E rho
        (fgsa_slashableBound_of_base p c E rho hp.set hp.fault)).1
  · intro V _ _ In c E rho G ΔF pt hT
    have hs := sourceDiscipline_strat p c E rho
      (pt := pt) ⟨hT.set.base, hT.set.faultQ⟩ (fgsa_rStore p c E rho)
    rw [RStrat_def] at hs
    exact hs
  · intro V _ _ In c E rho G ΔF pt hT j z r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := pt) ⟨hT.set.base⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, hp, _⟩ := hb.2.2 j z r a ha
    have hee : e = e' := Option.some.inj (he.symm.trans hn)
    exact ⟨C, hsrc, hee.trans hentry, hp⟩
  · intro V _ _ In c E rho G ΔF pt hT cut b j z W hj hW hcut
    show (heightView p W).h < b + 2
    by_contra hlt
    obtain ⟨z', r, a, u, T, tmo, ⟨k, hk, hrow⟩, _, hd, _, hh⟩ :=
      fgsa_rCap_heightView p c E rho hT.set.base.linked hT.set.base.valid
        hT.set.faultQ b j z W hW (Nat.le_of_not_lt hlt)
    have hcutr : p.actionTime r < cut :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hT.set.base.valid.toScheduleWellFormed
        hrow.2.1 cut).mp (hk.trans_le hj)
    exact absurd (hcut k z' r a u (b + 1) T tmo hrow hd hh hcutr) (Nat.lt_irrefl _)
  · intro V _ _ In c E rho G ΔF pt hT
    exact fgsa_rMono p c E rho
  · intro V _ _ In c E rho G ΔF pt hT
    exact fgsa_rXing (hroots := hT.set.base.idealization) p c E rho hT.set.base.linked
      hT.set.faultX_count_rec hT.set.base.valid.toUnforgeableSignatures

/-- ROOT-DIGEST W2b. Paper 22:1371–1400; firstfin plan §5 C.
DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness. Recovery₂ supplies the K-JOIN producers
and the TVote receipts at both public per-read GST cutoffs. -/
theorem fgsa_finalityLivenessRecFE_W (p : Params) :
    FinalityLivenessRecFEClaim_W p := by
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_closed_suppliers p
  exact fgsa_finalityLivenessRecFE_W_of p
    (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
    sel origin batch qc crossing safety strat emitted cap

/-- ROOT-DIGEST W2b. Paper 22:1371–1400; firstfin plan §5 C.
DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness. Recovery₂ supplies the K-JOIN producers
and the TVote receipts at both public per-read GST cutoffs. -/
theorem fgsa_finalityLivenessRecF4_W (p : Params) :
    FinalityLivenessRecF4Claim_W p := by
  intro G ΔF g w hδ V _ _ In c E rho pt h
  apply fgsa_finalityLivenessRecFE_W p G ΔF g w hδ c E rho pt
  exact ⟨⟨h.set.core, h.set.bound, F4_W_implies_FE_W h.set.recur⟩,
    h.input, h.start, h.hhor⟩

/-- ROOT-DIGEST W2b. Paper 22:1421–1430; firstfin plan §6. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL closed specified proposal coverage with its proposal-relative deadline.
Recovery₂ supplies the same producers and cutoff-scoped receipts as local W liveness. -/
theorem fgsa_proposalFinalRecFE_W (p : Params) :
    ProposalFinalRecFEClaim_W p := by
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_closed_suppliers p
  exact fgsa_proposalFinalRecFE_W_of p
    (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
    sel origin batch qc crossing safety strat emitted cap

/-- ROOT-DIGEST W2b. Paper 22:1421–1430; firstfin plan §6. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL closed specified proposal coverage with its proposal-relative deadline.
Recovery₂ supplies the same producers and cutoff-scoped receipts as local W liveness. -/
theorem fgsa_proposalFinalRecF4_W (p : Params) :
    ProposalFinalRecF4Claim_W p := by
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_closed_suppliers p
  exact fgsa_proposalFinalRecF4_W_of p
    (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
    sel origin batch qc crossing safety strat emitted cap

end AvailableChain.FGSA.Run
end

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- ROOT-DIGEST W2b. Paper 22:1434–1451; firstfin plan §7 F-ABOVE-B.
DC: W4D2GradeCallsite.lean:431; INTENTIONAL healing-input route.
Recovery supplies the same kernel producers; the package also supplies source discipline
and timed held-row origin. Recovery₂ supplies the cutoff-scoped TVote receipts. -/
theorem fgsa_aboveFrontierRecFE_W (p : Params) :
    AboveFrontierRecFEClaim_W p := by
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_closed_suppliers p
  apply fgsa_aboveFrontierRecFE_W_of p
    (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
    sel origin batch qc crossing safety strat emitted cap
  · intro V _ _ In c E rho hb0 j x r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := ()) ⟨hb0⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, _, _⟩ := hb.2.2 j x r a ha
    exact ⟨C, hsrc, (Option.some.inj (he.symm.trans hn)).trans hentry⟩
  · intro V _ _ In c E rho hv
    exact held_chain_row_origin_before p c E rho
      hv.toUnforgeableSignatures hv.toScheduleWellFormed

/-- ROOT-DIGEST W2b. Paper 22:1434–1451; firstfin plan §7 F-ABOVE-B.
DC: W4D2GradeCallsite.lean:431; INTENTIONAL healing-input route.
Recovery supplies the same kernel producers; the package also supplies source discipline
and timed held-row origin. Recovery₂ supplies the cutoff-scoped TVote receipts. -/
theorem fgsa_aboveFrontierRecF4_W (p : Params) :
    AboveFrontierRecF4Claim_W p := by
  obtain ⟨sel, origin, batch, qc, crossing, safety, strat, emitted, cap⟩ :=
    finality_closed_suppliers p
  apply fgsa_aboveFrontierRecF4_W_of p
    (fun _ E rho D x => fgsa_target_service_genesis E rho D x)
    sel origin batch qc crossing safety strat emitted cap
  · intro V _ _ In c E rho hb0 j x r a e ha he
    have hb := sourceDiscipline_base p c E rho (pt := ()) ⟨hb0⟩
    obtain ⟨e', C, _, hn, hsrc, hentry, _, _⟩ := hb.2.2 j x r a ha
    exact ⟨C, hsrc, (Option.some.inj (he.symm.trans hn)).trans hentry⟩
  · intro V _ _ In c E rho hv
    exact held_chain_row_origin_before p c E rho
      hv.toUnforgeableSignatures hv.toScheduleWellFormed

end AvailableChain.FGSA.Run
end
