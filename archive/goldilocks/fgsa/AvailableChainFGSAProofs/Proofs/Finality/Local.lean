module
public import AvailableChainFGSAProofs.Proofs.Finality.Forward

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem local_certificate_le (K : FGBlock (Fin p.n)) :
    (finalityView p K).h_F ≤ (heightView p (finalityView p K).F).h := by
  by_cases hz : (finalityView p K).h_F = 0
  · rw [hz]
    exact Nat.zero_le _
  · obtain ⟨C, _, _, _, birth, _⟩ := (fgCertificateLaws p).finality_origin K hz
    rw [JustificationBirth_def] at birth
    have he := (fgCertificateLaws p).height.entry_same_height C.parent
    rw [birth.2.2.1, birth.2.1] at he
    exact he.ge

/-- Paper 22:1371–1380; firstfin plan §5 B. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL strict extension and certificate height, including genesis 0/1.
The comparisons use each node's inclusive state; acceptance stays strict-before. -/
theorem finality_liveness_of_forward_W {G ΔF : Time} {g : Nat} {w : HealingWitness}
    {pt : PtT} (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt)
    (hf : ForwardWitness_W p c E rho ΔF g w pt.t) :
    ∃ U : FGBlock (Fin p.n),
      (∀ x ∈ rho.honest,
        Block.Prec (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord (eraseFG U)) ∧
      (∀ x ∈ rho.honest, ∀ K ∈ (V2.D.Run.readAt E rho pt.t x).st.fg.TF,
        (finalityView p K).F = (V2.D.Run.readAt E rho pt.t x).st.fg.F →
        (finalityView p K).h_F < (heightView p U).h) ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (pt.t + W_W p ΔF g) := by
  obtain ⟨_, _, A, Afg, U, d, D, _, _, _, _, _, _, heA, _, _, hd, _,
    hAU, hne, hU, _, hD, _, _, _, hSA, hacc⟩ :=
      (ForwardWitness_W_def p c E rho ΔF g w pt.t).mp hf
  have hs := h.set.core.base.valid.toScheduleWellFormed
  have hstartHor : tstar p w ≤ rho.horizon := h.start.trans
    ((le_add_of_nonneg_right (finality_window_nonneg p ΔF g)).trans h.hhor)
  have hstrict : eraseFG Afg ≠ eraseFG U := fun he => hne (kmid_eraseFG_inj p he)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro x hx
    have hSU := block_preceq_trans (hSA x hx) (heA ▸ eraseFG_preceq hAU)
    have hneSU : (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord ≠ eraseFG U := by
      intro he
      have hUA : Block.Preceq (eraseFG U) (eraseFG Afg) := by
        simpa only [he, ← heA] using hSA x hx
      exact hstrict (block_preceq_antisymm (eraseFG_preceq hAU) hUA)
    change (!decide ((V2.D.Run.readAt E rho pt.t x).st.base.stableRecord = eraseFG U) &&
      Block.preceq (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord (eraseFG U)) = true
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hneSU, hSU⟩
  · intro x hx K _ hKF
    have hout := fgsa_outputAt_eq_S_at E rho hs (fgsaInterface p c).stable
      (by simp) x pt.t
    change (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord = _ at hout
    have hread := V2.D.Engine.readAt_eq_stateBefore hs pt.t
    have hFS := h.input.healed.2.2.1 _ x x
      (fgsa_healSuffix_timeIdx E rho hs h.start) hx
      (finality_input_suffix_confirmed p c E rho h.set.core.toRecovery₂ h.input hx
        (fgsa_healSuffix_timeIdx E rho hs h.start) hstartHor)
    have hFA : Block.Preceq
        (eraseFG (V2.D.Run.readAt E rho pt.t x).st.fg.F) (eraseFG Afg) := by
      rw [heA]
      apply block_preceq_trans _ (hSA x hx)
      rw [hout, hread]
      exact hFS
    have hheight := (fgCertificateLaws p).height.h_mono (kmid_lift_preceq p hFA)
    have hcert := local_certificate_le p K
    rw [hKF] at hcert
    rw [hU, ← hd]
    exact Nat.lt_succ_of_le (hcert.trans hheight)
  · intro x hx
    exact finality_acceptsFinalBefore_mono_deadline p c E rho hs hD.le (hacc x hx)

/-- Paper 22:1371–1400; firstfin plan §5 B. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness; the inherited kernel inputs remain inline. -/
theorem finality_liveness_FE_W_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    ∃ U : FGBlock (Fin p.n),
      (∀ x ∈ rho.honest,
        Block.Prec (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord (eraseFG U)) ∧
      (∀ x ∈ rho.honest, ∀ K ∈ (V2.D.Run.readAt E rho pt.t x).st.fg.TF,
        (finalityView p K).F = (V2.D.Run.readAt E rho pt.t x).st.fg.F →
        (finalityView p K).h_F < (heightView p U).h) ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (pt.t + W_W p ΔF g) := by
  exact finality_liveness_of_forward_W p c E rho h
    (forward_witness_FE_of p c E rho hServices G ΔF g w hδ pt h
      hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore)

/-- Paper 22:1371–1400; firstfin plan §5 B. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL local W liveness; the inherited kernel inputs remain inline. -/
theorem finality_liveness_F4_W_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : FinalityLivenessPrem_W p c G ΔF .recF4 g w E rho pt)
    (hsel : TRowsSelect p c E rho)
    (horigin : ∀ (i : Nat) (x : V) (B : FGBlock (Fin p.n)),
      HeldAt p c E rho i x B → ∀ u ∈ chainRows B,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hQC : RQCOrigin p c E rho) (hXing : RXing p c E rho)
    (hI3 : FinalizedSafetyPrem p c E rho () →
      ∀ C W T₁ T₂ h₁ h₂,
        FinalityBlock p c E rho C → FinalityBlock p c E rho W →
        FinalityFinalizedAt p C T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
        FGBlock.compatible T₁ T₂ = true)
    (hStrat : ∀ j z W, z ∈ rho.honest → W ∈ (storeAt p c E rho j z).fg.TF →
      ∀ J ∈ certified p W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore p c E rho j u r a ∧
        namedEntry a.payload.height_pair = some ((heightView p J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt p c E rho j z r a →
      namedEntry a.payload.height_pair = some e → ∃ C,
        actionSourceFG p c E rho z r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin p.n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt p c E rho j z W →
      (∀ k u r a row h T timeout, HonestRowAt p c E rho k u r a →
        RowWire.toRow? a = some row → row.height_pair = .vote h T timeout →
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2) :
    ∃ U : FGBlock (Fin p.n),
      (∀ x ∈ rho.honest,
        Block.Prec (V2.D.Run.readAt E rho pt.t x).st.base.stableRecord (eraseFG U)) ∧
      (∀ x ∈ rho.honest, ∀ K ∈ (V2.D.Run.readAt E rho pt.t x).st.fg.TF,
        (finalityView p K).F = (V2.D.Run.readAt E rho pt.t x).st.fg.F →
        (finalityView p K).h_F < (heightView p U).h) ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (pt.t + W_W p ΔF g) := by
  have hFE : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt := {
    set := {
      core := h.set.core
      bound := h.set.bound
      recur := F4_W_implies_FE_W h.set.recur }
    input := h.input, start := h.start, hhor := h.hhor }
  exact finality_liveness_FE_W_of p c E rho hServices G ΔF g w hδ pt hFE
    hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore

end AvailableChain.FGSA.Run
end
