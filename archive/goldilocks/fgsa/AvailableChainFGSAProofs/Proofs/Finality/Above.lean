module
public import AvailableChainFGSAProofs.Proofs.Finality.Forward
public import AvailableChainFGSAProofs.Proofs.Finality.FrontierBound

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [Fintype V] in
private theorem above_accepts_read {x : V} {U : FGBlock (Fin p.n)} {D : Time}
    (hs : V2.D.ScheduleWellFormed E rho)
    (h : AcceptsFinalBefore p c E rho x U D) :
    FGBlock.Preceq U (V2.D.Run.readAt E rho D x).st.fg.F := by
  have hm := fgsa_monoAlong_preceq_F p c U
  obtain ⟨i, _, hbefore, hU⟩ :=
    (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs hm
      (finality_restore_preceq_F p c U)).mp h
  have hi : i ≤ timeIdx rho D := by
    by_contra hn
    obtain ⟨e, he, ht⟩ := hbefore (timeIdx rho D) (Nat.lt_of_not_ge hn)
    exact Nat.lt_irrefl _ ((V2.D.Engine.index_lt_read_length_iff hs D he).mpr ht.le)
  rw [Gen.V2.Duty.MonoAlong_def] at hm
  rw [V2.D.Engine.readAt_eq_stateBefore hs]
  exact V2.D.Engine.stateBefore_stable_restore _ hm.1 hm.2.1 hm.2.2 E rho hi x
    (finality_restore_preceq_F p c U) hU

/-- Paper 22:1434–1451; firstfin plan §7 F-ABOVE-B.
DC: W4D2GradeCallsite.lean:431; INTENTIONAL healing-input route.
The same healing input and first kernel deadline select the second window.
Strict growth follows at its honest opening proposer, including first-window equality. -/
theorem above_frontier_FE_W_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : AboveFrontierPrem_W p c G ΔF .recFE g w E rho pt)
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
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t) :
    ∃ U : FGBlock (Fin p.n), honestFrontier p c E rho pt.t < (heightView p U).h ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (pt.t + 2 * W_W p ΔF g) := by
  have first : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho pt :=
    ⟨h.set, h.input, h.start, h.firstHorizon⟩
  obtain ⟨_, r₁, A₁, Afg₁, U₁, d₁, D₁, _, _, _, _, htr₁, hA₁, heA₁, _, _, hd₁,
    high₁, _, _, hU₁, eqD₁, hD₁, _, _, _, _, hacc₁⟩ :=
    (ForwardWitness_W_def p c E rho ΔF g w pt.t).mp
      (forward_witness_FE_of p c E rho hServices G ΔF g w hδ pt first
        hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore)
  have hcut : pt.t < p.actionTime r₁ := by
    rw [kmid_period_eq] at htr₁
    rw [kmid_actionTime_eq]
    have := p.deltaPos
    linarith
  have cap := honestFrontier_le_opening p c E rho h.set.core.base h.set.core.faultQ
    w ΔF h.input r₁ A₁ Afg₁ hA₁ heA₁ (hd₁ ▸ high₁) pt.t hcut hNames hOrigin
  have hP : 0 < P p := by
    have hR : 0 < p.R := by have := p.RLarge; omega
    exact mul_pos (mul_pos (by decide) (Int.natCast_pos.mpr hR)) p.deltaPos
  have hb : 0 ≤ betaF p ΔF := by
    rw [betaF_def]
    exact mul_nonneg (mul_nonneg (by decide) (Int.natCast_nonneg _)) p.deltaPos.le
  have htD₁ : pt.t ≤ D₁ := by
    rw [eqD₁, kernelDeadlineW_def, Nat.cast_add, Nat.cast_ofNat]
    have := p.deltaPos
    nlinarith
  have second : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho ⟨D₁⟩ := {
    set := h.set, input := h.input, start := h.start.trans htD₁
    hhor := by have := h.hhor; dsimp only; linarith }
  obtain ⟨_, r₂, A₂, Afg₂, U₂, _, D₂, _, _, _, _, _, hA₂, heA₂, _, _, hd₂,
    _, _, _, hU₂, _, hD₂, _, _, _, hSA₂, hacc₂⟩ :=
    (ForwardWitness_W_def p c E rho ΔF g w D₁).mp
      (forward_witness_FE_of p c E rho hServices G ΔF g w hδ ⟨D₁⟩ second
        hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore)
  have hs := h.set.core.base.valid.toScheduleWellFormed
  let x := V2.D.proposerOf rho (fgsaInterface p c) (r₂ * p.R)
  have hx : x ∈ rho.honest := hA₂.1.2
  have hUF := above_accepts_read p c E rho hs (hacc₁ x hx)
  have hstartHor : tstar p w ≤ rho.horizon := h.start.trans
    ((le_add_of_nonneg_right (finality_window_nonneg p ΔF g)).trans h.firstHorizon)
  have hFS := h.input.healed.2.2.1 _ x x
    (fgsa_healSuffix_timeIdx E rho hs second.start) hx
    (finality_input_suffix_confirmed p c E rho h.set.core.toRecovery₂ h.input hx
      (fgsa_healSuffix_timeIdx E rho hs second.start) hstartHor)
  have hout := fgsa_outputAt_eq_S_at E rho hs (fgsaInterface p c).stable (by simp) x D₁
  change (V2.D.Run.readAt E rho D₁ x).st.base.stableRecord = _ at hout
  have hread := V2.D.Engine.readAt_eq_stateBefore hs D₁
  have hFA : Block.Preceq
      (eraseFG (V2.D.Run.readAt E rho D₁ x).st.fg.F) (eraseFG Afg₂) := by
    rw [heA₂]
    apply block_preceq_trans _ (hSA₂ x hx)
    rw [hout, hread]
    exact hFS
  have hheight := (fgCertificateLaws p).height.h_mono
    (KitFG.preceq_trans hUF (kmid_lift_preceq p hFA))
  refine ⟨U₂, ?_, ?_⟩
  · calc
      honestFrontier p c E rho pt.t ≤ (heightView p U₁).h := by
        rw [hU₁, ← hd₁]
        exact cap
      _ < (heightView p U₂).h := by
        rw [hU₂, ← hd₂]
        exact Nat.lt_succ_of_le hheight
  · have hdeadline : D₂ < pt.t + 2 * W_W p ΔF g := by linarith
    intro y hy
    exact finality_acceptsFinalBefore_mono_deadline p c E rho hs hdeadline.le (hacc₂ y hy)

/-- Paper 22:1434–1451; firstfin plan §7 F-ABOVE-B.
DC: W4D2GradeCallsite.lean:431; INTENTIONAL healing-input route.
The same healing input and first kernel deadline select the second window.
Strict growth follows at its honest opening proposer, including first-window equality. -/
theorem above_frontier_F4_W_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtT)
    (h : AboveFrontierPrem_W p c G ΔF .recF4 g w E rho pt)
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
        p.actionTime r < cut → h < b + 1) → (heightView p W).h < b + 2)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t) :
    ∃ U : FGBlock (Fin p.n), honestFrontier p c E rho pt.t < (heightView p U).h ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x U (pt.t + 2 * W_W p ΔF g) := by
  have hFE : AboveFrontierPrem_W p c G ΔF .recFE g w E rho pt := {
    set := {
      core := h.set.core, bound := h.set.bound
      recur := F4_W_implies_FE_W h.set.recur }
    input := h.input, start := h.start, firstHorizon := h.firstHorizon, hhor := h.hhor }
  exact above_frontier_FE_W_of p c E rho hServices G ΔF g w hδ pt hFE
    hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore hNames hOrigin

end AvailableChain.FGSA.Run
end
