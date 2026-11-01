module
public import AvailableChainFGSAProofs.Proofs.Finality.Forward

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Paper 22:1421–1430; firstfin plan §6. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL specified proposal coverage from the same forward Afg/U.
H3 serves X at its gate; H4 orders the gates at the actual opening proposer. -/
theorem proposal_final_of_forward_W {G ΔF : Time} {g : Nat} {w : HealingWitness}
    {pt : PtSX} (h : ProposalFinalPrem_W p c G ΔF .recFE g w E rho pt)
    (hf : ForwardWitness_W p c E rho ΔF g w
      (V2.D.proposalTime (fgsaInterface p c) pt.s)) :
    ∃ Xfg : FGBlock (Fin p.n), eraseFG Xfg = pt.X ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg
        (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g) := by
  obtain ⟨_, r, A, Afg, U, _, D, _, _, _, _, htr, hA, heA, _, _, _, _,
    hAU, _, _, _, hD, _, exA, hhA, _, hacc⟩ :=
      (ForwardWitness_W_def p c E rho ΔF g w _).mp hf
  have hs := h.set.core.base.valid.toScheduleWellFormed
  have hΔ := p.deltaPos
  have hslot : pt.s ≤ r * p.R := by
    rw [proposalTime_fgsa, kmid_period_eq] at htr
    change 4 * p.Δ * (pt.s : Time) ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) at htr
    have hc : (pt.s : Time) ≤ ((r * p.R : Nat) : Time) := by nlinarith
    exact_mod_cast hc
  have hu : w.u < pt.s := by
    by_contra hn
    have hscale := kmid_slot_scale_le p (Nat.le_of_not_gt hn)
    have hstart := h.start
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ ≤ 4 * p.Δ * (pt.s : Time) at hstart
    linarith
  have exX := h.input.ac.h3 pt.s pt.X h.prop
    (h.input.wit.proposal_lower.trans hu.le)
  have hgate : SA.gateTime p.toParams pt.s ≤ SA.gateTime p.toParams (r * p.R) := by
    have hscale := kmid_slot_scale_le p hslot
    change 4 * p.Δ * (pt.s : Time) + 6 * p.Δ ≤
      4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    linarith
  have hhX := hgate.trans hhA
  have hstartX : tstar p w ≤ SA.gateTime p.toParams pt.s := by
    have hstart := h.start
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ ≤ 4 * p.Δ * (pt.s : Time) at hstart
    change 4 * p.Δ * (w.u : Time) + 6 * p.Δ ≤ 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    linarith
  have hgateStar : isGateTime p (tstar p w) = true :=
    (isGateTime_iff p _).mpr ⟨w.u, rfl⟩
  have hsX : HealSuffix p c rho (tstar p w)
      (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) := by
    change (if isGateTime p (tstar p w) then _ else _) ≤ _ ∧ _
    rw [hgateStar, ite_eq_left rfl]
    exact ⟨afterTicksIdx_mono rho hstartX, List.length_filter_le _ _⟩
  have hsA : HealSuffix p c rho (tstar p w)
      (afterTicksIdx rho (SA.gateTime p.toParams (r * p.R))) :=
    ⟨hsX.1.trans (afterTicksIdx_mono rho hgate), List.length_filter_le _ _⟩
  let y := V2.D.proposerOf rho (fgsaInterface p c) (r * p.R)
  have hy : y ∈ rho.honest := hA.1.2
  have hcut : E.t_GST ≤ slotStartZ p (pt.s : Int) := by
    have hsync := h.input.wit.synchronous
    have hlow : (w.sStar : Int) + 2 ≤ (w.u : Int) := by
      exact_mod_cast h.input.wit.proposal_lower
    have hus : (w.u : Int) ≤ (pt.s : Int) := by exact_mod_cast hu.le
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hsync
    change E.t_GST ≤ 4 * p.Δ * (pt.s : Int)
    nlinarith [p.deltaPos]
  have hreaderX := finality_recovery_confirmed p c E rho h.set.core.toRecovery₂
    hy pt.s _ _ hcut le_rfl hhX
    (fun j hj => kmid_tick_lt_afterTicks p c E rho hs hj le_rfl)
  have hreaderA := finality_recovery_confirmed p c E rho h.set.core.toRecovery₂
    hy (r * p.R) _ _ (hcut.trans (kmid_slot_scale_le p hslot)) le_rfl hhA
    (fun j hj => kmid_tick_lt_afterTicks p c E rho hs hj le_rfl)
  have hX := (exX.2 hhX y hy hreaderX).2.2.2.1
  have hAA := (exA.2 hhA y hy hreaderA).2.2.2.1
  rw [afterTicks_eq_stateBefore E rho hs] at hX hAA
  change S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) y = pt.X at hX
  change S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (r * p.R))) y = A at hAA
  have hXA : Block.Preceq pt.X A := by
    have hmono := h.input.ac.h4.2.2.1 _ _ y hsX hsA
      (afterTicksIdx_mono rho hgate)
      (finality_input_suffix_confirmed p c E rho h.set.core.toRecovery₂ h.input hy
        hsX (hstartX.trans hhX))
      (finality_input_suffix_confirmed p c E rho h.set.core.toRecovery₂ h.input hy
        hsA (hstartX.trans hhX))
    rwa [hX, hAA] at hmono
  obtain ⟨Xfg, heX, _, _, _, _⟩ := kmid_opening_carrier p c E rho hs h.prop
  have hXU : FGBlock.Preceq Xfg U := KitFG.preceq_trans
    (kmid_lift_preceq p (by simpa only [heX, heA] using hXA)) hAU
  refine ⟨Xfg, heX, ?_⟩
  intro x hx
  exact finality_acceptsFinalBefore_mono_ancestor p c E rho hs hXU hD.le (hacc x hx)

/-- Paper 22:1421–1430; firstfin plan §6. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL proposal-relative W deadline. The frozen forward producer is called
once, with its named inline kernel inputs unchanged. -/
theorem proposal_final_FE_W_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtSX)
    (h : ProposalFinalPrem_W p c G ΔF .recFE g w E rho pt)
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
    ∃ Xfg : FGBlock (Fin p.n), eraseFG Xfg = pt.X ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg
        (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g) := by
  have hlocal : FinalityLivenessPrem_W p c G ΔF .recFE g w E rho
      ⟨V2.D.proposalTime (fgsaInterface p c) pt.s⟩ := {
    set := h.set, input := h.input, start := h.start, hhor := h.hhor }
  exact proposal_final_of_forward_W p c E rho h
    (forward_witness_FE_of p c E rho hServices G ΔF g w hδ
      ⟨V2.D.proposalTime (fgsaInterface p c) pt.s⟩ hlocal
      hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore)

/-- Paper 22:1421–1430; firstfin plan §6. DC-CS/W4FKChainSecondCheckpoint.lean:43:
INTENTIONAL F4 conversion through F4_W_implies_FE_W; the FE proof and its
proposal-relative deadline are reused. -/
theorem proposal_final_F4_W_of
    (hServices : FinalityActionReceipts p c E rho)
    (G ΔF : Time) (g : Nat) (w : HealingWitness)
    (hδ : p.δt = 2 * p.R) (pt : PtSX)
    (h : ProposalFinalPrem_W p c G ΔF .recF4 g w E rho pt)
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
    ∃ Xfg : FGBlock (Fin p.n), eraseFG Xfg = pt.X ∧
      ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x Xfg
        (V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g) := by
  have hFE : ProposalFinalPrem_W p c G ΔF .recFE g w E rho pt := {
    set := {
      core := h.set.core, bound := h.set.bound
      recur := F4_W_implies_FE_W h.set.recur }
    input := h.input, prop := h.prop, start := h.start, hhor := h.hhor }
  exact proposal_final_FE_W_of p c E rho hServices G ΔF g w hδ pt hFE
    hsel horigin hBatch hQC hXing hI3 hStrat hEmittedSource hcapBefore

end AvailableChain.FGSA.Run
end
