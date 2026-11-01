module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseService
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchAge
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchRepair
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchGap

public section

/-! Blueprint 21 HG.3 gap. TRepair, TCommon and TPerm have the named producers
healing_tRepair, healing_tCommon and healing_tPerm.
INLINE rowsReceipt: fgsa_tRowsReceipt; progressCoverage: fgsa_batchCoverage.
FaultQ and honestQuorum are the same explicit inputs as PromotionAge. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def p0d5cGapTiming (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0d5cGapTimingLaws (p : Params) :
    FGCompose.FGTimingLaws (p0d5cGapTiming p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl


variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}



/-- ROOT-DIGEST W2b. Blueprint 21 HG.3. DC: SAME lift the source path by root injectivity. -/
private theorem frontierSearch_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

/-- Blueprint 21 HG.3. DC: SAME period bound for the first opening. -/
theorem frontierSearch_period_bound (p : Params) : 8 * p.Δ ≤ P p := by
  exact FGCompose.frontierSearch_period_bound (p0d5cGapTiming p) (p0d5cGapTimingLaws p)

/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 gap. DC: SAME finish repair in a quiet settled phase.
The initial seed and every later seed keep the frozen first-label qualification. -/
theorem frontierSearch_gap_phase [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar u D : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {m : Nat} (hready : recoveryStart p E ≤ u)
    (hp : PhaseInterval p c E rho u D m none false)
    (mode : FrontierRepairStart p E G u ρbar)
    (hbudget : u + ρbar + (2 * P p + Γ p G - 4 * p.Δ) ≤ D) :
    ∃ t, u ≤ t ∧ t ≤ D ∧ StrongServed p c E rho m t := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  simp only [Time, Height] at *
  have hP := frontierSearch_period_bound p
  have hΓ := (fgsa_gamma_bounds p G).1
  have hbudget0 : u + ρbar ≤ D := by linarith [hrec.gapPos, p.deltaPos]
  obtain ⟨q, Q, hseed, hgate, hQ, hexact⟩ := frontierSearch_repair_seed E rho repair
    (healing_proposal_gap hrec) hrec.gapPos hready hp mode hbudget0
  have huq := frontierSearch_seed_after E hseed
  have hqg : SA.proposalTime p.toParams q ≤ SA.gateTime p.toParams q := by
    change _ ≤ SA.proposalTime p.toParams q + 6 * p.Δ
    linarith [p.deltaPos]
  have hgateD := hgate.trans hbudget0
  obtain ⟨iq, Qfg, hiq, hQmem, hErase⟩ := healing_rise_one_gate_copy p c E rho
    hrec.base.valid.toScheduleWellFormed hexact (hgateD.trans hp.2.1) hQ.1.2
    (healing_recovery_gate_reader hrec hQ.1.2 (hGST.trans huq) (hgateD.trans hp.2.1))
  obtain ⟨hlo, hhi⟩ := frontierSearch_proposal_heights E rho hrec crossing hready hp huq hgateD
    hQ hErase hexact
  by_cases hhigh : (heightView p Qfg).h = m
  · exact ⟨_, huq.trans hqg, hgateD,
      frontierSearch_save_seed E rho hready hp hseed hQ hErase hhigh hexact hgateD⟩
  have hlow : (heightView p Qfg).h = m - 1 := by
    have hlo' : m - 1 ≤ (heightView p Qfg).h := by simpa using hlo
    exact Nat.le_antisymm (Nat.le_sub_one_of_lt (lt_of_le_of_ne hhi hhigh)) hlo'
  have hex : ∃ r, q ≤ r * p.R := ⟨q, by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q
      (show 1 ≤ p.R from (by decide : 1 ≤ 2).trans p.RLarge)⟩
  let r := Nat.find hex
  have hqr : q ≤ r * p.R := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * p.R → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨h0, h1⟩ := common_first_time_bound (p := p) q r hqr hfirst
  have har : p.actionTime r ≤ u + ρbar + (P p - 4 * p.Δ) := by linarith
  have harD : p.actionTime r ≤ D := by linarith [hrec.gapPos, p.deltaPos]
  have hur : u ≤ p.actionTime r := by linarith
  have hpr := frontierSearch_phase_cut E rho hp hur harD
  obtain ⟨_, _, hc, _, _, hlowOr⟩ := common u m none false q Q Qfg r hready hQ hErase
    hexact huq hqr hfirst hpr
  obtain ⟨l, hlq, hrepair⟩ := frontierSearch_seed_repair E rho repair (healing_proposal_gap hrec)
    hrec.gapPos
    hready hseed (m := m) (J := none) (contested := false)
  have huvote : u ≤ SA.voteTime p.toParams (r * p.R) := by
    have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ
    change u ≤ 4 * p.Δ * (q : Time) at huq
    nlinarith [p.deltaPos]
  have hrl : SA.proposalTime p.toParams l < (r : Time) * P p := by
    have ht : SA.proposalTime p.toParams q ≤ (r : Time) * P p := by
      have hqrI : (q : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hqr
      change 4 * p.Δ * (q : Time) ≤ (r : Time) * (4 * (p.R : Time) * p.Δ)
      push_cast at hqrI
      nlinarith [p.deltaPos]
    exact hlq.trans_le ht
  have hstart : E.t_GST ≤ (r : Time) * P p := by
    have ha := actionTime_periodW p r
    have htg : SA.gateTime p.toParams q = SA.proposalTime p.toParams q + 6 * p.Δ := rfl
    linarith
  have finish {s : Slot} {X : FGBlock (Fin p.n)}
      (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X))
      (hlater : p.actionTime r < SA.proposalTime p.toParams s)
      (hsD : SA.gateTime p.toParams s ≤ D) (hh : m ≤ (heightView p X).h) :
      ∃ t, u ≤ t ∧ t ≤ D ∧ StrongServed p c E rho m t := by
    have hut : u ≤ SA.proposalTime p.toParams s := hur.trans hlater.le
    have hps := frontierSearch_phase_cut E rho hp
      (by change u ≤ SA.proposalTime p.toParams s + 6 * p.Δ; linarith [p.deltaPos]) hsD
    have hls : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s := by
      have ha := actionTime_periodW p r
      linarith [p.deltaPos]
    have hs := hrepair _ hps s _ hls le_rfl hnew
    have hheights := frontierSearch_proposal_heights E rho hrec crossing hready hp hut
      hsD hnew rfl hs
    have hh' : (heightView p X).h = m := Nat.le_antisymm hheights.2 hh
    have htq : SA.proposalTime p.toParams q < SA.proposalTime p.toParams s := by
      linarith
    exact ⟨_, by change u ≤ SA.proposalTime p.toParams s + 6 * p.Δ; linarith [p.deltaPos],
      hsD, frontierSearch_save_seed E rho hready hp (tfSeed_later p E hseed htq)
        hnew rfl hh' hs hsD⟩
  rcases hlowOr hlow with he | ⟨⟨x, K, hx, hK, hKh⟩, _⟩
  · let x := V2.D.proposerOf rho (fgsaInterface p c) q
    have hx : x ∈ rho.honest := hQ.1.2
    obtain ⟨K, nd, j, rSent, a, _, hK, _, hQK, _, _, _⟩ := hc x hx
    have hKheight := (he.choose_spec x K hx hK).1
    have hQKfg : FGBlock.Preceq Qfg K := frontierSearch_lift (hErase ▸ hQK)
    have hKU : (heightView p K).T_h = (heightView p Qfg).T_h :=
      ((fgCertificateLaws p).height.entry_plateau hQKfg (hlow.trans hKheight.symm)).symm
    let U := (heightView p Qfg).T_h
    have hQbase : Q ∈
        (rho.stateBefore E iq (V2.D.proposerOf rho (fgsaInterface p c) q)).st.base.blocks :=
      (cstoreInv_stateBefore E rho iq _).baseTree Q |>.mpr ⟨Qfg, hQmem, hErase⟩
    have hslot : U.slot ≤ q := by
      have hs := repair_stored_slot_le E rho hrec.base.valid iq _ Q hQbase (eraseFG U)
        (hErase ▸ eraseFG_preceq ((fgCertificateLaws p).height.entry_preceq Qfg))
      rw [eraseFG_slot, repair_proposal_slot E rho hQ] at hs
      exact hs
    have hage : SA.proposalTime p.toParams U.slot ≤ SA.proposalTime p.toParams q := by
      have hslotI : (U.slot : Time) ≤ q := by exact_mod_cast hslot
      change 4 * p.Δ * (U.slot : Time) ≤ 4 * p.Δ * (q : Time)
      nlinarith [p.deltaPos]
    have hgateBudget : max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
        (SA.proposalTime p.toParams U.slot + 2 * P p + Γ p G + 2 * p.Δ) ≤ D := by
      apply max_le
      · have heps := betaF_le_period p ΔF hbound
        rw [epsF_def]
        simp only [Time] at *
        linarith [p.deltaPos]
      · change SA.proposalTime p.toParams q + 6 * p.Δ ≤ u + ρbar at hgate
        linarith
    have hwindow : max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
        (SA.proposalTime p.toParams U.slot + 2 * P p - 4 * p.Δ) + G ≤ rho.horizon := by
      have ha := actionTime_periodW p r
      have heps := betaF_le_period p ΔF hbound
      apply le_trans _ hp.2.1
      rw [← max_add_add_right]
      apply max_le <;> simp only [Time] at * <;> linarith [p.deltaPos]
    obtain ⟨s, X, hnew, _, hlater, hsD, hh⟩ := frontierSearch_age_service E rho hrec
      hδ hbound perm rowsReceipt progressCoverage hfold faultQ honestQuorum he hc
      ⟨x, K, hx, hK, hKU⟩ hready hstart huvote hp hwindow hgateBudget
    apply finish hnew hlater hsD
    simpa only [Nat.sub_add_cancel hp.2.2.1] using hh
  · let b := (r : Time) * P p + 4 * p.Δ
    have hbGST : E.t_GST ≤ b := by dsimp only [b]; linarith [p.deltaPos]
    have hbhor : b + G ≤ rho.horizon := by
      apply le_trans _ hp.2.1
      dsimp only [b]
      have ha := actionTime_periodW p r
      linarith [p.deltaPos]
    obtain ⟨s, hloS, hhiS, hslotS⟩ := hrec.gap b hbGST hbhor
    rw [proposalTime_fgsa] at hloS hhiS
    have hsD : SA.gateTime p.toParams s ≤ D := by
      have ha := actionTime_periodW p r
      change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D
      dsimp only [b] at hhiS
      linarith
    have hsHor : SA.proposalTime p.toParams s ≤ rho.horizon := by
      change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D at hsD
      linarith [p.deltaPos, hp.2.1]
    have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
      have hlo := hloS
      dsimp only [b] at hlo
      change (r : Time) * P p + 4 * p.Δ < 4 * p.Δ * (s : Int) at hlo
      change E.t_GST ≤ 4 * p.Δ * ((s : Int) - 1)
      nlinarith [p.deltaPos]
    have hjoin := healing_recovery_restart_cutoff hrec hslotS.2 hsHor hcut
    obtain ⟨X, hnew, hXs, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂ hslotS
      (hbGST.trans hloS.le) hsHor hjoin
    have hslabel : r * p.R + 2 ≤ s := by
      dsimp only [b] at hloS
      change (r : Time) * (4 * (p.R : Time) * p.Δ) + 4 * p.Δ <
        4 * p.Δ * (s : Time) at hloS
      have hz : ((r * p.R : Nat) : Time) + 1 < s := by push_cast; nlinarith [p.deltaPos]
      exact_mod_cast Int.add_one_le_iff.mpr hz
    have hat : p.actionTime r < SA.proposalTime p.toParams s := by
      have ha := actionTime_periodW p r
      have hz : ((r * p.R + 2 : Nat) : Time) ≤ s := by exact_mod_cast hslabel
      change 4 * p.Δ * (s : Time) > _
      push_cast at hz
      change p.actionTime r = (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ at ha
      have hm := mul_le_mul_of_nonneg_left hz
        (show 0 ≤ 4 * p.Δ by linarith only [p.deltaPos])
      nlinarith only [hm, ha, p.deltaPos]
    have hpts := frontierSearch_phase_cut E rho hp (hur.trans hat.le)
      (by change SA.proposalTime p.toParams s + 6 * p.Δ ≤ D at hsD
          linarith only [hsD, p.deltaPos])
    have hparent := healing_promotion_source_parent E rho perm hready hpts huvote hat.le
      hx hK hslabel hnew
    have hpath : FGBlock.Preceq K X.parent := frontierSearch_lift
      ((eraseFG_parent X) ▸ hparent)
    have hPX : FGBlock.Preceq X.parent X := by
      cases X with
      | genesis => exact KitFG.preceq_refl _
      | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
    have hh : m ≤ (heightView p X).h := by
      have hKP := (fgCertificateLaws p).height.h_mono hpath
      have hPXh := (fgCertificateLaws p).height.h_mono hPX
      exact (hKh ▸ hKP).trans hPXh
    exact finish hnew hat hsD hh

/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 gap; run 2 R2-b.
DC: SAME finite first stop or the complete seed by the frozen gap deadline.
E_gF_eq is used only under LivenessBoundW. The horizon is closed. -/
theorem frontier_hg3_gap [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF ρbar : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (crossing : RXing p c E rho) (monoAll : RMonoAll p
      c E rho)
    (repair : TRepair p c E rho) (common : TCommon p c E rho)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {i m : Nat} {ev : V2.Event V (Obj p)}
    (hstart : FrontierSearchStart p c E rho i ev m .gap)
    (mode : FrontierRepairStart p E G (ev.time + 3 * p.Δ) ρbar)
    (hhor : ev.time + E_gF p ΔF G ρbar ≤ rho.horizon) :
    FrontierHG3Result p c E rho i m ev.time (ev.time + E_gF p ΔF G ρbar) := by
  apply (frontierHG3Result_iff p c E rho i m ev.time _).mpr
  have hsched := hrec.base.valid.toScheduleWellFormed
  obtain ⟨hi, hgst0, _, hfront, hm, hkind⟩ :=
    (frontierSearchStart_iff p c E rho i ev m .gap).mp hstart
  have hρ : 0 ≤ ρbar := by
    have hG := (fgsa_gamma_bounds p G).1
    have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
    cases mode with
    | two =>
      change 0 ≤ 2 * ((4 * (p.k : Time) - 1) * p.Δ) + Γ p G + 8 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos]
    | one =>
      change 0 ≤ (4 * (p.k : Time) - 1) * p.Δ + Γ p G + 10 * p.Δ
      nlinarith [p.deltaPos, hrec.gapPos]
  have hP := frontierSearch_period_bound p
  have hbudget : ev.time + 3 * p.Δ + ρbar +
      (2 * P p + Γ p G - 4 * p.Δ) = ev.time + E_gF p ΔF G ρbar := by
    rw [E_gF_eq p ΔF G ρbar hbound]
    change _ = ev.time + (ρbar + 2 * P p + Γ p G - p.Δ)
    ring
  rcases frontierSearch_first_effective_split p c E rho hsched i
      (ev.time + E_gF p ΔF G ρbar) with hstop | hquiet
  · rcases frontierSearch_classify_stop p c E rho monoAll hfront hstop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hG : 4 * p.Δ ≤ Γ p G := hrec.gapPos.trans (fgsa_gamma_bounds p G).1
  have htail0 : 0 ≤ 2 * P p + Γ p G - 4 * p.Δ := by
    linarith only [hP, hG, p.deltaPos]
  have hsettle : ev.time + 3 * p.Δ ≤ ev.time + E_gF p ΔF G ρbar := by
    rw [← hbudget]
    exact (le_add_of_nonneg_right hρ).trans (le_add_of_nonneg_right htail0)
  obtain ⟨J, hp, _⟩ := healing_settle_start_on (hroots := hrec.base.receiptIdealization)
    p c E rho crossing hrec.base.valid monoAll hrec
    (fun _ ht => healing_ready_read_cutoff E ht)
    (healing_phase_witness_receipts_recovery E rho hrec) i ev _ m .gap hi hgst0
    hsettle
    hhor hm hfront hkind hquiet
  have hgst : recoveryStart p E ≤ ev.time + 3 * p.Δ := by linarith [p.deltaPos]
  obtain ⟨t, hut, htD, hs⟩ := frontierSearch_gap_phase E rho hrec crossing repair common
    hδ hbound perm rowsReceipt progressCoverage hfold faultQ honestQuorum hgst hp mode
    hbudget.le
  exact Or.inr (Or.inr ⟨t, by linarith [p.deltaPos], htD, hs⟩)

end AvailableChain.FGSA.Run
end
