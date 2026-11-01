module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionAdvance
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionReceipt
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionPhase

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- Blueprint 21:1356–1419; frozen frontier plan §2.3, expanded in this lane.
DC: SAME renewed promotion keeps the effective-event alternative, strict first
receipt, and service only if the phase lasts through the selected gate.
Assembly supplies the three INLINE row/coverage/quorum facts and FaultQ,
RMono, RXing, TPerm and the progress fold. -/
theorem healing_renewedPromotion (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (services : ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (perm : TPerm p c E rho)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    (r : Nat) (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    ∀ u m J contested l q Q height,
      recoveryStart p E ≤ u → PhaseInterval p c E rho u (p.actionTime r) m J contested →
      u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R →
      SA.proposalTime p.toParams l < SA.proposalTime p.toParams q →
      HonestProposal E rho (fgsaInterface p c) q Q → ExactService p c E rho q Q →
      OpeningEntry p c E rho r height → OpeningCovered p c E rho r Q →
      (∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) →
      (∃ i ev, afterTicksIdx rho (p.actionTime r) ≤ i ∧
        rho.events[i]? = some ev ∧ EffectiveEvent p c E rho i ∧
        ev.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ) ∨
      (∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
        ↑r * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
        SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
        height + 1 ≤ (heightView p X).h ∧
        (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
          (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) ∧
        (PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
          ExactService p c E rho s (eraseFG X) ∧
          SA.gateTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ)) := by
  intro u m J contested l q Q height hready hp hu hq hl _hQ _hservice hentry hcovered hrepair
  have hsync : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hsched := hrec.base.valid.toScheduleWellFormed
  let D := p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ
  rcases healing_promotion_event_split p c E rho hsched (p.actionTime r) D with
    ⟨i, ev, hi, hev, heff, htime, _⟩ | hquiet
  · exact Or.inl ⟨i, ev, hi, hev, heff, htime⟩
  have har : E.t_GST ≤ p.actionTime r := hsync.trans hp.1
  obtain ⟨_, s, X, hnew, hslot, hlo, hhi, hgate, _⟩ :=
    healing_promotion_gap_proposal E rho hrec r har hhor
  have ha := actionTime_periodW p r
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hats : p.actionTime r ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
  have hdD : SA.proposalTime p.toParams s + p.Δ ≤ D := by dsimp only [D]; linarith
  have hdhor : SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon := by
    change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _ at hgate
    linarith [p.deltaPos]
  have hpD : PhaseInterval p c E rho u (SA.proposalTime p.toParams s + p.Δ) m J contested := by
    apply healing_phase_extend_of_no_effective p c E rho hrec.toRecovery₂ mono crossing hp
      (by linarith [p.deltaPos]) hdhor
    intro j hj hjd
    apply hquiet j
      ((preIdx_le_afterTicksIdx E rho hsched (p.actionTime r)).2.trans hj)
    apply hjd.trans_le
    change (rho.events.filter (fun e =>
      decide (e.time ≤ SA.proposalTime p.toParams s + p.Δ))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ D))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      ((of_decide_eq_true he).trans hdD))
  have hpts : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested := by
    refine ⟨hp.1.trans hats, le_trans (by linarith [p.deltaPos]) hdhor, hp.2.2.1, ?_⟩
    intro i x hui hits hx
    apply hpD.2.2.2 i x hui _ hx
    apply hits.trans
    change (rho.events.filter (fun e => decide (e.time ≤ SA.proposalTime p.toParams s))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ SA.proposalTime p.toParams s + p.Δ))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      (by have := of_decide_eq_true he; linarith [p.deltaPos]))
  have huvote : u ≤ SA.voteTime p.toParams (r * p.R) := by
    have hqt : SA.proposalTime p.toParams q ≤ SA.proposalTime p.toParams (r * p.R) := by
      change 4 * p.Δ * (q : Time) ≤ 4 * p.Δ * ((r * p.R : Nat) : Time)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by linarith [p.deltaPos])
    change u ≤ SA.proposalTime p.toParams (r * p.R) + p.Δ
    linarith [p.deltaPos]
  have hh := healing_promotion_advance E rho hrec.toRecovery₂ hδ hbound perm rowsReceipt
    progressCoverage
    hfold faultQ honestQuorum hentry hcovered hready hpts huvote hlo hnew hslot
  have hreceipt := healing_promotion_first_receipt E rho hrec.toRecovery₂ crossing (services s) hnew
    (hp.1.trans hats)
    hready hpD
  refine Or.inr ⟨s, X, hnew, hslot, hlo, hhi, hh, hreceipt, ?_⟩
  intro hpgate
  refine ⟨healing_promotion_continuing_service E rho hrepair ?_ hnew hpgate, hgate⟩
  have hqts : SA.proposalTime p.toParams q ≤ SA.proposalTime p.toParams s :=
    (by
      have hqt : SA.proposalTime p.toParams q ≤ (r : Time) * P p := by
        change 4 * p.Δ * (q : Time) ≤ (r : Time) * (4 * (p.R : Time) * p.Δ)
        have hq' : (q : Time) ≤ (r : Time) * p.R := by exact_mod_cast hq
        nlinarith [p.deltaPos]
      linarith [p.deltaPos])
  exact hl.trans_le hqts

end AvailableChain.FGSA.Run
end
