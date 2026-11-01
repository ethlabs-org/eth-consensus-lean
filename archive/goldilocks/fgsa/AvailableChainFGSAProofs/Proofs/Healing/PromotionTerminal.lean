module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRenewed
-- shake: keep (terminal promotion suppliers)

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

private theorem promotion_terminal_grid_upper (p : Params) (G z : Time) (s : Slot)
    (hs : SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + G) :
    SA.proposalTime p.toParams s ≤ 4 * p.Δ * z + Γ p G := by
  linarith [(fgsa_gamma_bounds p G).1]

private theorem promotion_terminal_gap_aligned (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (haligned : Γ p G = G)
    (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ rho.horizon) :
    (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon ∧
    ∃ s, (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.gateTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ := by
  have hclass0 : G = Γ p G := haligned.symm
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ; nlinarith [p.deltaPos]
  have ha := actionTime_periodW p r
  have hwindow : (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon := by
    rw [hclass0]
    linarith [p.deltaPos]
  have hstart : E.t_GST ≤ (r : Time) * P p + 2 * P p - 4 * p.Δ := by
    linarith [p.deltaPos]
  obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap _ hstart hwindow
  rw [proposalTime_fgsa] at hlo hhi
  have hgrid : (r : Time) * P p + 2 * P p - 4 * p.Δ =
      4 * p.Δ * ((r : Time) * p.R + 2 * p.R - 1) := by
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      2 * (4 * (p.R : Time) * p.Δ) - 4 * p.Δ = _
    ring
  have hup := promotion_terminal_grid_upper p G ((r : Time) * p.R + 2 * p.R - 1) s
    (by rw [← hgrid]; exact hhi)
  rw [← hgrid] at hup
  have hlow : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s := by
    rw [hgrid] at hlo
    change 4 * p.Δ * ((r : Time) * p.R + 2 * p.R - 1) < 4 * p.Δ * (s : Time) at hlo
    have hc : (r : Time) * p.R + 2 * p.R ≤ s := by
      have := p.deltaPos
      have : (r : Time) * p.R + 2 * p.R - 1 < s := by nlinarith
      linarith only [Int.add_one_le_iff.mpr this]
    change (r : Time) * (4 * (p.R : Time) * p.Δ) +
      2 * (4 * (p.R : Time) * p.Δ) ≤ 4 * p.Δ * (s : Time)
    nlinarith [p.deltaPos]
  refine ⟨hwindow, s, hlow, by linarith, hs, ?_⟩
  change SA.proposalTime p.toParams s + 6 * p.Δ ≤ _
  linarith

private theorem promotion_terminal_gap (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ rho.horizon) :
    (r : Time) * P p + 2 * P p - 4 * p.Δ + G ≤ rho.horizon ∧
    ∃ s, (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s ∧
      SA.gateTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ := by
  have hle := (fgsa_gamma_bounds p G).1
  have hround : Recovery₂ p c E rho (Γ p G) ΔF := by
    refine ⟨hrec.sync, hrec.deltaF, ?_, hrec.base, hrec.fault, hrec.awake,
      hrec.gapPos.trans hle⟩
    intro t hstart hhor
    obtain ⟨s, hlo, hhi, hs⟩ := hrec.gap t hstart (by linarith)
    exact ⟨s, hlo, by linarith, hs⟩
  have h := promotion_terminal_gap_aligned E rho hround (fgsa_gamma_idem p G) r hgst
    (by simpa only [fgsa_gamma_idem] using hhor)
  rw [fgsa_gamma_idem] at h
  exact ⟨by linarith [h.1, (fgsa_gamma_bounds p G).1], h.2⟩

/-- Blueprint 21 H.10:1356–1419; plan item S5 PA-ASSEMBLY N(1).
DC: INTENTIONAL the terminal horizon supplies promotion and the strict first
receipt. The private rounded recurrence supplies alignment. Assembly supplies RMonoAll, RXing,
TPerm, the progress fold, and the standing INLINE row/coverage/quorum facts. -/
theorem healing_renewedPromotion_terminal (E : Generic.Env V)
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
    (r : Nat)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ ≤ rho.horizon) :
    ∀ u m J contested q Q height,
      recoveryStart p E ≤ u → PhaseInterval p c E rho u (p.actionTime r) m J contested →
      u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R →
      OpeningEntry p c E rho r height → OpeningCovered p c E rho r Q →
      (∃ i ev, afterTicksIdx rho (p.actionTime r) ≤ i ∧
        rho.events[i]? = some ev ∧ EffectiveEvent p c E rho i ∧
        ev.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ) ∨
      (∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
        ↑r * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
        SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
        height + 1 ≤ (heightView p X).h ∧
        (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
          (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y)) := by
  intro u m J contested q Q height hready hp hu hq hentry hcovered
  have hsync : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  have hsched := hrec.base.valid.toScheduleWellFormed
  let D := p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ
  rcases healing_promotion_event_split p c E rho hsched (p.actionTime r) D with
    ⟨i, ev, hi, hev, heff, htime, _⟩ | hquiet
  · exact Or.inl ⟨i, ev, hi, hev, heff, htime⟩
  have har : E.t_GST ≤ p.actionTime r := hsync.trans hp.1
  obtain ⟨_, s, hlo, hhi, hslot0, _hgate⟩ :=
    promotion_terminal_gap E rho hrec.toRecovery₂ r har hhor
  have hproposalHor : SA.proposalTime p.toParams s ≤ rho.horizon := by
    linarith [p.deltaPos]
  have hproposalGST : E.t_GST ≤ SA.proposalTime p.toParams s := by
    have ha := actionTime_periodW p r
    have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
    have hP : 8 * p.Δ ≤ P p := by
      change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
      nlinarith [p.deltaPos]
    linarith [p.deltaPos]
  have hcut : E.t_GST ≤ slotStartZ p ((s : Int) - 1) := by
    unfold slotStartZ
    have ha := actionTime_periodW p r
    have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
    have hP : 8 * p.Δ ≤ P p := by
      change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
      nlinarith [p.deltaPos]
    change (r : Time) * P p + 2 * P p ≤ 4 * p.Δ * (s : Int) at hlo
    nlinarith [p.deltaPos]
  have hjoin : ∀ w, 0 ≤ w → w ≤ SA.proposalTime p.toParams s →
      V2.Event.restart (V2.D.proposerOf rho (fgsaInterface p c) s) w ∈ rho.events →
      w ≤ slotStartZ p ((s : Int) - 1) := by
    intro w _ _ hw
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hw
    exact (healing_recovery_restart_bound E rho hrec hslot0.2 hk).trans hcut
  obtain ⟨X, hnew, hslot, _⟩ := healing_promotion_slot_proposal E rho hrec.toRecovery₂ hslot0
    hproposalGST hproposalHor hjoin
  have ha := actionTime_periodW p r
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hats : p.actionTime r ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
  have hdD : SA.proposalTime p.toParams s + p.Δ ≤ D := by dsimp only [D]; linarith
  have hdhor : SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon := hdD.trans hhor
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
  exact Or.inr ⟨s, X, hnew, hslot, hlo, hhi, hh, hreceipt⟩

end AvailableChain.FGSA.Run
end
