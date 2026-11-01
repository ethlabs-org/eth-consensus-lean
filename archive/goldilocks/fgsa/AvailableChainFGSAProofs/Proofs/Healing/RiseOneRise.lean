module
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOneRepair
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOneAdvance
public import AvailableChainFGSAProofs.Proofs.Healing.RiseOneAccept

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1236–1237, 1317–1319, 1363–1370, 1467–1468; S5 M5b B3.
DC: SAME M1–M4 give a repaired height-one opening. The actual r3 gap proposal
consumes its mature progress quorum and has strict receipt by every honest
receiver, unless an effective event gives M1's rise first.
The terminal bound is rhoGamma + 3P + Gamma - 13Delta. The separate horizon
bound keeps r3's full window through rhoGamma + 3P + Gamma - 8Delta.
Assembly supplies only the existing M5 and exact r3 INLINE ports. -/
theorem healing_rise_one_rise (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho) (qc : RQCOrigin p c E rho)
    (services : RepairServiceScopes E rho)
    (opening : OpeningServiceScopes E rho)
    (proposalServices : ∀ s ip v (N : NamedProposal p.n) x,
      v ∈ rho.honest → x ∈ rho.honest →
      rho.events[ip]? = some (.tick v (SA.proposalTime p.toParams s)) →
      ofWire p ⟨.proposer s, .proposal N⟩ ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {u D : Time} (hready : recoveryStart p E ≤ u) (huD : u ≤ D) (hD : D ≤ rho.horizon)
    (hbudget : u + ρΓ p G + (P p - 4 * p.Δ) + (2 * P p + Γ p G - 9 * p.Δ) ≤ D)
    (hhor : u + ρΓ p G + (P p - 4 * p.Δ) +
      (2 * P p + Γ p G - 4 * p.Δ) ≤ rho.horizon) :
    RiseOneBy p c E rho D ∨
      ∃ r s X, p.actionTime r ≤ u + ρΓ p G + (P p - 4 * p.Δ) ∧
        HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
        (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
        SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
        2 ≤ (heightView p X).h ∧ SA.proposalTime p.toParams s + p.Δ ≤ D ∧
        ∀ x ∈ rho.honest, Gen.V2.Duty.HoldsBefore E rho
          (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) x := by
  have hGST : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  by_cases hrise : RiseOneBy p c E rho D
  · exact Or.inl hrise
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hΓ : 0 ≤ Γ p G := by
    have := (fgsa_gamma_bounds p G).1
    linarith [hrec.gapPos, p.deltaPos]
  have hopeningBudget : u + ρΓ p G + (P p - 4 * p.Δ) ≤ D := by
    linarith [p.deltaPos]
  rcases healing_rise_one_repair_opening E rho hrec mono crossing qc services opening
    writes rowCoverage
    hready huD hD hopeningBudget with hdone | hw
  · exact Or.inl hdone
  obtain ⟨β, q, Q, Qfg, r, hp, hβ, _hmin, _hrepair, hq, hgate, _hQ, _hexact,
    _heq, _hh, _he, hqr, _hfirst, _hrD, _h0, h1, hc, hentry⟩ := hw
  have har : p.actionTime r ≤ u + ρΓ p G + (P p - 4 * p.Δ) := by linarith
  have hβl : β ≤ β + 2 * p.k - 1 := by
    have hk : 1 ≤ 2 * p.k := by have := p.kLarge; omega
    exact Nat.le_sub_of_add_le (Nat.add_le_add_left hk β)
  have hβI : (β : Time) ≤ ((β + 2 * p.k - 1 : Nat) : Time) := by exact_mod_cast hβl
  have hβt : SA.proposalTime p.toParams β ≤
      SA.proposalTime p.toParams (β + 2 * p.k - 1) := by
    change 4 * p.Δ * (β : Time) ≤ 4 * p.Δ * ((β + 2 * p.k - 1 : Nat) : Time)
    nlinarith [p.deltaPos]
  have huq : u ≤ SA.proposalTime p.toParams q := hβ.le.trans (hβt.trans hq.le)
  have huvote : u ≤ SA.voteTime p.toParams (r * p.R) := by
    have hqt : SA.proposalTime p.toParams q ≤ SA.proposalTime p.toParams (r * p.R) := by
      change 4 * p.Δ * (q : Time) ≤ 4 * p.Δ * ((r * p.R : Nat) : Time)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqr) (by linarith [p.deltaPos])
    change u ≤ SA.proposalTime p.toParams (r * p.R) + p.Δ
    linarith [p.deltaPos]
  have hgstr : E.t_GST ≤ p.actionTime r := by
    have hav : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
      change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
        4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
      linarith [p.deltaPos]
    exact hGST.trans (huvote.trans hav)
  have hwindow : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon := by linarith
  obtain ⟨_, s, X, hnew, hslot, hlo, hhi, _hgate, _hcarrier⟩ :=
    healing_promotion_gap_proposal E rho hrec r hgstr hwindow
  have hd : SA.proposalTime p.toParams s + p.Δ ≤ D := by linarith
  have ha := actionTime_periodW p r
  have hafter : u ≤ SA.proposalTime p.toParams s := by
    have hav : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
      change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
        4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
      linarith [p.deltaPos]
    linarith [p.deltaPos]
  have hcut : timeIdx rho (SA.proposalTime p.toParams s) ≤ timeIdx rho D := by
    change (rho.events.filter (fun e => decide (e.time ≤ _))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ D))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      ((of_decide_eq_true he).trans (show SA.proposalTime p.toParams s ≤ D by
        linarith [p.deltaPos])))
  have hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) 1
      (some .genesis) false :=
    ⟨hafter, le_trans (by linarith [p.deltaPos]) hD, hp.2.2.1,
      fun i x hui hi hx => hp.2.2.2 i x hui (hi.trans hcut) hx⟩
  have hheight := healing_rise_one_advance E rho hrec hδ hbound mono crossing writes
    rowsReceipt progressCoverage hfold faultQ honestQuorum hentry hc hready hphase
    (services.permanence u (SA.proposalTime p.toParams s) 1
      (some .genesis) false hready hphase)
    huvote hlo hnew hslot
  rcases healing_rise_one_accept p c E rho hrec.toRecovery₂ mono crossing
    (proposalServices s) hnew hafter hready hd hD with
    hdone | hreceipt
  · exact Or.inl hdone
  exact Or.inr ⟨r, s, X, har, hnew, hslot, hlo, hhi, hheight, hd, hreceipt⟩

end AvailableChain.FGSA.Run
end
