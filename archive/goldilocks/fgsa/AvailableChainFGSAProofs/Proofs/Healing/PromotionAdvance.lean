module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionSource

public import AvailableChainFGSAProofs.Proofs.Healing.ResetScope

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Blueprint 21:1385–1410; r3 A3.
DC: SAME the fixed original rows give coverage only at unchanged parent height.
Assembly supplies rowsReceipt, progressCoverage, the honest-seat quorum and FaultQ.
No batch is built in the parent-already-crossed branch of hfold. -/
theorem healing_promotion_advance (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s) :
    height + 1 ≤ (heightView p X).h := by
  have hsync : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  have ha := actionTime_periodW p r
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hgate : p.actionTime r ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
  have hstart : E.t_GST ≤ p.actionTime r := hsync.trans (by
    have havote : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
      rw [actionTime_periodW]
      change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
        (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ
      push_cast
      nlinarith [p.deltaPos]
    exact hu.trans havote)
  have hc : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s := by
    rw [carrierTimeW_def]
    have := betaF_le_period p ΔF hbound
    linarith [p.deltaPos]
  obtain ⟨_, _, _, hdeadline, _, hafter⟩ :=
    healing_promotion_row_deadline E rho hrec hbound (rSent := r) le_rfl hstart hc
  have hhor : SA.proposalTime p.toParams s ≤ rho.horizon := hphase.2.1
  obtain ⟨U, hU, hUslot, hUP, hrows⟩ := healing_promotion_same_rows E rho hrec perm
    hentry hcovered hready hphase hu hgate hafter hnew hslot
  apply promotion_age_advance_of_source E rho hrec (r := r) (s := s) (U := U)
    ?_ hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum
  refine ⟨hU, hUP, hnew, hslot, hstart, hc, ?_, hhor, ?_⟩
  · have hscale : SA.proposalTime p.toParams U.slot ≤ (r : Time) * P p := by
      have hi : (U.slot : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hUslot
      change 4 * p.Δ * (U.slot : Time) ≤ (r : Time) * (4 * (p.R : Time) * p.Δ)
      have h := mul_le_mul_of_nonneg_left hi (by linarith [p.deltaPos] : 0 ≤ 4 * p.Δ)
      push_cast at h
      nlinarith
    linarith
  · intro x hx
    obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, hn, _⟩ := hrows x hx
    exact ⟨j, rSent, a, hr, ha, hn⟩

/-- The promotion consumer uses the selected sources at its actual proposal read. -/
theorem healing_promotion_advance_on (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (hδ : p.δt = 2 * p.R) (hbound : LivenessBoundW p ΔF)
    (rowsReceipt : ∀ j y r (a : RowWire p.n), HonestRowAt p c E rho j y r a →
      max (p.actionTime r) E.t_GST + ΔF ≤ rho.horizon →
      ∀ x ∈ rho.honest, HeldBefore p c E rho x a (max (p.actionTime r) E.t_GST + ΔF))
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin p.n)),
      BatchPrem p c E rho ΔF .progress r height U X →
      (heightView p X.parent).h = height → CoveredByChild p .progress X U height)
    (hfold : foldTrichotomy p .progress)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (honestQuorum : p.E.q ≤ p.E.weightOf (honestSeats p c rho))
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {r height : Nat} {s : Slot} {Q : Block} {X : FGBlock (Fin p.n)}
    (hentry : OpeningEntry p c E rho r height) (hcovered : OpeningCovered p c E rho r Q)
    (hready : recoveryStart p E ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hnew : HonestProposal E rho (fgsaInterface p c) s (eraseFG X)) (hslot : X.slot = s)
    (hParents : ∀ x ∈ rho.honest, ∀ K,
      actionSourceFG p c E rho x r = some (some K) →
      Block.Preceq (eraseFG K) (eraseFG X).parent) :
    height + 1 ≤ (heightView p X).h := by
  have hsync : E.t_GST ≤ u := by
    have := healing_recovery_start_lower (p := p) E
    linarith [p.deltaPos]
  classical
  have ha := actionTime_periodW p r
  have hR : (2 : Time) ≤ p.R := by exact_mod_cast p.RLarge
  have hP : 8 * p.Δ ≤ P p := by
    change 8 * p.Δ ≤ 4 * (p.R : Time) * p.Δ
    nlinarith [p.deltaPos]
  have hgate : p.actionTime r ≤ SA.proposalTime p.toParams s := by linarith [p.deltaPos]
  have hstart : E.t_GST ≤ p.actionTime r := hsync.trans (by
    have havote : SA.voteTime p.toParams (r * p.R) ≤ p.actionTime r := by
      rw [actionTime_periodW]
      change 4 * p.Δ * ((r * p.R : Nat) : Time) + p.Δ ≤
        (r : Time) * (4 * (p.R : Time) * p.Δ) + 6 * p.Δ
      push_cast
      nlinarith [p.deltaPos]
    exact hu.trans havote)
  have hc : carrierTimeW p ΔF r ≤ SA.proposalTime p.toParams s := by
    rw [carrierTimeW_def]
    have := betaF_le_period p ΔF hbound
    linarith [p.deltaPos]
  obtain ⟨_, _, _, hdeadline, _, hafter⟩ :=
    healing_promotion_row_deadline E rho hrec hbound (rSent := r) le_rfl hstart hc
  have hhor : SA.proposalTime p.toParams s ≤ rho.horizon := hphase.2.1
  obtain ⟨U, hU, hUslot, hUP, hrows⟩ := healing_promotion_same_rows_on E rho hrec
    hentry hcovered hready hphase hu hgate hafter hnew hslot hParents
  apply promotion_age_advance_of_source E rho hrec (r := r) (s := s) (U := U)
    ?_ hδ hbound rowsReceipt progressCoverage hfold faultQ honestQuorum
  refine ⟨hU, hUP, hnew, hslot, hstart, hc, ?_, hhor, ?_⟩
  · have hscale : SA.proposalTime p.toParams U.slot ≤ (r : Time) * P p := by
      have hi : (U.slot : Time) ≤ ((r * p.R : Nat) : Time) := by exact_mod_cast hUslot
      change 4 * p.Δ * (U.slot : Time) ≤ (r : Time) * (4 * (p.R : Time) * p.Δ)
      have h := mul_le_mul_of_nonneg_left hi (by linarith [p.deltaPos] : 0 ≤ 4 * p.Δ)
      push_cast at h
      nlinarith
    linarith
  · intro x hx
    obtain ⟨K, nd, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, hn, _⟩ := hrows x hx
    exact ⟨j, rSent, a, hr, ha, hn⟩

end AvailableChain.FGSA.Run
end
