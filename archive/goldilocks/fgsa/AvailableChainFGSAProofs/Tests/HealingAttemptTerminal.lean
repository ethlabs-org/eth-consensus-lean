module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionTerminal
-- shake: keep (terminal application and boundary tests)

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.HealingAttemptTerminal
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

-- Apply terminal promotion with only the terminal horizon.
example (E : Generic.Env V)
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
          (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y)) :=
  healing_renewedPromotion_terminal E rho hrec services hδ hbound mono crossing perm rowsReceipt
    progressCoverage hfold faultQ honestQuorum r hhor

-- The inclusive lower boundary is a real grid proposal and is mature.
example (p : Params) (hδ : p.δt = 2 * p.R) (r : Nat)
    (U : FGBlock (Fin p.n)) (hU : U.slot ≤ r * p.R) :
    SA.proposalTime p.toParams (r * p.R + 2 * p.R) =
      (r : Time) * P p + 2 * P p ∧ U.slot + p.δt ≤ r * p.R + 2 * p.R := by
  constructor
  · change 4 * p.Δ * ((r * p.R + 2 * p.R : Nat) : Time) =
      (r : Time) * (4 * (p.R : Time) * p.Δ) + 2 * (4 * (p.R : Time) * p.Δ)
    push_cast
    ring
  · rw [hδ]
    exact Nat.add_le_add_right hU _

end AvailableChain.FGSA.Run.Tests.HealingAttemptTerminal
end
