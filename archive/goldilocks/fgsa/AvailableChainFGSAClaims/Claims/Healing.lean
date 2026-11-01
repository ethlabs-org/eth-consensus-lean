module
public import AvailableChainFGSAClaims.Statements.Packages.Healing
public import AvailableChainFGSAClaims.Statements.HealedBest

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- RowPermissionAt: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def RowPermissionAt {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ∀ u v m J contested r x C nd,
    E.t_GST ≤ u → PhaseInterval p c E rho u v m J contested →
    u ≤ p.actionTime r → p.actionTime r ≤ v → x ∈ rho.honest →
    postClock E rho x (p.actionTime r) = some nd →
    actionSourceFG p c E rho x r = some (some C) →
    C ∈ FGSA.fullTree p nd.st →
    (FGSA.controls p nd.st).lo ≤ (heightView p C).h → (heightView p C).h ≤ m →
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
      namedEntry a.payload.height_pair = some ((heightView p C).h, (heightView p C).T_h.root)

/-- RowPermissionClaim: chapter-21 service.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def RowPermissionClaim : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    HealingPrem p c G ΔF E rho pt → RowPermissionAt p c E rho

/-- HealingInputClaim: chapter-21 service.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def HealingInputClaim : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtW),
    HealingInputPrem p c G ΔF E rho pt → HealingInput p c E rho pt.w ΔF

/-- HTimeConcl: chapter-21 service.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def HTimeConcl {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) : Prop :=
  ∃ w, HealingInput p c E rho w ΔF ∧
    tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ ∧
    p.actionTime w.rStar + Γ p G + 4 * p.Δ < recoveryStart p E + B_HF p ΔF G

/-- HTimeClaim: chapter-21 service.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def HTimeClaim : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    HealingTimePrem p c G ΔF E rho pt → HTimeConcl p c E rho G ΔF

/-- ResetArrivalConcl: chapter-21 service.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def ResetArrivalConcl {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) : Prop :=
  ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar < recoveryStart p E + B'_resetF p ΔF G

/-- ResetArrivalClaim: chapter-21 service.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def ResetArrivalClaim : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    ResetArrivalPrem p c G ΔF E rho pt → ResetArrivalConcl p c E rho G ΔF

/-- RenewedPromotionConcl: chapter-21 service.
H.9(b), blueprint 21:1356–1425: keep coverage from the fixed action r
and the proposal, block-acceptance, and gate deadlines.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def RenewedPromotionConcl {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time) (r : Nat) : Prop :=
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
        SA.gateTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ))

/-- RenewedPromotionClaim: chapter-21 service.
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def RenewedPromotionClaim : Prop :=
  ∀ (G ΔF : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtR),
    RenewedPromotionPrem p c G ΔF E rho pt → RenewedPromotionConcl p c E rho G pt.r

/-- Best H-time (21:120–123, 3155–3158; 00:511, 521: B_best requires qualified search), P3 §4.6 D11.
This is a companion (user ruling after the re-freeze); ΔF port of the S4.6c text.
Use the healing and liveness premises of HealingTimePrem, with the B_bestF horizon.
Consumers: none (companion).
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def HTimeBestClaim : Prop :=
  ∀ (G ΔF : Time) (g : Nat), p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      Gen.Pure.FinForm.recS.holds (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
        p.R (P p) p.Δ (recoveryStart p E) rho.horizon g →
      recoveryStart p E + B_bestF p ΔF G g ≤ rho.horizon → HTimeBestConcl p c E rho G ΔF g

/-- Qualified-search H-time (21:120–123, 3155–3158; 00:511, 521), P3 §4.6 D50.
This is a companion (user ruling after the re-freeze); ΔF port of the S4.6c text.
The search domain requires 1 ≤ g (00:328, Rec_s).
Consumers: none (companion).
DC: INTENTIONAL family delivery uses ΔF; SA clocks stay unchanged. -/
def HTimeSearchClaim : Prop :=
  ∀ (G ΔF : Time) (g : Nat), p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      1 ≤ g → HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      Gen.Pure.QualSearch (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
        p.R (P p) p.Δ (recoveryStart p E) rho.horizon g →
      recoveryStart p E + B_bestF p ΔF G g ≤ rho.horizon → HTimeBestConcl p c E rho G ΔF g

end AvailableChain.FGSA.Run
end
