module
public import AvailableChainFGSAProofs.Proofs.Healing.LiveDC -- shake: keep (LIVE-DC service)
public import AvailableChainFGSAClaims.Claims.Healing
public import AvailableChainFGSAProofs.Proofs.Healing.Reset -- shake: keep (H.11 reset supplier)
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionRenewed
public import AvailableChainFGSAProofs.Proofs.Healing.RecoveryPerm -- shake: keep (TPerm supplier)
public import AvailableChainFGSAProofs.Proofs.Healing.Attempt -- shake: keep (H.10 supplier)
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchFull
-- shake: keep (HG.5 supplier)
public import AvailableChainFGSAProofs.Proofs.Healing.HealingInputExport
-- shake: keep (J11)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetHealed -- shake: keep (J7)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJointStep -- shake: keep (J6-3)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetJointStep2 -- shake: keep (HTW-3)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetTHigh -- shake: keep (THigh)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetH2Prime -- shake: keep (H2P)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCone -- shake: keep (cone step)
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetRawStep -- shake: keep (HCLOSE steps)

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- Blueprint 21:1356–1425. The suppliers keep the renewed promotion ports.
The claim supplies recovery, the liveness bound, and the gate horizon.
Assembly must discharge every supplier port of these composition wrappers.
DC: SAME fixed action, effective-event alternative, and three deadlines. -/
theorem healing_renewedPromotionClaim_of
    (hmono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RMonoAll p c E rho)
    (hproposalServices : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      RecoverySleep₂ p c E rho G ΔF →
      ∀ s ip x (N : NamedProposal p.n), x ∈ rho.honest →
      rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)) →
      (ofWire p ⟨.proposer s, .proposal N⟩) ∈ rho.emitsAt E ip →
      E.t_GST ≤ SA.proposalTime p.toParams s →
      SA.proposalTime p.toParams s + p.Δ ≤ rho.horizon →
      Block.Compatible N.erase (eraseFG (rho.stateBeforeTime E
        (SA.proposalTime p.toParams s + p.Δ) x).st.fg.F) →
      Nonempty (ReceiverService E rho (ofWire p ⟨.proposer s, .proposal N⟩)
        (SA.proposalTime p.toParams s) (SA.proposalTime p.toParams s + p.Δ) x))
    (hcrossing : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      Recovery₂ p c E rho G ΔF → RXing p c E rho)
    (hperm : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      RecoverySleep₂ p c E rho G ΔF → TPerm p c E rho)
    (hrowsReceipt : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      Recovery₂ p c E rho G ΔF → TRowsReceipt p c E rho ΔF)
    (hprogressCoverage : ∀ ΔF, BatchCoverage p ΔF .progress)
    (hfold : foldTrichotomy p .progress)
    (hfaultQ : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      Recovery₂ p c E rho G ΔF → Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (hhonestQuorum : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time},
      Recovery₂ p c E rho G ΔF → p.E.q ≤ p.E.weightOf (honestSeats p c rho)) :
    RenewedPromotionClaim p := by
  intro G ΔF hδ V _ _ In c E rho pt h
  exact healing_renewedPromotion E rho h.set (hproposalServices c E rho h.set) hδ h.bound
    (hmono c E rho) (hcrossing c E rho h.set.toRecovery₂) (hperm c E rho h.set)
    (hrowsReceipt c E rho h.set.toRecovery₂) (hprogressCoverage ΔF c E rho)
    hfold (hfaultQ c E rho h.set.toRecovery₂) (hhonestQuorum c E rho h.set.toRecovery₂) pt.r h.hhor

/-- Blueprint 21:1120–1137 and SO-COV. The supplier keeps the local
earlier-or-current row conclusion. HealingPrem supplies Base₂, the fault
bound, and awake status within the phase horizon.
DC: SAME source height and named root; no new permission premise. -/
theorem healing_rowPermissionClaim_of
    (hcovered : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      Base₂ p c E rho → (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3 →
      ∀ (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root)) :
    RowPermissionClaim p := by
  intro G ΔF _hδ V _ _ In c E rho pt h u v m J contested r x C nd
    hGST hphase hu hv hx hnd hsrc hC hlo _
  exact hcovered c E rho h.set.base h.set.fault x hx r nd hnd C hsrc hC hlo
    (h.set.awake x hx _ (hGST.trans hu) (hv.trans hphase.2.1))

end AvailableChain.FGSA.Run
end
