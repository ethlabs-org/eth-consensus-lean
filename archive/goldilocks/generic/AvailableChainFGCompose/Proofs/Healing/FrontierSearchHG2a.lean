module

public import AvailableChainFGCompose.Proofs.Population.FrontierSearchHG2a

public import AvailableChainFGCompose.Proofs.Population.HolderBaseService

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : Prot.State → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))
variable (laws : FGHeightLaws Ef O.height)

/-- Blueprint 21:1695--1720; HG4-RISE F1/F2.
DC: SAME the capped entry and first-opening bounds fit the fixed HG.4 guard.
The epsF bound follows from the LivenessBoundW field. -/
theorem frontierSearch_hg2a_bound (hT : FGTimingLaws T) (G ΔF d a tU : Time)
    (hbound : LivenessBoundW T ΔF) (ha : a ≤ d + FGCompose.P T - 4 * T.delta)
    (hU : tU ≤ d - 6 * T.delta) :
    max (a + Γ T G - T.delta + epsF T ΔF)
      (tU + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ≤
        d + (2 * FGCompose.P T + Γ T G - 9 * T.delta) := by
  exact frontierSearch_hg2a_bound_core T hT G ΔF d a tU hbound ha hU

/-- Blueprint 21:1592--1640; HG4-RISE F1 STOP evidence.
DC: SAME the existing service budget is 5Δ after the terminal budget.
This identity does not give a larger horizon to the terminal task. -/
theorem frontierSearch_hg2a_gate_cost (G ΔF a tU : Time) :
    max (a + Γ T G + 4 * T.delta + epsF T ΔF)
      (tU + 2 * FGCompose.P T + Γ T G + 2 * T.delta) =
    max (a + Γ T G - T.delta + epsF T ΔF)
      (tU + 2 * FGCompose.P T + Γ T G - 3 * T.delta) + 5 * T.delta := by
  exact frontierSearch_hg2a_gate_cost_core T G ΔF a tU

omit [DecidableEq V] in
/-- Blueprint 21:1592--1640; HG4-RISE F1, slot component only.
DC: SAME reuse healing_promotion_age_gap. The rounded bound supplies the full
G window from the terminal guard. This produces an honest slot; it does not
assert promotion or receipt. -/
theorem frontierSearch_hg2a_gap (hT : FGTimingLaws T) {G ΔF : Time}
    (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (r : Nat) (U : FGBlock (Fin n)) (hgst : E.t_GST ≤ (r : Time) * FGCompose.P T)
    (hhor : max (T.action r + Γ T G - T.delta + epsF T ΔF)
      (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ≤ rho.horizon) :
    let U_F := max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta)
    U_F + G ≤ rho.horizon ∧
    ∃ s, U_F < T.proposal s ∧
      T.proposal s ≤ U_F + Γ T G ∧
      Gen.V2.Duty.HonestSlot rho I s ∧
      T.proposal s + T.delta ≤
        max (T.action r + Γ T G - T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ∧
      T.gate s ≤
        max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) := by
  exact frontierSearch_hg2a_gap_core T E rho I hT deltaF hdelta gap r U hgst hhor

include laws in
/-- ROOT-DIGEST W2b. Blueprint 21:1592–1640; S5 H2, route steps 1–8.
DC: SAME the saved seed supplies source transfer only through the proposal read,
here through its local service leaf. The strict cap supplies receipt through t_X+Δ
by the cap receipt leaf. A first rise before maturity is the left arm. -/
theorem frontier_hg2a_receipt (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    {Jst : Time} (hJst : E.t_GST ≤ Jst) (mono : FGRunOrderLaws E rho R)
    (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (erasePreceq : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
      FGBlock.Preceq A B)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (capReceipt : PromotionCapReceipt R E rho O T I)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    {u : Time} {i m r q : Nat} {Q : Block} {Qfg U : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hQ : HonestProposal E rho I q Q)
    (he : R.erase Qfg = Q) (hQm : (O.height Qfg).h = m)
    (hu : u ≤ T.proposal q) (hqr : q ≤ r * T.roundSlots) (hU : U = (O.height Qfg).T_h)
    (service : ∀ t, T.gate q ≤ t → t ≤ rho.horizon →
      (∀ k x, timeIdx rho u ≤ k → k ≤ timeIdx rho t → x ∈ rho.honest →
        (R.core (V2.D.Run.stateBefore E rho k x)).fg.h_max ≤ m) →
      FrontierLocalService R S E rho O T I D.heightPair q Q Qfg m t)
    (entryAgreement : ∀ x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (hstart : frontierAtIdx R E rho (i + 1) ≤ m)
    (hhor : max (T.action r + Γ T G - T.delta + epsF T ΔF)
      (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ≤ rho.horizon) :
    FrontierHG2aResult R E rho O T I G ΔF i m r U := by
  exact frontier_hg2a_receipt_holder R S O T E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows parentFG parentHeight validFor fold laws hT schedule faultWeight deltaF hdelta
    gap hJst mono keep eraseParent erasePreceq slotProposal read order signer capReceipt hδ hbound
    rowsReceipt progressCoverage hfold honestQuorum hready hQ he hQm hu hqr hU (fun t hg ht hc =>
    frontierLocalService_to_holder_core (service t hg ht hc)) entryAgreement sourceSlot
    ancestorSlot hstart hhor

end AvailableChain.FGCompose
end
