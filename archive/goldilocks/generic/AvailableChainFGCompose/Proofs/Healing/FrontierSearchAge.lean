module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchAge

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

include laws in
/-- Blueprint 21 HG.3/HG.2. DC: SAME the actual source entry is an explicit
local branch input. The full G window and gate bound come from the caller's deadline.
The selected proposal reaches the entry height by the generic advance from its
source; the opening sources reach its parent by the source transfer leaf. -/
theorem frontierSearch_age_service (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    {Jst : Time} (hJst : E.t_GST ≤ Jst)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    {u D' : Time} {m height r : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {U : FGBlock (Fin n)}
    (hentry : OpeningEntry R E rho O.height T r height)
    (hcovered : OpeningCovered R S E rho O.height T D.heightPair r Q)
    (hsource : ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
      (O.height K).T_h = U)
    (entryAgreement : ∀ x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (hready : Jst ≤ u) (hstart : E.t_GST ≤ (r : Time) * FGCompose.P T)
    (hu : u ≤ T.vote (r * T.roundSlots))
    (hp : PhaseInterval R E rho O u D' m J contested)
    (hwin : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + G ≤ rho.horizon)
    (hbudget : max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
      (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) ≤ D') :
    ∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      T.action r < T.proposal s ∧ T.gate s ≤ D' ∧ height + 1 ≤ (O.height X).h := by
  classical
  obtain ⟨A, hA, hAQ⟩ := honestQuorum
  have hAh : A ⊆ FGHonestSeats S rho := by
    intro i hi
    simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hA i hi
  have hn : A.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he] at hAQ
    change Ef.q ≤ ∑ i ∈ (∅ : Finset (Fin n)), Ef.weight i at hAQ
    simp only [Finset.sum_empty] at hAQ
    omega
  exact frontierSearch_age_service_holder R S O T E rho I D Ef decodeProposal bodyErase
    bodyRows blockWireRows parentFG parentHeight validFor fold laws hAh hn hT schedule
    faultWeight deltaF hdelta gap hJst slotProposal read order signer sourceParent hδ hbound
    rowsReceipt progressCoverage hfold hAQ hentry (fun i hi => hcovered _ (hA i hi)) hsource
    entryAgreement sourceSlot ancestorSlot hready hstart hu hp hwin hbudget

end AvailableChain.FGCompose
end
