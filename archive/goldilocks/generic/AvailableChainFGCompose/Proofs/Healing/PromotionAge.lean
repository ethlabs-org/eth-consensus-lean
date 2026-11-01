module

public import AvailableChainFGCompose.Proofs.Population.PromotionAge

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

/-- Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME the strict age trigger gives the carrier and maturity grid bounds. -/
theorem promotion_age_grid (hT : FGTimingLaws T) (r s : Nat) (U : FGBlock (Fin n))
    (ΔF : Time)
    (hlo : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) < T.proposal s) :
    carrierTimeW T ΔF r ≤ T.proposal s ∧
    T.proposal U.slot + 2 * FGCompose.P T ≤ T.proposal s := by
  exact promotion_age_grid_core T hT r s U ΔF hlo

include laws in
/-- Blueprint 21:1592–1638; S5 H1, receipt half of persistent-phase HG.2.
DC: SAME the receipt half ends at t_X+Δ and uses the terminal budget.
The opening sources reach the new parent by the source transfer leaf; the
selected receiver processes it by the phase receipt leaf. -/
theorem healing_promotion_age_receipt (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    {Jst : Time} (hJst : E.t_GST ≤ Jst) (hne : rho.honest.Nonempty)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    (receipt : PromotionPhaseReceipt R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {r height : Nat} {Q : Block}
    (hentry : OpeningEntry R E rho O.height T r height)
    (hcovered : OpeningCovered R S E rho O.height T D.heightPair r Q)
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
    (hu : u ≤ T.vote (r * T.roundSlots)) :
    ∃ U : FGBlock (Fin n), EntryAt O.height U height ∧ U.slot ≤ r * T.roundSlots ∧
      ∀ v, PhaseInterval R E rho O u v m J contested →
        max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
          (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + G ≤ rho.horizon →
        max (T.action r + Γ T G - T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ≤ v →
        let U_F := max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
          (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta)
        ∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
          U_F < T.proposal s ∧ T.proposal s ≤ U_F + Γ T G ∧
          height + 1 ≤ (O.height X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y) ∧
          T.proposal s + T.delta ≤
            max (T.action r + Γ T G - T.delta + epsF T ΔF)
              (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) := by
  classical
  have _ := hne
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
    have hz : 0 ≤ Ef.weightOf (historyFaulty S rho) := Nat.zero_le _
    omega
  exact healing_promotion_age_receipt_holder R S O T E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows parentFG parentHeight validFor fold laws hAh hn hT schedule faultWeight deltaF
    hdelta gap hJst slotProposal read order signer sourceParent receipt hδ hbound rowsReceipt
    progressCoverage hfold hAQ hentry (fun i hi => hcovered _ (hA i hi)) entryAgreement sourceSlot
    ancestorSlot hready hstart hu (m := m) (J := J) (contested := contested)

/-- Blueprint 21:1592–1638; S5 H1, service tail of persistent-phase HG.2.
DC: SAME service alone uses repair continuation and the phase through the gate.
The gate budget is the original HG.2b_F maximum. The protocol keeps its exact
service clauses; this generic tail returns the semantic proposal service. -/
theorem healing_promotion_age_service_tail (hT : FGTimingLaws T)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    {u : Time} {m r : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {l s : Slot} {U X : FGBlock (Fin n)}
    (hl : T.proposal l < (r : Time) * FGCompose.P T)
    (hrepair : ∀ v, PhaseInterval R E rho O u v m J contested → ∀ s Q,
      T.proposal l < T.proposal s → T.gate s ≤ v → HonestProposal E rho I s Q →
      FrontierProposalService R E rho T s Q)
    (hnew : HonestProposal E rho I s (R.erase X))
    (hlo : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
      (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) < T.proposal s)
    (hhi : T.proposal s ≤
      max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
        (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + Γ T G)
    (hpgate : PhaseInterval R E rho O u (T.gate s) m J contested) :
    FrontierProposalService R E rho T s (R.erase X) ∧
      T.gate s ≤
        max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) := by
  exact healing_promotion_age_service_tail_core R O T E rho I hT deltaF hdelta hl hrepair hnew hlo
    hhi hpgate

include laws in
/-- Blueprint 21:1592–1638; r3 A5, persistent-phase HG.2.
DC: SAME the age trigger uses q = U.slot for the actual fixed starting entry.
The full G window and a phase through the gate budget are explicit local
premises. First receipt remains strict and block delay remains Δ. -/
theorem healing_promotion_age_service (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    {Jst : Time} (hJst : E.t_GST ≤ Jst) (hne : rho.honest.Nonempty)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    (receipt : PromotionPhaseReceipt R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {r height : Nat} {l : Slot} {Q : Block}
    (hentry : OpeningEntry R E rho O.height T r height)
    (hcovered : OpeningCovered R S E rho O.height T D.heightPair r Q)
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
    (hl : T.proposal l < (r : Time) * FGCompose.P T)
    (hrepair : ∀ v, PhaseInterval R E rho O u v m J contested → ∀ s Q,
      T.proposal l < T.proposal s → T.gate s ≤ v → HonestProposal E rho I s Q →
      FrontierProposalService R E rho T s Q) :
    ∃ U : FGBlock (Fin n), EntryAt O.height U height ∧ U.slot ≤ r * T.roundSlots ∧
      ∀ v, PhaseInterval R E rho O u v m J contested →
        max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
          (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + G ≤ rho.horizon →
        max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
          (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) ≤ v →
        let U_F := max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
          (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta)
        ∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
          U_F < T.proposal s ∧ T.proposal s ≤ U_F + Γ T G ∧
          height + 1 ≤ (O.height X).h ∧
          (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
            (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y) ∧
          T.proposal s + T.delta ≤
            max (T.action r + Γ T G - T.delta + epsF T ΔF)
              (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ∧
          (PhaseInterval R E rho O u (T.gate s) m J contested →
            FrontierProposalService R E rho T s (R.erase X) ∧
            T.gate s ≤
              max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
                (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta)) := by
  classical
  have _ := hne
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
    have hz : 0 ≤ Ef.weightOf (historyFaulty S rho) := Nat.zero_le _
    omega
  exact healing_promotion_age_service_holder R S O T E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows parentFG parentHeight validFor fold laws hAh hn hT schedule faultWeight deltaF
    hdelta gap hJst slotProposal read order signer sourceParent receipt hδ hbound rowsReceipt
    progressCoverage hfold hAQ hentry (fun i hi => hcovered _ (hA i hi)) entryAgreement sourceSlot
    ancestorSlot hready hstart hu hl hrepair (m := m) (J := J) (contested := contested)

end AvailableChain.FGCompose
end
