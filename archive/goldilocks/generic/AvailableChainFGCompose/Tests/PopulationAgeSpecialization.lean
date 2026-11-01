module
public import AvailableChainFGCompose.Proofs.Population.PromotionSource

set_option linter.privateModule false

public section

namespace AvailableChain.FGCompose.Tests.PopulationAgeSpecialization
open AvailableChain.FGCompose
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
/-- Conditional old-supplier specialization, not a concrete premise producer.
The frozen call recovers precisely the unchanged old age-advance conclusion. -/
private theorem frozen_advance_specialization (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    {deltaT r height : Nat} {U X : FGBlock (Fin n)} {s : Slot}
    (src : PromotionSourceAt R S E rho O T I D ΔF r height U s X)
    (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D) :
    height + 1 ≤ (O.height X).h := by
  obtain ⟨A, hAh, hAw⟩ := honestQuorum
  have hA : A ⊆ FGHonestSeats S rho := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAh i hi⟩
  have hsrc : PromotionSourceAtFG R S E rho O T I D A ΔF r height U s X :=
    ⟨src.entry, src.parentPath, src.proposal, src.slot, src.sync, src.carrier, src.age,
      src.horizon, fun i hi => src.rows _ (hAh i hi)⟩
  exact promotion_age_advance_of_source_holder R S O T E rho I D Ef decodeProposal bodyErase
    bodyRows blockWireRows parentFG parentHeight validFor fold laws hA hT schedule faultWeight
    deltaF hdelta hsrc hδ hbound rowsReceipt progressCoverage hfold hAw read order signer

#print axioms frozen_advance_specialization
end AvailableChain.FGCompose.Tests.PopulationAgeSpecialization
end
