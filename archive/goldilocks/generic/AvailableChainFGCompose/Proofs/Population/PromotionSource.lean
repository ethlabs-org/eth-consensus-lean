module
public import AvailableChainFGCompose.Statements.FrontierMaturity
public import AvailableChainFGCompose.Statements.Population.FrontierMaturity
public import AvailableChainFGCompose.Statements.Population.Seats
public import AvailableChainFGCompose.Proofs.Healing.PromotionRows
public import AvailableChainFGCompose.Proofs.Healing.PromotionArithmetic

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
/-- ROOT-DIGEST W2b. Blueprint 21:1592–1638; S5 H1, route step 6.
DC: SAME progress uses the fixed rows and source path at the proposal read.
The batch is built from the proposal read, the stored row order and the row
signer leaves. The core has no phase, permanence, repair, or service premise. -/
theorem promotion_age_advance_of_source_holder
    {A : Finset (Fin n)} (hA : A ⊆ FGHonestSeats S rho) (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    {deltaT r height : Nat} {U X : FGBlock (Fin n)} {s : Slot}
    (src : PromotionSourceAtFG R S E rho O T I D A ΔF r height U s X)
    (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : Ef.q ≤ Ef.weightOf A)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D) :
    height + 1 ≤ (O.height X).h := by
  classical
  obtain ⟨hU, hUP, hnew, hslot, hstart, hc, hage, hhor, hrows⟩ := src
  have hF : 0 ≤ ΔF := by
    rw [hdelta] at deltaF
    linarith [hT.delta_pos]
  obtain ⟨_, _, _, hdeadline, _, hafter⟩ :=
    healing_promotion_row_deadline T hT E hF hbound (rSent := r) le_rfl hstart hc
  have hmature : U.slot + deltaT ≤ X.slot := by
    rw [hslot]
    exact healing_promotion_maturity T hT hδ hage
  have hX : X ≠ .genesis := by
    intro he
    have ht := hnew.1.1
    rw [← hslot, he] at ht
    cases ht
  apply hfold height U X hX hU hUP ?_ hmature
  intro hpar
  obtain ⟨⟨rows, hcar, hrowsEq⟩, nd, hread, hparent, hfh, hft, hph, hv⟩ := read s X hnew hslot
  refine progressCoverage r height U X ?_ hpar
  refine ⟨schedule, faultWeight, deltaF, rowsReceipt, ?_, ?_, ?_, ?_, hU, hUP, ?_⟩
  · rw [hslot]
    exact ⟨hdeadline, hhor⟩
  · rw [hslot]
    exact ⟨rows, hcar, hrowsEq⟩
  · rw [hslot]
    exact hafter
  · have hQh : ∀ i ∈ A, safetyHolder S rho i ∈ rho.honest := by
      intro i hi
      exact (Finset.mem_filter.mp (hA hi)).2
    refine ⟨A, hQh, honestQuorum, ?_⟩
    intro i hi
    obtain ⟨j, rSent, a, hr, hrow, hn⟩ := hrows i hi
    obtain ⟨b, hb⟩ := signer.1 j _ rSent a hrow
    have hvalid := p0d3_same_row R S E rho O.height I D.heightPair parentFG parentHeight
      validFor fold Ef laws hslot hU hUP hpar hread hparent ⟨hfh, hft⟩ hph
      ⟨b, hb, (D.decode_height a b hb).symm⟩ hn (hv a)
    refine ⟨j, rSent, a, T.action rSent, hr, hrow, signer.2 i j rSent a hrow, hn, ?_, rfl,
      hvalid.1, hvalid.2⟩
    change rho.events[j]?.map V2.Event.time = some (T.action rSent)
    rw [hrow.2.1]
    rfl
  · intro i _ W hW hn
    exact order s X height U hnew hslot hpar hUP i W hW hn

end AvailableChain.FGCompose
end
