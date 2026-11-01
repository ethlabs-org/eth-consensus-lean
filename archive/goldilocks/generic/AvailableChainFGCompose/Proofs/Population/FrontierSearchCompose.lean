module
public import AvailableChainFGCompose.Proofs.Population.HolderBaseCompose
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchGap
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchTop

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
variable (Jst : Time) (leaseSlots : Nat)
variable (obs : FGObservationLaws R O) (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, finite phase composition.
DC: SAME gap and top J cannot repeat. A saved seed leaves the supplied tail budget.
Every phase result comes from its d5c consumer. The repair allowance at each actual
start after `Jst + 2P` is a leaf (FG-SA proves it for ρΓ and the guarded ρ₁). -/
theorem frontierSearch_phase_tail_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    (crossing : RXing R E rho O) (schedule : V2.D.ScheduleWellFormed E rho)
    (mono : FGRunOrderLaws E rho R)
    (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (joinedTick : ∀ iy y t, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y t) → t ≤ rho.horizon →
      E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
      joined (Prot.clock (rho.stateBefore E iy y) t) = true)
    (readyCut : ∀ t, Jst ≤ t → E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
    (hServices : ∀ i (ev : V2.Event V Prot.Object) m,
      rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
      frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
      PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
    (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
      W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF ρbar : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
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
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
      FGBlock.Preceq A B)
    (floor : AttemptProposalFloor R E rho O T I Jst)
    (gateCopy : ∀ u v m J contested q Q, Jst ≤ u →
      PhaseInterval R E rho O u v m J contested →
      FrontierSeedQualification T leaseSlots E.t_GST u q → T.gate q ≤ v →
      HonestProposal E rho I q Q → ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧
        i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF ∧ R.erase Qfg = Q)
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCoveredFG R S E rho O.height T D.heightPair (FGHonestSeats S rho) r Q ∧
      ((O.height Qfg).h = m - 1 → OpeningEntry R E rho O.height T r (m - 1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
          (O.height K).h = m))
    (heldSlot : ∀ i x A K, K ∈ (R.core (rho.stateBefore E i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot)
    (proposalSlot : ∀ q Q K, HonestProposal E rho I q Q → R.erase K = Q → K.slot = q)
    (justifiedSource : ∀ i x, x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ HonestRowAt S E rho T j y r a ∧
        actionSourceFG R E rho T y r = some (some K) ∧
        (O.height K).T_h = (R.core (rho.stateBefore E i x)).fg.J)
    (parentFrame : ∀ q Q, HonestProposal E rho I q Q → ∃ j,
      rho.events[j]? = some (.tick (V2.D.proposerOf rho I q) (T.proposal q)) ∧
      ∀ Qfg, R.erase Qfg = Q → FGBlock.Preceq
        (O.controls (rho.stateBefore E j (V2.D.proposerOf rho I q))).Z Qfg.parent)
    (allowance : ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
      Jst + 2 * FGCompose.P T ≤ ev.time →
      FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta))
    (tail : Time) (htail : 0 ≤ tail)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hdelay : Jst + 2 * FGCompose.P T ≤ ev.time)
    (hhor : ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (ev.time + frontierSearch_remaining T G ΔF ρbar tail kind) ∨
    ∃ t, ev.time ≤ t ∧ t + tail ≤ ev.time + frontierSearch_remaining T G ΔF ρbar tail kind ∧
      StrongServedFG R S E rho O T I D.heightPair Jst leaseSlots m t := by
  refine frontierSearch_phase_compose_core (R := R) (O := O) (T := T) (E := E) (rho := rho)
    (Ef := Ef) (Jst := Jst) (obs := obs) (cert := cert) (inv := inv) (justif := justif)
    (keep := keep) hT crossing schedule mono
    (StrongServedFG R S E rho O T I D.heightPair Jst leaseSlots) hG
    (allowance i ev m kind hstart hdelay).1 htail ?_ hstart hdelay hhor
  intro i ev m kind hst hdl hph
  have hal := allowance i ev m kind hst hdl
  have res : FrontierHG3ResultFG R S E rho O T I D.heightPair Jst leaseSlots i m ev.time
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) := by
    cases kind with
    | gap =>
      exact frontier_hg3_gap_holder (R := R) (S := S) (O := O) (T := T) (E := E) (rho := rho)
        (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
        (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
        (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
        (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots) (obs := obs) (cert := cert)
        (inv := inv) (justif := justif) (keep := keep) (positive := positive)
        (coreLaws := coreLaws) (erasePreceq := erasePreceq) (joined := joined)
        (receipt := receipt) hT hk crossing schedule mono awake joinedTick readyCut
        hServices receiptHeld faultWeight deltaF hdelta gap hJst hG slotProposal read
        order signer sourceParent hδ hbound rowsReceipt progressCoverage hfold
        honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect floor gateCopy
        service common heldSlot proposalSlot hst hal hph
    | topJ =>
      exact frontier_hg3_topJ_holder (R := R) (S := S) (O := O) (T := T) (E := E) (rho := rho)
        (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
        (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
        (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
        (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots) (obs := obs) (cert := cert)
        (inv := inv) (justif := justif) (keep := keep) (positive := positive)
        (coreLaws := coreLaws) (erasePreceq := erasePreceq) (joined := joined)
        (receipt := receipt) hT hk crossing schedule mono awake joinedTick readyCut
        hServices receiptHeld faultWeight deltaF hdelta gap hJst hG slotProposal read
        order signer sourceParent hδ hbound rowsReceipt progressCoverage hfold
        honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect floor gateCopy
        service common justifiedSource parentFrame hst hal hph
    | contest =>
      exact frontier_hg3_contest_holder (R := R) (S := S) (E := E) (rho := rho) (O := O) (T := T)
        (I := I) (pair := D.heightPair) (Jst := Jst) (leaseSlots := leaseSlots) (Ef := Ef)
        (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
        (positive := positive) (coreLaws := coreLaws) (erasePreceq := erasePreceq)
        (joined := joined) (receipt := receipt) hT hk crossing schedule mono hdelta hJst
        awake joinedTick readyCut hServices receiptHeld hG floor gateCopy service hst hal hph
  exact (FrontierHG3ResultFG_def R S E rho O T I D.heightPair Jst leaseSlots i m ev.time _).mp res

end AvailableChain.FGCompose
end
