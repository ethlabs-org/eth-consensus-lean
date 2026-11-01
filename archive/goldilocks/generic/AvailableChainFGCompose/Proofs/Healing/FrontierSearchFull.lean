module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchFull

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3. The full search: HG.3, the capped HG.4 rise
and exact-height row provenance. One first row is selected before both allowances.
There is no search, reset or post-reset service premise. `frontierSearch_family` proves the
start-family companion statement. `frontierSearch` derives the landed statement from it
under `transfer` (see its docstring for the producer scope). -/

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

variable (chainRows : Prot.State → Block → List Wire)

private theorem popc_local_service_holder {q : Slot} {Q : Block}
    {Qfg : FGBlock (Fin n)} {m : Nat} {v : Time}
    (h : FrontierLocalService R S E rho O T I D.heightPair q Q Qfg m v) :
    FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m v := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro r hr ht
  obtain ⟨hc, rest⟩ := h.2.2.2.2 r hr ht
  exact ⟨fun i hi => hc _ (Finset.mem_filter.mp hi).2, rest⟩

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, the search for one allowance value.
DC: SAME rise from M, then first row at M+1. Both complete horizon guards are retained.
RCap supplies a skipped row; otherwise the event at M+1 starts the row task. The
allowance at every actual phase start is the premise of the companion statement; there
is no transfer from the cut. -/
theorem frontierSearch_family (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat}
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
      FrontierLocalService R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCovered R S E rho O.height T D.heightPair r Q ∧
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
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (capReceipt : PromotionCapReceipt R E rho O T I)
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    (hne : rho.honest.Nonempty)
    (ρbar : Time) :
    FrontierSearchFamilyStatement R S E rho O T I D.heightPair Jst leaseSlots deltaT G ΔF
      ρbar := by
  exact frontierSearch_family_holder (R := R) (S := S) (O := O)
      (T := T) (E := E) (rho := rho) (I := I) (D := D) (Ef := Ef)
      (decodeProposal := decodeProposal) (bodyErase := bodyErase) (bodyRows := bodyRows)
      (blockWireRows := blockWireRows) (parentFG := parentFG) (parentHeight := parentHeight)
      (validFor := validFor) (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots)
      (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
      (positive := positive) (coreLaws := coreLaws) (erasePreceq := erasePreceq)
      (joined := joined) (receipt := receipt) (chainRows := chainRows)
    hT hk crossing schedule mono awake joinedTick readyCut hServices receiptHeld faultWeight
    deltaF hdelta gap hJst hG slotProposal read order signer sourceParent rowsReceipt
    progressCoverage hfold honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect
    floor gateCopy
    (fun u v m J contested q Q Qfg hr hQ he hh hs hseed hu hp hg hhor hcap =>
      popc_local_service_holder R S O T E rho I D
        (service u v m J contested q Q Qfg hr hQ he hh hs hseed hu hp hg hhor hcap))
    (fun u m J contested q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp => by
      obtain ⟨hc, rest⟩ := common u m J contested q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp
      exact ⟨fun i hi => hc _ (Finset.mem_filter.mp hi).2, rest⟩)
    heldSlot proposalSlot justifiedSource parentFrame eraseParent capReceipt cap hne ρbar

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, full FrontierSearchStatement (conditional form).
DC: SAME one first row is selected before both allowances. This theorem is derived from
`frontierSearch_family` and `transfer`. `transfer` carries EVERY allowance admitted at the
cut to every actual later start. It has a producer only for start-independent (canonical)
allowances; a protocol with canonical budgets uses `frontierSearch_family` directly. -/
theorem frontierSearch (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat}
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
      FrontierLocalService R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCovered R S E rho O.height T D.heightPair r Q ∧
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
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (capReceipt : PromotionCapReceipt R E rho O T I)
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    (hne : rho.honest.Nonempty)
    (transfer : ∀ rG ρbar, Jst ≤ T.action rG → (∀ r, Jst ≤ T.action r → rG ≤ r) →
      FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (T.action (rG + 2)) →
      ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
        Jst + 2 * FGCompose.P T ≤ ev.time →
        FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar
          (ev.time + 3 * T.delta)) :
    FrontierSearchStatement R S E rho O T I D.heightPair Jst leaseSlots deltaT G ΔF := by
  exact frontierSearch_holder (R := R) (S := S) (O := O)
      (T := T) (E := E) (rho := rho) (I := I) (D := D) (Ef := Ef)
      (decodeProposal := decodeProposal) (bodyErase := bodyErase) (bodyRows := bodyRows)
      (blockWireRows := blockWireRows) (parentFG := parentFG) (parentHeight := parentHeight)
      (validFor := validFor) (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots)
      (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
      (positive := positive) (coreLaws := coreLaws) (erasePreceq := erasePreceq)
      (joined := joined) (receipt := receipt) (chainRows := chainRows)
    hT hk crossing schedule mono awake joinedTick readyCut hServices receiptHeld faultWeight
    deltaF hdelta gap hJst hG slotProposal read order signer sourceParent rowsReceipt
    progressCoverage hfold honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect
    floor gateCopy
    (fun u v m J contested q Q Qfg hr hQ he hh hs hseed hu hp hg hhor hcap =>
      popc_local_service_holder R S O T E rho I D
        (service u v m J contested q Q Qfg hr hQ he hh hs hseed hu hp hg hhor hcap))
    (fun u m J contested q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp => by
      obtain ⟨hc, rest⟩ := common u m J contested q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp
      exact ⟨fun i hi => hc _ (Finset.mem_filter.mp hi).2, rest⟩)
    heldSlot proposalSlot justifiedSource parentFrame eraseParent capReceipt cap hne transfer

end AvailableChain.FGCompose
end
