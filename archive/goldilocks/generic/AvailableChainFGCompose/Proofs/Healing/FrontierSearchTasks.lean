module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchGap
public import AvailableChainFGCompose.Proofs.Healing.ResetCut

public import AvailableChainFGCompose.Proofs.Population.FrontierSearchTasks

public import AvailableChainFGCompose.Proofs.Population.HolderBaseService

public section

/-! Blueprint 21 HG.5/H.11:1722–1800; S5 F3. First rise, then the first height-M+1 row.
Each task composes the d5d-a phase tail with the d5c per-seed tail of the saved seed.
The saved seed's held copy and continuing local service come from the published
gate-copy and service leaves. The cut start reads the actual tick of an honest node. -/

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

/-- Blueprint 21:1722–1800; S5 F3, budget arithmetic.
DC: SAME each remaining phase sum fits its frozen total, with a nonnegative tail.
Allowance nonnegativity is an explicit input. -/
theorem frontierSearch_task_bounds (hT : FGTimingLaws T) {G ΔF ρbar : Time}
    (hG : 4 * T.delta ≤ G) (hbound : LivenessBoundW T ΔF) (hρ : 0 ≤ ρbar) (kind : PhaseKind) :
    frontierSearch_remaining T G ΔF ρbar (2 * FGCompose.P T + Γ T G - 9 * T.delta) kind ≤
        frontierSearchRiseBudget T G ΔF ρbar ∧
    frontierSearch_remaining T G ΔF ρbar (FGCompose.P T - 4 * T.delta) kind ≤
        frontierSearchRowBudget T G ΔF ρbar ∧
    0 ≤ 2 * FGCompose.P T + Γ T G - 9 * T.delta ∧ 0 ≤ FGCompose.P T - 4 * T.delta ∧
    0 ≤ frontierSearchRiseBudget T G ΔF ρbar ∧ 0 ≤ frontierSearchRowBudget T G ΔF ρbar := by
  exact frontierSearch_task_bounds_core T hT hG hbound hρ kind

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, first task.
DC: SAME HG.3 reaches a saved seed or advances phase; HG.4 finishes the rise. -/
theorem frontierSearch_rise_task (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
    (allowance : ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
      Jst + 2 * FGCompose.P T ≤ ev.time →
      FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta))
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (capReceipt : PromotionCapReceipt R E rho O T I)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hdelay : Jst + 2 * FGCompose.P T ≤ ev.time)
    (hhor : ev.time + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (ev.time + frontierSearchRiseBudget T G ΔF ρbar) := by
  exact frontierSearch_rise_task_holder R S O T E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows parentFG parentHeight validFor fold Jst leaseSlots obs cert inv justif keep
    positive coreLaws erasePreceq joined receipt hT hk crossing schedule mono awake joinedTick
    readyCut hServices receiptHeld faultWeight deltaF hdelta gap hJst hG slotProposal read order
    signer sourceParent hδ hbound rowsReceipt progressCoverage hfold honestQuorum entryAgreement
    sourceSlot ancestorSlot eraseReflect floor gateCopy (fun u v m J c q Q Qfg hr hQ he hh hs hseed
    hu hp hg ht hc => frontierLocalService_to_holder_core (service u v m J c q Q Qfg hr hQ he hh hs
    hseed hu hp hg ht hc)) (fun u m J c q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp => ⟨fun i hi
    => (common u m J c q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp).1 _ (Finset.mem_filter.mp
    hi).2, (common u m J c q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp).2⟩) heldSlot proposalSlot
    justifiedSource parentFrame allowance eraseParent capReceipt hstart hdelay hhor

include cert inv in
/-- Blueprint 21:1722–1800; S5 F3, row provenance.
DC: SAME a rise past m supplies an earlier real height-m row through RCap. -/
theorem frontierSearch_row_of_rise (hT : FGTimingLaws T)
    (hs : V2.D.ScheduleWellFormed E rho)
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    {i m : Nat} {Dl : Time} (hm : 1 ≤ m) (hrise : FrontierRiseBy R E rho i m Dl) :
    FirstHeightRowBy S E rho T D.heightPair m Dl := by
  exact frontierSearch_row_of_rise_core R S O T E rho D Ef cert inv chainRows hT hs cap hm hrise

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, second task.
DC: SAME HG.3 plus the HG.4 row tail keeps exact height m and the frozen row budget. -/
theorem frontierSearch_row_task (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
    (allowance : ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
      Jst + 2 * FGCompose.P T ≤ ev.time →
      FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta))
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hdelay : Jst + 2 * FGCompose.P T ≤ ev.time)
    (hhor : ev.time + frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon) :
    FirstHeightRowBy S E rho T D.heightPair m
      (ev.time + frontierSearchRowBudget T G ΔF ρbar) := by
  exact frontierSearch_row_task_holder R S O T E rho I D Ef decodeProposal bodyErase bodyRows
    blockWireRows parentFG parentHeight validFor fold Jst leaseSlots obs cert inv justif keep
    positive coreLaws erasePreceq joined receipt chainRows hT hk crossing schedule mono awake
    joinedTick readyCut hServices receiptHeld faultWeight deltaF hdelta gap hJst hG slotProposal
    read order signer sourceParent hδ hbound rowsReceipt progressCoverage hfold honestQuorum
    entryAgreement sourceSlot ancestorSlot eraseReflect floor gateCopy (fun u v m J c q Q Qfg hr hQ
    he hh hs hseed hu hp hg ht hc => frontierLocalService_to_holder_core (service u v m J c q Q Qfg
    hr hQ he hh hs hseed hu hp hg ht hc)) (fun u m J c q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp
    => ⟨fun i hi => (common u m J c q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp).1 _
    (Finset.mem_filter.mp hi).2, (common u m J c q Q Qfg r hr hQ he hs hseed hu hqr hfirst hp).2⟩)
    heldSlot proposalSlot justifiedSource parentFrame allowance cap hstart hdelay hhor

/-- Blueprint 21:1744–1800; S5 F3.
DC: SAME classify a frontier by its accepted evidence. -/
theorem frontierSearch_phase_exists (i m : Nat) :
    ∃ kind, AttemptPhaseAt R E rho O i m kind := by
  classical
  by_cases hc : ContestEvidence R E rho O i m
  · exact ⟨.contest, hc⟩
  · by_cases ht : TopEvidence R E rho i m
    · exact ⟨.topJ, ht, hc⟩
    · exact ⟨.gap, ht, hc⟩

include cert inv in
/-- Blueprint 21:1744–1800; S5 F3, inclusive cut.
DC: SAME an honest node ticks at the cut, and the last event at the cut time starts the
search at the honest frontier. The nonempty honest set and wakefulness are inputs. -/
theorem frontierSearch_cut_start (hT : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho)
    (hne : rho.honest.Nonempty)
    (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (hdelta : E.Δ = T.delta) (hJst : E.t_GST ≤ Jst)
    {rG M : Nat} {u₀ : Time} (hgst : Jst ≤ T.action rG)
    (hfirst : ∀ r, Jst ≤ T.action r → rG ≤ r)
    (hu₀ : u₀ = T.action (rG + 2)) (hdelay : Jst + 2 * FGCompose.P T ≤ u₀)
    (hM : M = honestFrontier R E rho u₀) (hhor : u₀ ≤ rho.horizon) :
    ∃ i ev kind, FrontierSearchStart R E rho O T Jst i ev M kind ∧
      ev.time = u₀ ∧ timeIdx rho u₀ = i + 1 := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hd := hT.delta_pos
  have hP := frontierSearch_period_bound T hT
  have hgrid : u₀ = ((4 * ((rG + 2) * T.roundSlots) + 6 : Nat) : Time) * E.Δ := by
    rw [hu₀, hT.action_eq, hT.gate_eq, hT.proposal_eq, hdelta]
    push_cast
    ring
  have hJ0 : Jst ≤ u₀ := by linarith
  have hnn : 0 ≤ u₀ := by
    rw [hgrid, hdelta]
    positivity
  have htick : V2.Event.tick x u₀ ∈ rho.events :=
    hs.tick_total x hx u₀ ⟨_, hgrid⟩ hnn hhor (awake x hx u₀ (hJst.trans hJ0) hhor)
  obtain ⟨i, ev, hi, ht, hidx⟩ :=
    (reset_inclusive_start_iff E rho hs u₀).mpr ⟨.tick x u₀, htick, rfl⟩
  have hfront : frontierAtIdx R E rho (i + 1) = M := by
    rw [← hidx]
    exact (hM.trans (reset_inclusive_frontier R E rho hs u₀)).symm
  have hm : 1 ≤ M := by
    obtain ⟨W, hW, hWh⟩ := healing_phase_frontier_witness (R := R) (E := E) (rho := rho)
      (O := O) (Ef := Ef) (cert := cert) (inv := inv) (i + 1) x
    have h1 := cert.height.one_le_h W
    have h2 := healing_phase_local_le_frontier (R := R) (E := E) (rho := rho) (i := i + 1) hx
    simp only [Height] at *
    omega
  obtain ⟨kind, hkind⟩ := frontierSearch_phase_exists R O E rho (i + 1) M
  exact ⟨i, ev, kind, (FrontierSearchStart_def R E rho O T Jst i ev M kind).mpr
    ⟨hi, ht ▸ hJ0, Or.inr ⟨rG, hgst, hfirst, ht.trans hu₀, ht ▸ hidx⟩, hfront, hm, hkind⟩,
    ht, hidx⟩

omit [DecidableEq V] in
/-- Blueprint 21:1744–1800; S5 F3.
DC: SAME event order also permits equal timestamps. -/
theorem frontierSearch_event_time_mono (hs : V2.D.ScheduleWellFormed E rho) {i j : Nat}
    {ev ev' : V2.Event V Prot.Object} (hi : rho.events[i]? = some ev)
    (hj : rho.events[j]? = some ev') (hij : i ≤ j) : ev.time ≤ ev'.time := by
  by_cases he : i = j
  · subst j
    have hev : ev = ev' := Option.some.inj (hi.symm.trans hj)
    exact hev ▸ le_rfl
  · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl (by omega)
    rw [hie, hje] at hk
    exact V2.D.Engine.time_le_of_key_le _ _ hk

end AvailableChain.FGCompose
end
