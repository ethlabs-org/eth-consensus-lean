module
public import AvailableChainFGCompose.Proofs.Population.HolderBaseTasks
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchCompose
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchRise

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

variable (chainRows : Prot.State → Block → List Wire)

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, first task.
DC: SAME HG.3 reaches a saved seed or advances phase; HG.4 finishes the rise. -/
theorem frontierSearch_rise_task_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (capReceipt : PromotionCapReceipt R E rho O T I)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hdelay : Jst + 2 * FGCompose.P T ≤ ev.time)
    (hhor : ev.time + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (ev.time + frontierSearchRiseBudget T G ΔF ρbar) := by
  obtain ⟨hb, _, ht, _, _, _⟩ := frontierSearch_task_bounds_core T hT hG hbound
    (allowance i ev m kind hstart hdelay).1 kind
  have hbudget : ev.time + frontierSearch_remaining T G ΔF ρbar
      (2 * FGCompose.P T + Γ T G - 9 * T.delta) kind ≤
      ev.time + frontierSearchRiseBudget T G ΔF ρbar := by
    linarith only [hb]
  rcases frontierSearch_phase_tail_holder (R := R) (S := S) (O := O) (T := T) (E := E) (rho := rho)
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
    service common heldSlot proposalSlot justifiedSource parentFrame allowance _ ht hstart hdelay
    (hbudget.trans hhor) with
      hr | ⟨t, _, htail, hserved⟩
  · exact frontierSearch_rise_mono R E rho hbudget hr
  · have hf := ((FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart).2.2.2.1
    obtain ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hQm, hsvc, hseed, hu, hp, hqt, _, _,
        _⟩ :=
      (StrongServedFG_def R S E rho O T I D.heightPair Jst leaseSlots m t).mp hserved
    obtain ⟨j, x, Qfg', _, _, _, hmem, he'⟩ :=
      gateCopy u (T.gate q) m J contested q Q hready hp hseed le_rfl hQ
    have hQQ : Qfg' = Qfg := coreLaws.erase_inj (he'.trans he.symm)
    exact frontierSearch_rise_mono R E rho (htail.trans hbudget)
      (healing_frontierTail_rise_of_seed_holder (R := R) (S := S) (O := O) (T := T)
        (E := E) (rho := rho)
        (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
        (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
        (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
        (fold := fold) (Jst := Jst) (cert := cert) (inv := inv) (keep := keep) hT schedule
        faultWeight deltaF hdelta gap
        hJst mono eraseParent eraseReflect slotProposal read order signer capReceipt hδ
        hbound rowsReceipt progressCoverage hfold honestQuorum entryAgreement sourceSlot
        ancestorSlot heldSlot proposalSlot hready hQ he hQm hu hqt ⟨j, x, hQQ ▸ hmem⟩
        (fun v hv hvh hc => service u v m J contested q Q Qfg hready hQ he hQm hsvc hseed
          hu hp hv hvh hc) hf.le ((htail.trans hbudget).trans hhor))

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, second task.
DC: SAME HG.3 plus the HG.4 row tail keeps exact height m and the frozen row budget. -/
theorem frontierSearch_row_task_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hdelay : Jst + 2 * FGCompose.P T ≤ ev.time)
    (hhor : ev.time + frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon) :
    FirstHeightRowBy S E rho T D.heightPair m
      (ev.time + frontierSearchRowBudget T G ΔF ρbar) := by
  classical
  have honestSeats : (FGHonestSeats S rho).Nonempty := by
    obtain ⟨A, hA, hq⟩ := honestQuorum
    have hne : A.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [he] at hq
      delta Electorate.weightOf at hq
      rw [Finset.sum_empty] at hq
      omega
    obtain ⟨seat, hs⟩ := hne
    refine ⟨seat, ?_⟩
    simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and]
      using hA seat hs
  obtain ⟨_, hb, _, ht, _, _⟩ := frontierSearch_task_bounds_core T hT hG hbound
    (allowance i ev m kind hstart hdelay).1 kind
  have hbudget : ev.time + frontierSearch_remaining T G ΔF ρbar
      (FGCompose.P T - 4 * T.delta) kind ≤
      ev.time + frontierSearchRowBudget T G ΔF ρbar := by
    linarith only [hb]
  rcases frontierSearch_phase_tail_holder (R := R) (S := S) (O := O) (T := T) (E := E) (rho := rho)
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
    service common heldSlot proposalSlot justifiedSource parentFrame allowance _ ht hstart hdelay
    (hbudget.trans hhor) with
      hr | ⟨t, _, htail, hserved⟩
  · have hm := ((FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart).2.2.2.2.1
    exact frontierSearch_row_of_rise_core (R := R) (S := S) (O := O) (T := T) (E := E)
      (rho := rho) (D := D) (Ef := Ef) (cert := cert) (inv := inv) (chainRows := chainRows)
      hT schedule cap hm (frontierSearch_rise_mono R E rho hbudget hr)
  · obtain ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hQm, hsvc, hseed, hu, hp, hqt, _, _,
        _⟩ :=
      (StrongServedFG_def R S E rho O T I D.heightPair Jst leaseSlots m t).mp hserved
    obtain ⟨r, hr, hfirst, htime⟩ :=
      (FirstHeightRowBy_def S E rho T D.heightPair m _).mp
        (healing_frontierTail_row_holder (R := R) (S := S) (E := E) (rho := rho) (O := O) (T := T)
          (I := I) (pair := D.heightPair) (chainRows := chainRows) (Ef := Ef) (cert := cert)
          (inv := inv) hT schedule honestSeats mono cap hp hQ hqt
          (fun v hv hvh hc => service u v m J contested q Q Qfg hready hQ he hQm hsvc hseed
            hu hp hv hvh hc) ((htail.trans hbudget).trans hhor))
    exact (FirstHeightRowBy_def S E rho T D.heightPair m _).mpr
      ⟨r, hr, hfirst, htime.trans (htail.trans hbudget)⟩

end AvailableChain.FGCompose
end
