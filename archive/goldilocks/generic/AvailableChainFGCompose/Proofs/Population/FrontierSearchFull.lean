module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchTasks
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchTasks

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
/-- Blueprint 21:1722–1800; S5 F3, the search for one allowance value.
DC: SAME rise from M, then first row at M+1. Both complete horizon guards are retained.
RCap supplies a skipped row; otherwise the event at M+1 starts the row task. The
allowance at every actual phase start is the premise of the companion statement; there
is no transfer from the cut. -/
theorem frontierSearch_family_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (capReceipt : PromotionCapReceipt R E rho O T I)
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    (hne : rho.honest.Nonempty)
    (ρbar : Time) :
    FrontierSearchFamilyStatement R S E rho O T I D.heightPair Jst leaseSlots deltaT G ΔF
      ρbar := by
  classical
  apply (FrontierSearchFamilyStatement_def R S E rho O T I D.heightPair Jst leaseSlots deltaT
    G ΔF ρbar).mpr
  intro hδ hbound hρ hall rG u₀ M hgst hfirst hu₀ hdelay hM _rowCap
  have rise : u₀ + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon →
      ∃ (j : Nat) (ev : V2.Event V Prot.Object), timeIdx rho u₀ ≤ j ∧
        rho.events[j]? = some ev ∧ u₀ ≤ ev.time ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
        M < frontierAtIdx R E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M) := by
    intro hhor
    have hb := (frontierSearch_task_bounds_core T hT hG hbound hρ .gap).2.2.2.2.1
    have hcutHor : u₀ ≤ rho.horizon := by linarith only [hhor, hb]
    obtain ⟨i, ev, kind, hstart, ht, hidx⟩ :=
      frontierSearch_cut_start (R := R) (O := O) (T := T) (E := E) (rho := rho) (Ef := Ef)
        (Jst := Jst) (cert := cert) (inv := inv) hT schedule hne awake hdelta hJst hgst
        hfirst hu₀ hdelay hM hcutHor
    have hrise := frontierSearch_rise_task_holder (R := R) (S := S) (O := O) (T := T)
        (E := E) (rho := rho)
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
        service common heldSlot proposalSlot justifiedSource parentFrame hall eraseParent
        capReceipt hstart
      (ht ▸ hdelay) (ht ▸ hhor)
    obtain ⟨j, nextEv, hij, hj, htime, hh, hcap⟩ :=
      (FrontierRiseBy_def R E rho i M _).mp hrise
    have hi := ((FrontierSearchStart_def R E rho O T Jst i ev M kind).mp hstart).1
    have hlow : u₀ ≤ nextEv.time :=
      ht ▸ frontierSearch_event_time_mono E rho schedule hi hj hij.le
    refine ⟨j, nextEv, by omega, hj, hlow, ?_, hh, ?_⟩
    · rwa [ht] at htime
    · intro k hk hkj
      exact hcap k (by omega) hkj
  refine ⟨?_, ?_⟩
  · intro hhor
    obtain ⟨j, ev, hjcut, hj, _, ht, hh, hcap⟩ := rise hhor
    exact ⟨j, ev, hjcut, hj, ht, hh, hcap⟩
  · intro hhor
    have rows :
        ∃ (j : Nat) (ev : V2.Event V Prot.Object), timeIdx rho u₀ ≤ j ∧
          rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
          M < frontierAtIdx R E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M) ∧
          FirstHeightRowBy S E rho T D.heightPair (M + 1)
            (ev.time + frontierSearchRowBudget T G ΔF ρbar) := by
      have hb := (frontierSearch_task_bounds_core T hT hG hbound hρ .gap).2.2.2.2.2
      have hRiseHor : u₀ + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon := by
        linarith only [hhor, hb]
      obtain ⟨j, ev, hjcut, hj, hlow, ht, hh, hcap⟩ := rise hRiseHor
      have hP := frontierSearch_period_bound_core T hT
      have hd := hT.delta_pos
      have hrowHor : ev.time + frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon := by
        linarith only [ht, hhor]
      refine ⟨j, ev, hjcut, hj, ht, hh, hcap, ?_⟩
      by_cases heq : frontierAtIdx R E rho (j + 1) = M + 1
      · obtain ⟨kind, hkind⟩ := frontierSearch_phase_exists R O E rho (j + 1) (M + 1)
        have heff : EffectiveEvent R E rho O j := Or.inl ((hcap j hjcut le_rfl).trans_lt hh)
        have hstart : FrontierSearchStart R E rho O T Jst j ev (M + 1) kind :=
          (FrontierSearchStart_def R E rho O T Jst j ev (M + 1) kind).mpr
            ⟨hj, by linarith, Or.inl heff, heq, by omega, hkind⟩
        exact frontierSearch_row_task_holder (R := R) (S := S) (O := O) (T := T) (E := E)
          (rho := rho)
          (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
          (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
          (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
          (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots) (obs := obs) (cert := cert)
          (inv := inv) (justif := justif) (keep := keep) (positive := positive)
          (coreLaws := coreLaws) (erasePreceq := erasePreceq) (joined := joined)
          (receipt := receipt) (chainRows := chainRows) hT hk crossing schedule mono awake
          joinedTick readyCut
          hServices receiptHeld faultWeight deltaF hdelta gap hJst hG slotProposal read
          order signer sourceParent hδ hbound rowsReceipt progressCoverage hfold
          honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect floor gateCopy
          service common heldSlot proposalSlot justifiedSource parentFrame hall cap
          hstart
          (hdelay.trans hlow) hrowHor
      · obtain ⟨x', hx', hmax⟩ := Finset.lt_sup_iff.mp
          (show M + 1 < frontierAtIdx R E rho (j + 1) by omega)
        obtain ⟨W', hW', hWh'⟩ := healing_phase_frontier_witness (R := R) (E := E)
          (rho := rho) (O := O) (Ef := Ef) (cert := cert) (inv := inv) (j + 1) x'
        obtain ⟨l, z, r, a, e, hlj, ha, hn, _⟩ := cap M (j + 1) x' W' ⟨hx', hW'⟩
          (by simp only [Height] at *; omega)
        have hcut : l < timeIdx rho ev.time :=
          (Nat.le_of_lt_succ hlj).trans_lt
            ((V2.D.Engine.index_lt_read_length_iff schedule ev.time hj).mpr le_rfl)
        have htime : T.action r ≤ ev.time :=
          frontierSearch_event_time_le E rho schedule ha.2.1 hcut
        exact frontierSearch_first_row S E rho T D.heightPair hT ⟨l, z, a, e, ha, hn⟩
          (by linarith only [htime, hb])
    obtain ⟨j, ev, hjcut, hj, ht, hh, hcap, hrow⟩ := rows
    obtain ⟨r, hr, hfirst', htime⟩ :=
      (FirstHeightRowBy_def S E rho T D.heightPair (M + 1) _).mp hrow
    exact ⟨r, hr, hfirst', j, ev, hjcut, hj, ht, hh, hcap, htime⟩

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- Blueprint 21:1722–1800; S5 F3, full FrontierSearchStatement (conditional form).
DC: SAME one first row is selected before both allowances. This theorem is derived from
`frontierSearch_family_holder` and `transfer`. `transfer` carries EVERY allowance admitted at the
cut to every actual later start. It has a producer only for start-independent (canonical)
allowances; a protocol with canonical budgets uses `frontierSearch_family_holder` directly. -/
theorem frontierSearch_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
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
  have fam := fun ρbar => (FrontierSearchFamilyStatement_def R S E rho O T I D.heightPair Jst
    leaseSlots deltaT G ΔF ρbar).mp (frontierSearch_family_holder (R := R) (S := S) (O := O)
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
      floor gateCopy service common heldSlot proposalSlot justifiedSource parentFrame eraseParent
      capReceipt cap hne ρbar)
  apply (FrontierSearchStatement_def R S E rho O T I D.heightPair Jst leaseSlots deltaT G
    ΔF).mpr
  intro hδ hbound rG u₀ M hgst hfirst hu₀ hdelay hM hrowCap
  have key := fun ρbar (hal : FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u₀) =>
    fam ρbar hδ hbound hal.1 (transfer rG ρbar hgst hfirst (hu₀ ▸ hal)) rG u₀ M hgst hfirst
      hu₀ hdelay hM hrowCap
  refine ⟨fun ρbar hal hhor => (key ρbar hal).1 hhor, ?_⟩
  rintro ⟨ρ0, hal0, hhor0⟩
  obtain ⟨rStar, hrStar, hfirstStar, _⟩ := (key ρ0 hal0).2 hhor0
  refine ⟨rStar, hrStar, hfirstStar, fun ρbar hal hhor => ?_⟩
  obtain ⟨r, hr, hfirst', j, ev, hjcut, hj, ht, hh, hcap, htime⟩ := (key ρbar hal).2 hhor
  have heq : rStar = r := frontierSearch_first_row_unique S E rho T D.heightPair
    hrStar hfirstStar hr hfirst'
  exact ⟨j, ev, hjcut, hj, ht, hh, hcap, heq.symm ▸ htime⟩

end AvailableChain.FGCompose
end
