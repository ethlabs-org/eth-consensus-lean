module
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchHG2a
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchTail

public section

/-! Blueprint 21 HG.4:1695–1720; S5 F2. The saved entry and first opening give the
frozen rise guard through the generic capped HG.2a_F consumer. The continuing local
service, the held copy and the stored-slot reads of the saved seed are leaves. -/

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

include cert inv keep in
/-- ROOT-DIGEST W2b. Blueprint 21:1695–1720; S5 F2, saved-seed rise tail.
DC: SAME use capped HG.2a_F with the actual saved entry and first opening.
No phase after the saved gate or horizon beyond the frozen rise guard is assumed.
The seed fields are explicit; its continuing local service is a leaf of this seed. -/
theorem healing_frontierTail_rise_of_seed_holder (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (mono : FGRunOrderLaws E rho R)
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
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
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (heldSlot : ∀ i x A K, K ∈ (R.core (rho.stateBefore E i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot)
    (proposalSlot : ∀ q Q K, HonestProposal E rho I q Q → R.erase K = Q → K.slot = q)
    {u t : Time} {i m q : Nat} {Q : Block} {Qfg : FGBlock (Fin n)}
    (hready : Jst ≤ u) (hQ : HonestProposal E rho I q Q) (he : R.erase Qfg = Q)
    (hQm : (O.height Qfg).h = m) (hu : u ≤ T.proposal q) (hqt : T.gate q ≤ t)
    (hcopy : ∃ j x, Qfg ∈ (R.core (rho.stateBefore E j x)).fg.TF)
    (hservice : ∀ v, T.gate q ≤ v → v ≤ rho.horizon →
      (∀ k x, timeIdx rho u ≤ k → k ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E k x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m v)
    (hstart : frontierAtIdx R E rho (i + 1) ≤ m)
    (hhor : t + (2 * FGCompose.P T + Γ T G - 9 * T.delta) ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (t + (2 * FGCompose.P T + Γ T G - 9 * T.delta)) := by
  classical
  have p0d5c_rise_first_time (T : FGTiming) (hT : FGTimingLaws T) {q r : Nat}
      (hqr : q ≤ r * T.roundSlots) (hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r') :
      T.action r ≤ T.gate q + FGCompose.P T - 4 * T.delta := by
    have hd := hT.delta_pos
    rw [hT.action_eq, hT.gate_eq, hT.gate_eq, hT.proposal_eq, hT.proposal_eq]
    have hup : r * T.roundSlots + 1 ≤ q + T.roundSlots := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        have := hT.rounds
        omega
      · have hlt : ¬ q ≤ (r - 1) * T.roundSlots := fun h => by
          have := hfirst (r - 1) h
          omega
        have he : (r - 1) * T.roundSlots + T.roundSlots = r * T.roundSlots := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr]
        omega
    have hupI : ((r * T.roundSlots : Nat) : Time) + 1 ≤ (q : Time) + T.roundSlots := by
      exact_mod_cast hup
    unfold FGCompose.P
    nlinarith
  have hd := hT.delta_pos
  have hex : ∃ r, q ≤ r * T.roundSlots := ⟨q, by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q
      (show 1 ≤ T.roundSlots from (by decide : 1 ≤ 2).trans hT.rounds)⟩
  let r := Nat.find hex
  have hqr : q ≤ r * T.roundSlots := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  have har := p0d5c_rise_first_time T hT hqr hfirst
  have ha : T.action r ≤ t + FGCompose.P T - 4 * T.delta := by linarith
  let U := (O.height Qfg).T_h
  obtain ⟨j, x, hmem⟩ := hcopy
  have hUslot : U.slot ≤ q := (heldSlot j x U Qfg hmem (cert.height.entry_preceq Qfg)).trans_eq
    (proposalSlot q Q Qfg hQ he)
  have hUage : T.proposal U.slot ≤ t - 6 * T.delta := by
    have hc : (U.slot : Time) ≤ q := by exact_mod_cast hUslot
    rw [hT.gate_eq, hT.proposal_eq] at hqt
    rw [hT.proposal_eq]
    nlinarith
  have hD := frontierSearch_hg2a_bound_core T hT G ΔF t (T.action r) (T.proposal U.slot) hbound
    ha hUage
  have hresult := frontier_hg2a_receipt_holder (R := R) (S := S) (O := O) (T := T) (E := E)
    (rho := rho) (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
    (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
    (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
    (fold := fold) (laws := cert.height) hT schedule faultWeight deltaF hdelta gap hJst mono
    keep eraseParent eraseReflect slotProposal read order signer capReceipt hδ hbound
    rowsReceipt progressCoverage hfold honestQuorum hready hQ he hQm hu hqr rfl hservice
    (entryAgreement r) (sourceSlot r) (ancestorSlot r) hstart (hD.trans hhor)
  rcases (FrontierHG2aResult_def R E rho O T I G ΔF i m r U).mp hresult with
      hrise | ⟨s, X, _, _, hh, y, hy, hheld⟩
  · exact frontierSearch_rise_mono R E rho hD hrise
  · exact frontierSearch_rise_of_receipt R E rho O inv keep schedule mono hstart hy hh hheld hD


include cert inv keep in
/-- ROOT-DIGEST W2b. Blueprint 21:1695–1720; S5 F2, HG.4 rise.
DC: SAME use capped HG.2a_F with the actual saved entry and first opening.
The served seed's held copy and continuing service come from the seed-qualified leaves. -/
theorem healing_frontierTail_rise_holder (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (mono : FGRunOrderLaws E rho R)
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
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
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (heldSlot : ∀ i x A K, K ∈ (R.core (rho.stateBefore E i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot)
    (proposalSlot : ∀ q Q K, HonestProposal E rho I q Q → R.erase K = Q → K.slot = q)
    (eraseInj : Function.Injective R.erase)
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
    {i m : Nat} {ev : V2.Event V Prot.Object} {kind : PhaseKind}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m kind)
    (hserved : StrongServedFG R S E rho O T I D.heightPair Jst leaseSlots m ev.time)
    (hhor : ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta) ≤ rho.horizon) :
    FrontierRiseBy R E rho i m (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta)) := by
  have hf := ((FrontierSearchStart_def R E rho O T Jst i ev m kind).mp hstart).2.2.2.1
  obtain ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hQm, hs, hseed, hu, hp, hqt, _, _,
    _⟩ := hserved
  obtain ⟨j, x, Y, _, _, _, hYmem, hYe⟩ := gateCopy u (T.gate q) m J contested q Q hready hp
    hseed le_rfl hQ
  have hYQ : Y = Qfg := by
    have := hYe.trans he.symm
    exact eraseInj this
  subst Y
  exact healing_frontierTail_rise_of_seed_holder R S O T E rho I D Ef decodeProposal bodyErase
    bodyRows blockWireRows parentFG parentHeight validFor fold Jst cert inv keep hT schedule
    faultWeight deltaF hdelta gap hJst mono eraseParent eraseReflect slotProposal read order
    signer capReceipt hδ hbound rowsReceipt progressCoverage hfold honestQuorum entryAgreement
    sourceSlot ancestorSlot heldSlot proposalSlot hready hQ he hQm hu hqt ⟨j, x, hYmem⟩
    (fun v hv hvh hcap => service u v m J contested q Q Qfg hready hQ he hQm hs hseed hu hp hv
      hvh hcap) hf.le hhor

include cert inv keep in
/-- ROOT-DIGEST W2b. Blueprint 21:1695–1720; S5 F2, full HG.4.
DC: SAME combine the capped rise and the exact-height row under their separate guards.
There is no second repair allowance and no fixed F interval. -/
theorem healing_frontierTail_holder (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (cap : RCap R S E rho O T (fun a => namedEntry (D.heightPair a)) chainRows)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (mono : FGRunOrderLaws E rho R)
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
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
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (heldSlot : ∀ i x A K, K ∈ (R.core (rho.stateBefore E i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot)
    (proposalSlot : ∀ q Q K, HonestProposal E rho I q Q → R.erase K = Q → K.slot = q)
    (eraseInj : Function.Injective R.erase)
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
    : FrontierTailStatementFG R S E rho O T I D.heightPair Jst leaseSlots deltaT G ΔF := by
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
  intro _ _ i ev m kind hstart hserved
  refine ⟨fun hhor => healing_frontierTail_rise_holder R S O T E rho I D Ef decodeProposal bodyErase
    bodyRows blockWireRows parentFG parentHeight validFor fold Jst leaseSlots cert inv keep hT
    schedule faultWeight deltaF hdelta gap hJst mono eraseParent eraseReflect slotProposal read
    order signer capReceipt hδ hbound rowsReceipt progressCoverage hfold honestQuorum
    entryAgreement sourceSlot ancestorSlot heldSlot proposalSlot eraseInj gateCopy service hstart
    hserved hhor, fun hhor => ?_⟩
  obtain ⟨u, J, contested, q, Q, Qfg, hready, hQ, he, hQm, hs, hseed, hu, hp, hqt, _, _,
    _⟩ := hserved
  exact healing_frontierTail_row_holder R S E rho O T I D.heightPair chainRows Ef cert inv hT
    schedule honestSeats mono cap hp hQ hqt
    (fun v hv hvh hcap => service u v m J contested q Q Qfg hready hQ he hQm hs hseed hu hp hv
      hvh hcap) hhor

end AvailableChain.FGCompose
end
