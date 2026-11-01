module
public import AvailableChainFGCompose.Proofs.Healing.PromotionAge
public import AvailableChainFGCompose.Proofs.Population.Promotion
public import AvailableChainFGCompose.Proofs.Population.PromotionSource

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
theorem frontierSearch_age_service_holder
    {A : Finset (Fin n)} (hA : A ⊆ FGHonestSeats S rho) (hne : A.Nonempty) (hT : FGTimingLaws T)
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
    (honestQuorum : Ef.q ≤ Ef.weightOf A)
    {u D' : Time} {m height r : Nat} {J : Option (FGBlock (Fin n))} {contested : Bool}
    {Q : Block} {U : FGBlock (Fin n)}
    (hentry : OpeningEntry R E rho O.height T r height)
    (hcovered : OpeningCoveredFG R S E rho O.height T D.heightPair A r Q)
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
  have p0d5b_search_action (T : FGTiming) (hT : FGTimingLaws T) (r : Nat) :
      T.action r = (r : Time) * FGCompose.P T + 6 * T.delta := by
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    unfold FGCompose.P
    push_cast
    ring
  have p0d5b_search_vote (T : FGTiming) (hT : FGTimingLaws T) (r : Nat) :
      T.vote (r * T.roundSlots) ≤ T.action r := by
    rw [hT.action_eq, hT.gate_eq, hT.vote_eq]
    linarith [hT.delta_pos]
  have p0d5b_search_kappa_two (T : FGTiming) (hT : FGTimingLaws T) (ΔF : Time) (hF : 0 ≤ ΔF) :
      (2 : Time) ≤ kappaF T ΔF := by
    have hd : 0 < 4 * T.delta := by linarith [hT.delta_pos]
    have hn : 0 ≤ 6 * T.delta + ΔF + 4 * T.delta - 1 := by
      have hd1 : (1 : Time) ≤ T.delta := hT.delta_pos
      linarith
    have hc : 6 * T.delta + ΔF ≤ (kappaF T ΔF : Time) * (4 * T.delta) := by
      delta kappaF
      rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
      have hhi := Int.lt_ediv_add_one_mul_self (6 * T.delta + ΔF + 4 * T.delta - 1) hd
      nlinarith
    have hnat : 2 ≤ kappaF T ΔF := by
      by_contra hk
      have hk' : (kappaF T ΔF : Time) ≤ 1 := by
        exact_mod_cast (show kappaF T ΔF ≤ 1 by omega)
      nlinarith [hT.delta_pos]
    exact_mod_cast hnat
  have p0d5b_search_phase_cut (R : FGCoreReads Prot n Base Proposal Wire)
      (O : FGObservationReads R) (E : Generic.Env V) (rho : V2.D.Run V Prot)
      {u v w : Time} {m : Nat}
      {J : Option (FGBlock (Fin n))} {contested : Bool}
      (hp : PhaseInterval R E rho O u v m J contested) (huw : u ≤ w) (hwv : w ≤ v) :
      PhaseInterval R E rho O u w m J contested := by
    refine ⟨huw, hwv.trans hp.2.1, hp.2.2.1, ?_⟩
    intro i x hui hiw hx
    apply hp.2.2.2 i x hui _ hx
    apply hiw.trans
    rw [timeIdx_def, timeIdx_def, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      ((of_decide_eq_true he).trans hwv))
  have hsync : E.t_GST ≤ u := hJst.trans hready
  obtain ⟨x₀, K₀, hx₀, hK₀, hK₀U⟩ := hsource
  obtain ⟨U', hU', _, hrows⟩ := healing_promotion_bounded_rows_holder R S E rho O.height T
    D.heightPair Ef laws hA hne hentry hcovered entryAgreement sourceSlot ancestorSlot
  obtain ⟨i₁, hi₁⟩ := hne
  let x₁ := safetyHolder S rho i₁
  have hx₁ : x₁ ∈ rho.honest := (Finset.mem_filter.mp (hA hi₁)).2
  have hUU : U' = U := by
    obtain ⟨K, _, _, _, _, _, hK, _, _, _, _, _, hKU, _⟩ := hrows i₁ hi₁
    obtain ⟨e, he⟩ := hentry
    have hroot := (he x₁ K hx₁ hK).2.trans (he x₀ K₀ hx₀ hK₀).2.symm
    exact hKU.symm.trans
      ((entryAgreement x₁ x₀ K K₀ hx₁ hx₀ hK hK₀ hroot).trans hK₀U)
  subst hUU
  have hF : 0 ≤ ΔF := by
    rw [hdelta] at deltaF
    linarith [hT.delta_pos]
  obtain ⟨_, s, hlo, _, hslot, _, hgate⟩ :=
    healing_promotion_age_gap T hT I E rho gap hF r U'.slot hstart hwin
  have hgateD : T.gate s ≤ D' := hgate.trans hbudget
  have hgs : T.gate s = T.proposal s + 6 * T.delta := hT.gate_eq s
  have hhor : T.proposal s ≤ rho.horizon := by linarith [hT.delta_pos, hp.2.1]
  obtain ⟨hc, hage⟩ := promotion_age_grid T hT r s U' ΔF hlo
  have hk := p0d5b_search_kappa_two T hT ΔF hF
  have hb8 : 8 * T.delta ≤ betaF T ΔF := by
    change 8 * T.delta ≤ 4 * (kappaF T ΔF : Time) * T.delta
    nlinarith [hT.delta_pos]
  have hcarrier : T.action r < carrierTimeW T ΔF r := by
    rw [p0d5b_search_action T hT]
    change _ < (r : Time) * FGCompose.P T + betaF T ΔF
    linarith [hT.delta_pos]
  have hat : T.action r < T.proposal s := hcarrier.trans_le hc
  have hut : u ≤ T.proposal s := hu.trans ((p0d5b_search_vote T hT r).trans hat.le)
  have hpT := p0d5b_search_phase_cut R O E rho hp hut (by linarith [hT.delta_pos])
  have hstartAction : E.t_GST ≤ T.action r := by
    rw [p0d5b_search_action T hT]
    linarith [hT.delta_pos]
  have hgsts : E.t_GST + 4 * T.delta ≤ T.proposal s := by
    have hc' := hc
    change (r : Time) * FGCompose.P T + betaF T ΔF ≤ T.proposal s at hc'
    linarith
  obtain ⟨X, hnew, hXslot⟩ := slotProposal s hslot hgsts hhor
  obtain ⟨_, _, _, _, _, hafter⟩ :=
    healing_promotion_row_deadline T hT E hF hbound (rSent := r) le_rfl hstartAction hc
  obtain ⟨K, _, _, _, _, _, hK, _, _, hUK, _⟩ := hrows i₁ hi₁
  have hKX := sourceParent u m J contested r s X x₁ K hready hpT hu hat.le hafter hnew hx₁ hK
  have src : PromotionSourceAtFG R S E rho O T I D A ΔF r height U' s X := by
    refine ⟨hU', KitFG.preceq_trans hUK hKX, hnew, hXslot, hstartAction, hc, hage, hhor, ?_⟩
    intro x hx
    obtain ⟨_, _, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, hn⟩ := hrows x hx
    exact ⟨j, rSent, a, hr, ha, hn⟩
  have hh := promotion_age_advance_of_source_holder R S O T E rho I D Ef decodeProposal bodyErase
    bodyRows blockWireRows parentFG parentHeight validFor fold laws hA hT schedule faultWeight
    deltaF hdelta src hδ hbound rowsReceipt progressCoverage hfold honestQuorum read order
    signer
  exact ⟨s, X, hnew, hXslot, hat, hgateD, hh⟩

end AvailableChain.FGCompose
end
