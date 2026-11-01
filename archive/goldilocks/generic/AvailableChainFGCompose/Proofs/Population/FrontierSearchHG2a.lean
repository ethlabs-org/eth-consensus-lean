module
public import AvailableChainFGCompose.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGCompose.Proofs.Population.HolderBasePromotionAge
public import AvailableChainFGCompose.Proofs.Population.HolderBaseHG2a
public import AvailableChainFGCompose.Proofs.Population.Promotion
public import AvailableChainFGCompose.Proofs.Population.PromotionSource
public import AvailableChainFGCompose.Statements.Population.FrontierSearch

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
/-- ROOT-DIGEST W2b. Blueprint 21:1592–1640; S5 H2, route steps 1–8.
DC: SAME the saved seed supplies source transfer only through the proposal read,
here through its local service leaf. The strict cap supplies receipt through t_X+Δ
by the cap receipt leaf. A first rise before maturity is the left arm. -/
theorem frontier_hg2a_receipt_holder (hT : FGTimingLaws T)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    {Jst : Time} (hJst : E.t_GST ≤ Jst) (mono : FGRunOrderLaws E rho R)
    (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
    (eraseParent : ∀ X : FGBlock (Fin n), (R.erase X).parent = R.erase X.parent)
    (erasePreceq : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
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
    {u : Time} {i m r q : Nat} {Q : Block} {Qfg U : FGBlock (Fin n)}
    (hready : Jst ≤ u) (_hQ : HonestProposal E rho I q Q)
    (he : R.erase Qfg = Q) (hQm : (O.height Qfg).h = m)
    (hu : u ≤ T.proposal q) (hqr : q ≤ r * T.roundSlots) (hU : U = (O.height Qfg).T_h)
    (service : ∀ t, T.gate q ≤ t → t ≤ rho.horizon →
      (∀ k x, timeIdx rho u ≤ k → k ≤ timeIdx rho t → x ∈ rho.honest →
        (R.core (V2.D.Run.stateBefore E rho k x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m t)
    (entryAgreement : ∀ x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (hstart : frontierAtIdx R E rho (i + 1) ≤ m)
    (hhor : max (T.action r + Γ T G - T.delta + epsF T ΔF)
      (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta) ≤ rho.horizon) :
    FrontierHG2aResult R E rho O T I G ΔF i m r U := by
  have p0d5b_hg2a_action (T : FGTiming) (hT : FGTimingLaws T) (r : Nat) :
      T.action r = (r : Time) * FGCompose.P T + 6 * T.delta := by
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    unfold FGCompose.P
    push_cast
    ring
  have p0d5b_hg2a_kappa_two (T : FGTiming) (hT : FGTimingLaws T) (ΔF : Time) (hF : 0 ≤ ΔF) :
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
  have p0d5b_hg2a_idx_mono (rho : V2.D.Run V Prot) {d d' : Time} (hdd : d ≤ d') :
      V2.D.Run.idxBefore rho d ≤ V2.D.Run.idxBefore rho d' := by
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def, ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      (lt_of_lt_of_le (of_decide_eq_true he) hdd))
  have hGST : E.t_GST ≤ u := hJst.trans hready
  classical
  obtain ⟨A, hAh, hAq⟩ := honestQuorum
  have hA : A ⊆ FGHonestSeats S rho := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hAh i hi⟩
  have hne : A.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    change Ef.q ≤ ∑ i ∈ A, Ef.weight i at hAq
    rw [he, Finset.sum_empty] at hAq
    omega
  obtain ⟨seat, hseat⟩ := hne
  let Dl := max (T.action r + Γ T G - T.delta + epsF T ΔF)
    (T.proposal U.slot + 2 * FGCompose.P T + Γ T G - 3 * T.delta)
  rcases frontierSearch_strict_cap_or_rise R E rho schedule mono i m Dl hstart
      with hrise | hcap
  · exact Or.inl hrise
  · right
    have hqT : T.proposal q ≤ (r : Time) * FGCompose.P T := by
      have hc : (q : Time) ≤ (r : Time) * T.roundSlots := by exact_mod_cast hqr
      rw [hT.proposal_eq]
      change _ ≤ (r : Time) * (4 * (T.roundSlots : Time) * T.delta)
      nlinarith [hT.delta_pos]
    have hsync : E.t_GST ≤ (r : Time) * FGCompose.P T := hGST.trans (hu.trans hqT)
    obtain ⟨_, s, hlo, hhi, hslot, hterminal, _⟩ :=
      frontierSearch_hg2a_gap_core T E rho I hT deltaF hdelta gap r U hsync hhor
    have htD : T.proposal s < Dl := by linarith [hT.delta_pos]
    have hshor : T.proposal s ≤ rho.horizon := htD.le.trans hhor
    obtain ⟨hc, hage⟩ := promotion_age_grid_core T hT r s U ΔF hlo
    have hF : 0 ≤ ΔF := by
      rw [hdelta] at deltaF
      linarith [hT.delta_pos]
    have hk := p0d5b_hg2a_kappa_two T hT ΔF hF
    have hb8 : 8 * T.delta ≤ betaF T ΔF := by
      change 8 * T.delta ≤ 4 * (kappaF T ΔF : Time) * T.delta
      nlinarith [hT.delta_pos]
    have hat : T.action r ≤ T.proposal s := by
      have hc' := hc
      change (r : Time) * FGCompose.P T + betaF T ΔF ≤ T.proposal s at hc'
      rw [p0d5b_hg2a_action T hT]
      linarith [hT.delta_pos]
    have hqgate : T.gate q ≤ T.proposal s := by
      rw [hT.gate_eq]
      rw [p0d5b_hg2a_action T hT] at hat
      linarith only [hqT, hat]
    have hstartAction : E.t_GST ≤ T.action r := by
      rw [p0d5b_hg2a_action T hT]
      linarith [hT.delta_pos]
    have hgsts : E.t_GST + 4 * T.delta ≤ T.proposal s := by
      have hc' := hc
      change (r : Time) * FGCompose.P T + betaF T ΔF ≤ T.proposal s at hc'
      linarith
    obtain ⟨X, hnew, hXslot⟩ := slotProposal s hslot hgsts hshor
    have hf := service (T.proposal s) hqgate hshor (fun k x _ hkt hx => hcap k x
      (hkt.trans (frontierSearch_timeIdx_le_idxBefore rho htD)) hx)
    obtain ⟨hcovered, hentry, hentryEq, _⟩ := hf.2.2.2.2 r hqr hat
    obtain ⟨U0, hU0, _, hrows⟩ := healing_promotion_bounded_rows_holder R S E rho O.height T
      D.heightPair Ef laws hA ⟨seat, hseat⟩ hentry (fun i hi => hcovered i (hA hi))
      entryAgreement sourceSlot ancestorSlot
    have hU0U : U0 = U := by
      obtain ⟨K, _, _, _, _, _, hK, _, _, _, _, _, hKU0, _⟩ := hrows seat hseat
      exact hKU0.symm.trans ((hentryEq _ K (hAh seat hseat) hK).trans hU.symm)
    subst U0
    have hqs : q + 2 ≤ s := by
      obtain ⟨_, _, _, _, _, hafter⟩ :=
        healing_promotion_row_deadline T hT E hF hbound (rSent := r) le_rfl hstartAction hc
      omega
    have hQX : FGBlock.Preceq Qfg X.parent := by
      have hb := hf.2.1 s (R.erase X) hqs le_rfl hnew
      rw [← he, eraseParent] at hb
      exact erasePreceq _ _ hb
    have hUP : FGBlock.Preceq U X.parent := by
      rw [hU]
      exact KitFG.preceq_trans (laws.entry_preceq Qfg) hQX
    have src : PromotionSourceAtFG R S E rho O T I D A ΔF r m U s X := by
      refine ⟨hU0, hUP, hnew, hXslot, hstartAction, hc, hage, hshor, ?_⟩
      intro x hx
      obtain ⟨_, _, j, rSent, a, _, _, _, _, _, _, _, _, hr, ha, hn⟩ := hrows x hx
      exact ⟨j, rSent, a, hr, ha, hn⟩
    have hh := promotion_age_advance_of_source_holder R S O T E rho I D Ef decodeProposal bodyErase
      bodyRows blockWireRows parentFG parentHeight validFor fold laws hA hT schedule faultWeight
      deltaF hdelta src hδ hbound rowsReceipt progressCoverage hfold hAq read order
      signer
    obtain ⟨y, hy, hheld⟩ := capReceipt m s Qfg X hnew (by linarith [hT.delta_pos]) hQX
      (fun k x hk hx => hcap k x (hk.trans (p0d5b_hg2a_idx_mono rho hterminal)) hx)
      hQm (hterminal.trans hhor)
    have heldMono {d d' : Time} (hdd : d ≤ d')
        (hheld : Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ (R.core nd).fg.TF) d y) :
        Gen.V2.Duty.HoldsBefore E rho (fun nd => X ∈ (R.core nd).fg.TF) d' y := by
      rw [Gen.V2.Duty.HoldsBefore_def,
        ← Gen.V2.Duty.stateBefore_idxBefore E rho d schedule] at hheld
      rw [Gen.V2.Duty.HoldsBefore_def,
        ← Gen.V2.Duty.stateBefore_idxBefore E rho d' schedule]
      exact keep _ _ (p0d5b_hg2a_idx_mono rho hdd) y hheld
    exact ⟨s, X, hnew, hXslot, hh, y, hy, heldMono hterminal hheld⟩

end AvailableChain.FGCompose
end
