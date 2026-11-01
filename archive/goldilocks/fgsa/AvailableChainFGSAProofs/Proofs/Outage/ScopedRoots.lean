module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedPrefix

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The general arming certificate supplies the actual pending batch at every
joined enabled receiver, including receivers outside G. -/
theorem outage_pending_gate_cert_receipt [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1)) : GateReceiptScope E rho i x (l + 1) := by
  have hs := h.base.valid.toScheduleWellFormed
  have hJ := outage_enabled_gate_joined h.base.valid hx hG
  have heg : SA.earlyTime p.toParams (l + 1) ≤ SA.gateTime p.toParams (l + 1) := by
    rw [arming_early_eq, arming_gate_eq]
    linarith [p.deltaPos]
  have hecut : SA.earlyTime p.toParams (l + 1) ≤ b₀ :=
    (arming_early_next p l).trans_le hc.gate_le_cut
  have hDelivery : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o)
      (fun t => t + p.Δ) b₀ := by
    simpa only [h.base.delta] using Gen.V2.Duty.deliveryWithinOn_of_healthyPrefixBy
      E rho b₀ h.healthy (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  have hPub : V2.PublicTime E (SA.voteTime p.toParams (l + 1)) := by
    refine ⟨4 * (l + 1) + 1, ?_⟩
    rw [h.base.delta, arming_vote_nat]
  have hBatch := outage_prefix_batch_service h.base hDelivery hx hJ le_rfl heg
    (hecut.trans h.cut.2) hecut le_rfl hPub (arming_vote_add p (l + 1))
  refine ⟨hG, hJ, outage_enabled_gate_read_epoch hs hG ?_, ?_⟩
  · change 4 * p.Δ * ((l + 1 : Nat) : Int) <
      4 * p.Δ * ((l + 1 : Nat) : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  · intro q K hy hTarget
    obtain ⟨k, hk, hem⟩ : V2.D.Run.emits E rho
        (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩)
        (SA.voteTime p.toParams (l + 1)) := by
      obtain ⟨k, _, _, hk, hem, _, _⟩ := hTarget
      exact ⟨k, hk, hem⟩
    obtain ⟨K', hTarget', hbad | hService⟩ := hBatch.heads _ _ q K.root hy
      ⟨k, hk, hem⟩ (by rw [toWire_ofHead]; rfl)
    all_goals have heq : K = K' := headTargetAtEmission_unique E rho hs hTarget hTarget'
    · have hDK := hc.joined_heads _ hy
        (fgsa_joinedAt_of_emitted_head E rho h.base.valid hk hem) k hk
      change Block.Preceq D (headVote p (clock p (rho.stateBefore E k
        (rho.seatOf (.base (.head (l + 1))) q)).st (SA.voteTime p.toParams (l + 1)))
          (l + 1)) at hDK
      rw [← headTargetAtEmission_at_tick E rho hs hTarget hk rfl] at hDK
      have hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
          (SA.earlyTime p.toParams (l + 1)) x).st.fg.F) D := by
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
        exact hc.f_below _ x (fgsa_idxBefore_mono rho heg) hx
      exact (hbad (heq ▸ block_compatible_of_common (block_preceq_refl K)
        (block_preceq_trans hFloor hDK))).elim
    · simpa only [← heq] using hService

/-- The complete joined Clean batch makes every enabled pending result compatible.
The receiver can be in W; the prefix service has no covered-node premise. -/
theorem outage_pending_gate_cert_result [Fintype V] {fast : Bool} {T b₀ ΔF : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) {B : Block} {l : Slot}
    {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    {i : Nat} {x : V} {C : Block} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x (l + 1))
    (hC : gateResultAt p c E rho i = some (some C)) : Block.Compatible C B := by
  have hv0 : 0 ≤ SA.voteTime p.toParams (l + 1) := by
    rw [arming_vote_eq]
    have := p.deltaPos
    positivity
  have hvcut : SA.voteTime p.toParams (l + 1) < b₀ :=
    (arming_vote_lt_early p _).1.trans_le
      ((arming_early_next p l).trans_le hc.gate_le_cut)
  obtain ⟨H, hH, hbatch⟩ := inclusion_joined_head_seats E rho h.base.cstar (l + 1)
    ⟨h.joinedPartBefore _ hv0 hvcut⟩
  have hrest : ((GridCO.seats p.n (GridCO.lateVotes p.toParams.engine
      (actView (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams (l + 1))))
        (l + 1))).toFinset \ H).card ≤ (Gen.V2.Duty.faulty rho).card := by
    apply inclusion_joined_rest_bound E rho h.base.cstar h.base.valid (l + 1) H
      (fun k hh hj => (hH k).mpr ⟨hh, hj⟩)
    intro o ho k hk
    obtain ⟨hm, hl⟩ := List.mem_filter.mp (List.mem_filter.mp ho).1
    change o ∈ (clockPre p (storeAt p c E rho i x) _).base.votes at hm
    rw [(Internal.clockPre_vn _ _).1] at hm
    exact ⟨i, x, o, hm, beq_iff_eq.mp hl, hk⟩
  have hraw := inclusion_gate_raw_at_tick E rho h.base.valid.toScheduleWellFormed hG
  have hresult := Option.some.inj (hraw.symm.trans hC)
  exact outageV_gate_of_good_service E rho h.base i x (l + 1) B C hx
    H (outage_gate_scope_of_shared (outage_pending_gate_cert_receipt h hc hx hG) H)
    (Gen.V2.Duty.faulty rho).card hbatch.lt hrest
    (fun q hq => (hH q).mp hq)
    (fun q hq K hK => by
      have hKeep := hK
      obtain ⟨k, _, _, hk, hem, _, _⟩ := hK
      have hDK := hc.joined_heads _ ((hH q).mp hq).1
        (fgsa_joinedAt_of_emitted_head E rho h.base.valid hk hem) k hk
      change Block.Preceq D (headVote p (clock p (rho.stateBefore E k
        (rho.seatOf (.base (.head (l + 1))) q)).st (SA.voteTime p.toParams (l + 1)))
          (l + 1)) at hDK
      rw [← headTargetAtEmission_at_tick E rho h.base.valid.toScheduleWellFormed
        hKeep hk rfl] at hDK
      have hFD : Block.Preceq (F_at p c E rho i x) D := by
        change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) D
        rw [arming_tick_store_on h.base.valid.toScheduleWellFormed hG.1
          (outage_enabled_gate_tick_epoch h.base.valid.toScheduleWellFormed hG)]
        exact hc.f_below _ x le_rfl hx
      exact ⟨block_preceq_trans hc.max_read hDK, block_preceq_trans hFD hDK⟩) hresult

/-- An enabled pre-restoration gate after the pending label makes its actor
covered or a member of W. The selected vote can be s+1 when v(s) precedes b0. -/
theorem outage_enabled_old_gate_covered
    (hBase : Base₂ p c E rho) {fast : Bool} {b₀ b₁ : Time} {l s : Slot}
    (hOrder : b₀ ≤ b₁) (hCut : b₀ < SA.gateTime p.toParams (l + 1))
    (hls : l + 1 < s) (hsr : s ≤ restoredLabel p b₁)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho i x s)
    (hNW : x ∉ outageW p E rho fast b₀ (restoredLabel p b₁)) :
    x ∈ coveredNodes p E rho fast b₀ := by
  classical
  by_contra hn
  apply hNW
  refine Finset.mem_filter.mpr ⟨hx, hn, ?_⟩
  have hJ := outage_enabled_gate_joined hBase.valid hx hG
  by_cases hb : b₀ ≤ SA.voteTime p.toParams s
  · refine ⟨s, hb, hsr, ?_⟩
    apply outage_restored_reader_awake hJ
    · rw [arming_vote_eq]; have := p.deltaPos; positivity
    · change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
      linarith [p.deltaPos]
    · exact (fgsa_vote_lt_gate p s).le
  · refine ⟨s + 1, ?_, ?_, ?_⟩
    · apply hCut.le.trans
      rw [arming_gate_eq, arming_vote_eq]
      have hcast := Int.ofNat_lt.mpr hls
      push_cast at hcast ⊢; nlinarith [p.deltaPos]
    · have hsr' : s < restoredLabel p b₁ := by
        by_contra hh
        have he : s = restoredLabel p b₁ := Nat.le_antisymm hsr (Nat.le_of_not_gt hh)
        have hv := (outage_first_restored_label p b₁ s).mpr (he ▸ le_rfl)
        exact hb (hOrder.trans hv)
      exact Nat.succ_le_of_lt hsr'
    · apply outage_restored_reader_awake hJ
      · rw [arming_vote_eq]; have := p.deltaPos; positivity
      · change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
        push_cast; linarith [p.deltaPos]
      · rw [arming_vote_eq, arming_gate_eq]
        push_cast; linarith [p.deltaPos]

/-- At an actual scoped HEAD the old live rows are compatible. G uses its
stable invariant; other pre-End readers cannot have outage writes outside W.
Post-End readers use only the earlier enabled result history. -/
theorem outage_scoped_head_rows [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    {B : Block}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hReader : outageHeadReader p E rho fast b₀ b₁ x (SA.voteTime p.toParams s))
    (hCover : x ∈ coveredNodes p E rho fast b₀ → Block.Preceq B (S_at p c E rho i x))
    (hResults : ∀ j q C, j < i → restoredLabel p b₁ < q →
      enabledGateAt p c E rho j x q → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) :
    ∀ row ∈ (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).base.obligations,
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).base.now < row.2.2 →
      Block.Compatible row.1 B := by
  classical
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hx := hs.honest_only _ (List.mem_of_getElem? hi)
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hOff := arming_clock_offGate_fields p (storeAt p c E rho i x) _
    (fun q => arming_gate_ne_vote p q s)
  intro row hr hl
  by_cases hG : x ∈ coveredNodes p E rho fast b₀
  · have hBS : Block.Preceq B dst.base.stableRecord := by
      rw [show dst.base.stableRecord = (storeAt p c E rho i x).base.stableRecord
        from hOff.2.1]
      exact hCover hG
    exact block_compatible_of_common
      ((storeBundle_postClock E rho i x (SA.voteTime p.toParams s)).lease row hr hl) hBS
  · rcases hReader.2 with hG' | ⟨hNW, _⟩ | hEnd
    · exact (hG hG').elim
    · have hm := hOff.2.2.2.subset hr
      obtain ⟨j, hji, q, C, hQ, hC, hRC, _⟩ := outage_row_deadline_origin hs i x row hm
      apply block_compatible_of_preceq_compatible hRC
      rcases lt_trichotomy q (l + 1) with hql | rfl | hlq
      · have hql' : q ≤ l := by dsimp only [Slot] at *; omega
        have hTime := ((arming_gate_le_iff p q l).mpr hql').trans hc.gate_le_cut
        have hidx := (V2.D.Engine.index_lt_read_length_iff hs b₀ hQ.1).mpr hTime
        exact block_compatible_of_common
          (hc.max_le q C ⟨j, hidx, x, hQ.1, hQ.2, hC⟩ hql') hc.max_read
      · exact outage_pending_gate_cert_result h.sleepPre hc hx hQ hC
      · by_cases hqr : q ≤ restoredLabel p b₁
        · exact (hG (outage_enabled_old_gate_covered h.pre.base h.order.2.2.1
            hc.cut_lt_pending hlq hqr hx hQ hNW)).elim
        · exact hResults j q C hji (Nat.lt_of_not_ge hqr) hQ hC
    · exact outage_head_rows_after_handover hs hEnd hResults row hr


/-- The named frame and scoped live rows give the actual HEAD live root. -/
theorem outage_scoped_head_root [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) {B : Block} {β : FGBlock (Fin p.n)}
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hReader : outageHeadReader p E rho fast b₀ b₁ x (SA.voteTime p.toParams s))
    (hNames : OutageNamedHistory p c E rho β i)
    (hCover : x ∈ coveredNodes p E rho fast b₀ → Block.Preceq B (S_at p c E rho i x))
    (hResults : ∀ j q C, j < i → restoredLabel p b₁ < q →
      enabledGateAt p c E rho j x q → gateResultAt p c E rho j = some (some C) →
      Block.Compatible C B) :
    Block.Compatible (liveRoot p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s))) B := by
  classical
  have hs := h.pre.base.valid.toScheduleWellFormed
  have hx := hs.honest_only _ (List.mem_of_getElem? hi)
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hOff := arming_clock_offGate_fields p (storeAt p c E rho i x) _
    (fun q => arming_gate_ne_vote p q s)
  have hcFrame := fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat
    i x β hx hNames.history
  have hZ : Block.Compatible (eraseFG (controls p dst).Z) B := by
    rw [← hβ]
    have hCtrl : controls p dst = controls p (storeAt p c E rho i x) := by
      change KitFG.treeStoreControlsView (heightView p) dst.fg = _
      rw [show dst.fg = (storeAt p c E rho i x).fg from clock_fg p _ _]
      rfl
    rw [hCtrl]
    have hZF : FGBlock.Preceq (controls p (storeAt p c E rho i x)).Z β ∨
        FGBlock.Preceq β (controls p (storeAt p c E rho i x)).Z := by
      change FGBlock.Preceq (if (controls p _).rootIsJ then _ else _) β ∨
        FGBlock.Preceq β (if (controls p _).rootIsJ then _ else _)
      cases (controls p (storeAt p c E rho i x)).rootIsJ
      · exact hcFrame.2.1
      · exact hcFrame.2.2.1
    exact Bool.or_eq_true_iff.mpr (hZF.imp eraseFG_preceq eraseFG_preceq)
  apply outageV_liveRoot_compatible p dst B hZ
  exact outage_scoped_head_rows h hc hi hReader hCover hResults

/-- Both local frame inputs at the first regression are produced by its
causal prefix and prior good batch. Only the uncontested frozen path is separate. -/
theorem outage_first_regression_retained_frame [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)
    {k : Nat} {s : Slot}
    (hReg : OutageScopedRegression (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ b₁ B k s)
    (hFirst : ∀ j, j < k → ∀ q, ¬ OutageScopedRegression (p := p) (c := c) (E := E)
      (rho := rho) fast b₀ b₁ B j q) :
    ∃ q K, rho.events[k]? = some
      (.tick (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s)) ∧
      outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
        (SA.voteTime p.toParams s) ∧
      HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K ∧
      ¬ Block.Preceq B K ∧
      Block.Compatible (liveRoot p (clock p (storeAt p c E rho k
        (rho.seatOf (.base (.head s)) q)) (SA.voteTime p.toParams s))) B ∧
      RetainedTargetScores p (clock p (storeAt p c E rho k
        (rho.seatOf (.base (.head s)) q)) (SA.voteTime p.toParams s)) s B := by
  obtain ⟨q, K, hk, hR, hK, hBad, hScores, _⟩ := outage_first_regression_scores
    h hf htsrc hnamed hsrc hState hprov hne hc hβ hReg hFirst
  obtain ⟨hResults, _, hNames, _, hCover⟩ := outage_first_regression_prefix
    h hf htsrc hnamed hsrc hState hprov hne hc hβ hReg hFirst
  exact ⟨q, K, hk, hR, hK, hBad,
    outage_scoped_head_root h hf hc hβ hk hR hNames (hCover _)
      (fun j q C hj => hResults j _ q C hj hR.1.1), hScores⟩

end AvailableChain.FGSA.Run
end
