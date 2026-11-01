module
public import AvailableChainFGSAProofs.Proofs.Outage.RestoredReceipt

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- An authentic fresh HEAD is not excluded at its early deadline. The result
uses the sender's actual emission, not a protected-receiver certificate. -/
theorem outage_fresh_head_not_excluded
    (hV : V2.D.ExecutionValid E rho) {x y : V} {s : Slot} {q : Fin p.n} {b : BlockId}
    (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s)) :
    (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
  have hS := hV.toScheduleWellFormed
  obtain ⟨k, hk, hem⟩ := he
  have he' := hem
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at he'
  have hseat := ((fgsa_emits_head E rho _ y _ s q b).mp he').2.2.1
  have hh : rho.seatOf (.base (.head s)) q ∈ rho.honest := hseat ▸ hy
  have h0 : 0 ≤ SA.earlyTime p.toParams s := by
    rw [arming_early_eq]
    have := p.deltaPos
    positivity
  have hnow : (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.base.now ≤
      SA.earlyTime p.toParams s := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    have hSource := V2.D.Engine.stateBefore_now_source_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho (rho.idxBefore (SA.earlyTime p.toParams s)) x
    have hClock := fgsa_clock_now p c (rho.stateBefore E
      (rho.idxBefore (SA.earlyTime p.toParams s)) x)
    simp only [hClock] at hSource
    rcases hSource with hz | ⟨j, hj, hevent | hevent⟩
    · rw [hz]; exact h0
    · exact ((Gen.V2.Duty.index_lt_idxBefore_iff hS hevent _).mp hj).le
    · exact ((Gen.V2.Duty.index_lt_idxBefore_iff hS hevent _).mp hj).le
  have hwindow : (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.slot p ≤ s + 1 := by
    have hslot : p.slotOf (SA.earlyTime p.toParams s) = s :=
      slotOf_offset p s (2 * p.Δ) (by have := p.deltaPos; positivity)
        (by have := p.deltaPos; dsimp [Time] at *; omega)
    exact ((Internal.slotOf_mono (p := p) hnow).trans_eq hslot).trans (Nat.le_succ s)
  cases hNX : (fgsa p c).excludes
      (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) with
  | false => rfl
  | true =>
    obtain ⟨u, hu, v, hv, hne, hlu, hlv, hqu, hqv, _, _⟩ :=
      fgsa_head_excluded_before E rho hS x (SA.earlyTime p.toParams s) s q b hwindow hNX
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hu hv
    have hEmit : V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
        (ofHead p ⟨.seat (.head s) q, b⟩) (SA.voteTime p.toParams s) :=
      hseat.symm ▸ ⟨k, hk, hem⟩
    have hU := fgsa_honest_head_eq_of_stored E rho hV _ x s q b _ hh hEmit u hu hlu hqu
    have hW := fgsa_honest_head_eq_of_stored E rho hV _ x s q b _ hh hEmit v hv hlv hqv
    exact (hne (hU.trans hW.symm)).elim

/-- A joined reader supplies the exact batch epoch and HEAD transport.
The source is fresh; the receiver can have restarted before this label. -/
theorem outage_joined_head_service {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {x y : V} {s : Slot} {C R : Time} {q : Fin p.n} {b : BlockId}
    (_hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hC : SA.earlyTime p.toParams s ≤ C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (he : V2.D.Run.emits E rho y (ofHead p ⟨.seat (.head s) q, b⟩)
      (SA.voteTime p.toParams s)) :
    Nonempty (FreshHeadService E rho s q b C x) := by
  have hd := p.deltaPos
  have hv0 : 0 ≤ SA.voteTime p.toParams s := by rw [arming_vote_eq]; positivity
  have hstart : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith
  have hve := (arming_vote_lt_early p s).1
  have hRF := outage_restored_reader_epoch hBase.valid.toScheduleWellFormed hJ
    hstart (hve.trans_le (hC.trans hCR))
  have hdl : max (SA.voteTime p.toParams s) E.t_GST + p.Δ =
      SA.earlyTime p.toParams s := by rw [max_eq_left hGST, arming_vote_add]
  refine ⟨{
    dl := fun a => max a E.t_GST + p.Δ
    cut := rho.horizon
    within := ?_
    ready := ?_
    later := by simpa only [hdl] using hve
    cut_le := by simpa only [hdl] using hC.trans hhor
    horizon := by simpa only [hdl] using hC.trans hhor
    freeze_le := by simpa only [hdl] using hC
    epoch := hRF.mono le_rfl (fgsa_idxBefore_mono rho hCR)
    handlers := by simpa only [hdl] using arming_head_handlers hBase.valid hBase.delta s q b x
    not_excluded := by simpa only [hdl] using outage_fresh_head_not_excluded hBase.valid hy he }⟩
  · simpa only [hBase.delta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy
      E rho hSync (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  · rw [hdl]
    refine ⟨y, hy, Or.inl he, ?_⟩
    intro u hvu hue
    exact outage_restored_reader_awake hJ (hv0.trans hvu) (hstart.trans hvu)
      (hue.le.trans (hC.trans hCR))

private theorem outage_proposal_direct (st : State p.n) (parent o : Obj p)
    {s : Slot} {N : NamedProposal p.n} (hd : (toWire p o).decode = some (.block s N))
    (hh : handlesS p st parent o) : parent = o := by
  rcases hh with h | h
  · exact h
  · cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r M =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofHead] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd
        · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
          rw [toWire_ofRow] at hd
          rcases q with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [Wire.decode] at hd

/-- Original proposal emission or acceptance drives service at a public anchor.
Durable proposal history supplies HistorySafeAt after an earlier restart. -/
theorem outage_joined_proposal_service {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {x y : V} {s q : Slot} {N : NamedProposal p.n} {send a C R : Time}
    (_hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hStart : slotStartZ p (s : Int) ≤ a) (hPub : V2.PublicTime E a)
    (hDeadline : a + p.Δ = C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hGST : E.t_GST ≤ a) (ht : send ≤ a)
    (he : V2.D.Run.emits E rho y (ofWire p ⟨.proposer q, .proposal N⟩) send ∨
      ∃ k, V2.D.Run.acceptsAt E rho k y (ofWire p ⟨.proposer q, .proposal N⟩) send)
    (hNX : (fgsa p c).excludes (rho.stateBeforeTime E C x)
      (ofWire p ⟨.proposer q, .proposal N⟩) = false) :
    Nonempty (ReceiverService E rho (ofWire p ⟨.proposer q, .proposal N⟩) send C x) := by
  have hV := hBase.valid
  have ha0 : 0 ≤ a := le_trans (by
    change 0 ≤ 4 * p.Δ * (s : Int); have := p.deltaPos; positivity) hStart
  have haC : a < C := hDeadline ▸ lt_add_of_pos_right a p.deltaPos
  have hdl : max a E.t_GST + p.Δ = C := by rw [max_eq_left hGST, hDeadline]
  have hAct : fgsaAdmissionTime p (ofWire p ⟨.proposer q, .proposal N⟩) ≤ send := by
    rcases he with ⟨k, hk, hem⟩ | ⟨k, hacc⟩
    · rw [(V2.D.Run.step_tick_eq E rho hk).2] at hem
      exact ((fgsa_emits_proposal E rho _ y send q (.proposal N)).mp hem).2.1.le
    · have hbound := timely_of_relay_retained E rho (fgsaTimelyClock p c)
        (fgsaAdmitSound p c) hV.toScheduleWellFormed
        (by rw [fgsaTimelyClock_clock]; exact fgsaRestoreTimeLaw p c)
        (fun obj => (fgsaTimelyClock_actTime p c obj).symm ▸
          fgsa_admissionTime_public p E hBase.delta obj) y k _ send hacc
      rw [fgsaTimelyClock_actTime] at hbound
      exact hbound.trans (Gen.V2.Duty.pubFloor_le E send)
  have hRF := outage_restored_reader_epoch hV.toScheduleWellFormed hJ hStart
    (haC.trans_le hCR)
  refine ⟨{
    dl := fun a => max a E.t_GST + p.Δ
    cut := rho.horizon
    anchor := a
    within := ?_
    ready := ?_
    send_le := ht
    nonneg := ha0
    later := by simpa only [hdl] using haC
    cut_le := by simpa only [hdl] using hhor
    horizon := by simpa only [hdl] using hhor
    freeze_le := by rw [hdl]
    history := fgsa_historySafeAt_of_proposal x _ a rfl
    epoch := hRF.mono le_rfl (fgsa_idxBefore_mono rho hCR)
    handlers := ?_
    not_excluded := by simpa only [hdl] using hNX }⟩
  · simpa only [hBase.delta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy
      E rho hSync (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ ΔF)
  · rw [hdl]
    refine ⟨y, hy, he, ?_⟩
    intro u hau huC
    exact outage_restored_reader_awake hJ (ha0.trans hau) (hStart.trans hau)
      (huC.le.trans hCR)
  · intro j u hau hud hh
    obtain ⟨parent, hj, hp⟩ := hh
    have hEq := outage_proposal_direct _ parent _ rfl hp
    subst parent
    refine ⟨hV.wire j x _ u hj, hV.deps j x _ u hj, ?_⟩
    have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hV hj hPub ha0 hau
    change fgsaAdmissionTime p _ ≤ (rho.stateBefore E j x).st.base.now
    rw [← fgsa_clock_now p c (rho.stateBefore E j x)]
    exact (hAct.trans ht).trans hn

private theorem outage_target_decode {o : Obj p} {K : Block}
    (h : blockOf? p o = some K) :
    ∃ q N, o = ofWire p ⟨.proposer q, .proposal N⟩ ∧ N.erase = K := by
  unfold blockOf? at h
  cases hd : (toWire p o).decode with
  | none => simp only [hd, reduceCtorEq] at h
  | some m =>
    cases m <;> simp only [hd, reduceCtorEq, Option.some.injEq] at h
    rename_i q N
    refine ⟨q, N, ?_, h⟩
    apply toWire_injective
    rw [toWire_ofWire]
    exact decode_eq_block.mp hd

/-- A joined honest reader gets a full batch at the exact public deadline.
Incompatible targets keep the public finality alternative. Compatible targets
use their original acceptance and durable proposal history. -/
theorem outage_joined_batch_service {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {x : V} {s : Slot} {a C R : Time} (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) R)
    (hC : SA.earlyTime p.toParams s ≤ C) (hCR : C ≤ R) (hhor : C ≤ rho.horizon)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hva : SA.voteTime p.toParams s ≤ a) (hPub : V2.PublicTime E a)
    (hDeadline : a + p.Δ = C) : ArmingBatchReceiptService E rho x s C := by
  classical
  have hV := hBase.valid
  have hS := hV.toScheduleWellFormed
  have hStart : slotStartZ p (s : Int) ≤ a := le_trans (by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]) hva
  constructor
  · intro y o q b hy he hd
    have ho : o = ofHead p ⟨.seat (.head s) q, b⟩ := by
      apply toWire_injective
      rw [toWire_ofHead]
      exact decode_eq_vote.mp hd
    subst o
    obtain ⟨k, hk, hem⟩ := he
    have he' := hem
    rw [(V2.D.Run.step_tick_eq E rho hk).2] at he'
    have hf := (fgsa_emits_head E rho _ y _ s q b).mp he'
    let K := headVote p (FGSA.clock p (rho.stateBefore E k y).st
      (SA.voteTime p.toParams s)) s
    have hroot : K.root = b := hf.2.2.2.2.symm
    have hTarget : HeadTargetAtEmission p c E rho y
        (ofHead p ⟨.seat (.head s) q, b⟩) (SA.voteTime p.toParams s) K := by
      refine ⟨k, s, q, hk, hem, ?_, rfl⟩
      rw [hroot]
    refine ⟨K, hTarget, ?_⟩
    by_cases hbad : ¬ Block.Compatible K (eraseFG (rho.stateBeforeTime E C x).st.fg.F)
    · exact Or.inl hbad
    right
    refine ⟨outage_joined_head_service hBase hSync hx hy hJ hC hCR hhor hGST
      ⟨k, hk, hem⟩, ?_⟩
    by_cases hgen : K = .genesis
    · exact hgen ▸ fgsa_target_service_genesis E rho C x
    have hK : K ∈ (storeAt p c E rho k y).base.blocks := by
      have hm := headVote_stored p _
        (storeBundle_postClock E rho k y (SA.voteTime p.toParams s)).cstore s
      change K ∈ (clock p (storeAt p c E rho k y) _).base.blocks at hm
      rwa [clock_base_blocks] at hm
    obtain ⟨j, hjk, send, obj, hobj, hacc⟩ := fgsa_block_accepted_origin E rho k y K hgen hK
    obtain ⟨q', N, rfl, hNK⟩ := outage_target_decode hobj
    have hsend : send ≤ SA.voteTime p.toParams s := by
      obtain ⟨parent, hj, _⟩ := hacc.1
      by_contra hn
      have hkj := V2.D.Engine.tick_index_lt_delivery E rho hS hk hj (le_of_not_ge hn)
      omega
    have hT : Gen.V2.Duty.Trigger E rho (ofWire p ⟨.proposer q', .proposal N⟩) send :=
      Or.inr ⟨y, hy, j, hacc⟩
    have hNX : (fgsa p c).excludes (rho.stateBeforeTime E C x)
        (ofWire p ⟨.proposer q', .proposal N⟩) = false := by
      change (blockExcluded _ N.erase || invalidForParent p _ N) = false
      rw [fgsa_trigger_invalid_false E rho _ send q' N hT rfl]
      change (!activeCompatible _ N.erase || false) = false
      have hc : activeCompatible (rho.stateBeforeTime E C x).st N.erase = true := by
        change Block.compatible N.erase (eraseFG (rho.stateBeforeTime E C x).st.fg.F) = true
        rw [hNK]
        exact not_not.mp hbad
      rw [hc]
      rfl
    exact hNK ▸ fgsa_target_service_of_proposal E rho q' N send C x
      (outage_joined_proposal_service hBase hSync hx hy hJ hStart hPub hDeadline
        hCR hhor (hGST.trans hva) (hsend.trans hva) (Or.inr ⟨j, hacc⟩) hNX)
  · intro y o m q N hy he htime hNX hd
    have ho : o = ofWire p ⟨.proposer q, .proposal N⟩ := by
      apply toWire_injective
      rw [toWire_ofWire]
      exact decode_eq_block.mp hd
    subst o
    exact outage_joined_proposal_service hBase hSync hx hy hJ hStart hPub hDeadline
      hCR hhor (hGST.trans hva) (htime.trans hva) (Or.inl he) hNX

/-- The restored-label formula gives the inclusive vote cut used by every service. -/
theorem outage_restored_vote_cut (p : Params) (b₁ : Time) {q : Slot}
    (hq : restoredLabel p b₁ ≤ q) : b₁ ≤ SA.voteTime p.toParams q := by
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hc : max 0 (- ((p.Δ - b₁) / (4 * p.Δ))) ≤ (q : Int) := by
    have hh : ((restoredLabel p b₁ : Nat) : Int) ≤ (q : Int) := by exact_mod_cast hq
    change ((max 0 (- ((p.Δ - b₁) / (4 * p.Δ)))).toNat : Int) ≤ _ at hh
    rwa [Int.toNat_of_nonneg (le_max_left _ _)] at hh
  have hh : -(q : Int) ≤ (p.Δ - b₁) / (4 * p.Δ) := by
    have h := (le_max_right _ _).trans hc
    linarith
  have hm := (Int.le_ediv_iff_mul_le hd).mp hh
  rw [arming_vote_eq]
  nlinarith

/-- Full-run synchrony and the joined read guards derive all restored services.
No prefix receipt, target compatibility, or receiver-service premise is needed. -/
theorem outage_restored_services {ΔF : Time} {fast : Bool} {T b₀ b₁ : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hGST : E.t_GST ≤ b₁) :
    OutageRestoredServices (p := p) (c := c) (E := E) (rho := rho) fast T b₀ b₁ := by
  have hd := p.deltaPos
  constructor
  · intro x q hq hhor hx
    apply outage_joined_batch_service hBase hSync hx.1 hx.2 le_rfl
      (a := SA.voteTime p.toParams q)
    · change 4 * p.Δ * (q : Int) + 2 * p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
      linarith
    · exact hhor
    · exact hGST.trans (outage_restored_vote_cut p b₁ hq)
    · exact le_rfl
    · refine ⟨4 * q + 1, ?_⟩
      rw [hBase.delta, arming_vote_eq]
      push_cast
      ring
    · exact arming_vote_add p q
  · intro x s hs hq hhor hx
    obtain ⟨q, rfl⟩ : ∃ q, s = q + 1 := ⟨s - 1, by dsimp only [Slot] at *; omega⟩
    simp only [Nat.add_sub_cancel] at hq ⊢
    apply outage_joined_batch_service hBase hSync hx.1 hx.2
      (a := SA.earlyTime p.toParams q)
    · rw [arming_early_eq, arming_freeze_eq]
      linarith
    · rw [arming_freeze_eq, arming_vote_eq]
      push_cast
      linarith
    · exact le_trans (by
        rw [arming_freeze_eq, arming_vote_eq]
        push_cast
        linarith) hhor
    · exact hGST.trans (outage_restored_vote_cut p b₁ hq)
    · exact (arming_vote_lt_early p q).1.le
    · refine ⟨4 * q + 2, ?_⟩
      rw [hBase.delta, arming_early_eq]
      push_cast
      ring
    · rw [arming_early_eq, arming_freeze_eq]
      ring
  · intro m hm hq hhor x hx
    obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by dsimp only [Slot] at *; omega⟩
    simp only [Nat.add_sub_cancel] at hq ⊢
    change SA.proposalTime p.toParams (q + 1) ≤ rho.horizon at hhor
    change headReader p E rho x (q + 1) (SA.proposalTime p.toParams (q + 1)) at hx
    apply outage_joined_batch_service hBase hSync hx.1 hx.2
      (a := SA.freezeTime p.toParams q) (C := SA.proposalTime p.toParams (q + 1))
      (R := SA.proposalTime p.toParams (q + 1))
    · rw [arming_early_eq, arming_proposal_eq]
      push_cast
      linarith
    · exact le_rfl
    · exact hhor
    · exact hGST.trans (outage_restored_vote_cut p b₁ hq)
    · rw [arming_vote_eq, arming_freeze_eq]
      linarith
    · refine ⟨4 * q + 3, ?_⟩
      rw [hBase.delta, arming_freeze_eq]
      push_cast
      ring
    · rw [arming_freeze_eq, arming_proposal_eq]
      push_cast
      ring

/-- The restored clauses come entirely from the continuation regime. P-Ar owns
the separate prefix receipt at the healthy cut. -/
theorem outage_continuation_receipt_of_prefix [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hPrefix : OutagePrefixReceipt p c E rho fast T b₀) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ := by
  have hServices := outage_restored_services (fast := fast) (T := T) (b₀ := b₀)
    h.pre.base h.sync h.gst
  exact outage_restored_receipt_with_service h.pre.base.valid h.pre.base.receiptIdealization
    hPrefix hServices.early hServices.freeze hServices.proposal

/-- Both the prefix and restored receipt services come from the continuation regime. -/
theorem outage_continuation_receipt [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ := by
  exact outage_continuation_receipt_of_prefix h (arming_continuation_prefix_receipt h)

end AvailableChain.FGSA.Run
end
